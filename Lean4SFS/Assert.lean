/-
Lean 4 syntax categories for the `@Assert`/`@Invariant` formula language used throughout
this repository (`f="<<Name : params : body>>"`, or `Assertion::Assert` in `.kerml`
files / `Assert::Assert` in `.sysml` files -- see the repo's `CLAUDE.md`).

## Scope

This file declares `syntax` categories and productions -- a real, working *parser* for
the `<< ... >>` formula strings. It also *elaborates* them, via the `domain%` macro,
into genuine `SFS.lean` terms: `forall x~Occurrence are φ` becomes an actual
`∀ x : SFS.Occurrence, ...`, `I[[d::f,tau]]` becomes `SFS.Get d f tau`, `<Name : params
: wff>` becomes a real curried `Prop`-valued function of `params`, and so on. The
elaborator is deliberately *not* exhaustive: constructs with no clean, honest SFS.lean
counterpart (`numberof`/`productof`/`sumof`, `shifted...by`'s missing step size -- see
their cases below) raise a clear `Macro.throwError` rather than fabricate one, and a
formula referencing an SFS.lean name that doesn't exist (e.g. `Location`'s own body
uses infix `L`, but `SFS.lean` has no `L` -- unrelated to `Location`'s own argument
type, which used to also mismatch (`Part` vs. this formula's `Occurrence` subject)
until the 2026-08-21 `Part`-retirement fixed that half) is *expected* to fail with an
honest "unknown identifier"/type-mismatch error, not silently coerced into something
that type-checks but doesn't mean what the formula says.

A formula may also reference identifiers that are neither header params nor
`SFS.lean` names -- names visible in the surrounding KerML scope the `@Assert`
attaches to (an implicit `self`, or a sibling feature of the annotated element),
per the repo's `CLAUDE.md`. See the "Scope-visible identifiers" section below
(`freeIdentsInTerm`/`freeIdentsInWff`, used from `elabDslAssert`) for how these are
auto-bound as untyped `fun` parameters rather than causing an outright failure.

## Sources

- `~/git4/Supplemental-Semantics/Chapter/TemporalLogic.tex` (Appendix J, "Domain
  Logic"): `\S`J.3 defines the propositional grammar `WFF_0` (`df-bl0wff`, this file's
  `dslWff` core: `¬`/`∧`/`→`/`@`/`≺`/`=`/bounded `∀`/parens/`⊤`/`⊥`); `\S`J.4 extends to
  full first-order `Domain` with typed `VAR`/`TYPE`/`FUNC`/`PRED` and terms `PT`
  (constants, variables, n-ary function application -- this file's `dslTerm`); `WFF`
  itself (`df-blwff`) adds n-ary predicate application, `P(...)@τ`, and `r1=r2`.
- `~/git4/Supplemental-Semantics/Chapter/ExpressionSemantics.tex` `\S`3.13.1 ("Extending
  Expression for SFS"): the concrete `NonExecutableExpression`/`RangeOrBoolean`/
  `RangeSymbol` EBNF -- `timed...at`, `shifted...by`, `forall`/`exists`/`numberof`/
  `productof`/`sumof ... in Range ... are/that ...`. This is the closest thing to a
  normative ASCII-level grammar for the formula strings, and this file's keyword choices
  (`forall`/`exists`/`are`/`that`/`in`/range symbols `..`/`.,`/`,.`/`,,`) follow it
  directly.
- Real `f="<<...>>"` strings throughout `sysml.library/Kernel Libraries/Kernel Semantic
  Library/SFS library/*.kerml`/`*.sysml` (grepped, not just the EBNF above) pinned down
  details `\S`3.13.1 leaves ambiguous or doesn't cover: `~` (not `:`) for the
  identifier-typing separator in binder lists (`x,y,z~Class`, matching Appendix J's own
  `v~Type` convention, not `\S`3.13.1's `Identifier : Type`); `in Range` is genuinely
  *optional* on quantifiers in practice (`forall x~Class are ...` with no range at all,
  vs. `forall t~Instant in tau ., now are ...` with one); `I[[d::f,tau]]`/`I[[d::f,now]]`
  (the interpretation-bracket term form, `::` for feature access, an optional trailing
  time argument); `result~Type | body` (the named-result binding form for
  function/predicate-valued `@Assert`s, e.g. `Location : o~Occurrence := result~Region |
  o L result`); `<>` for `≠`. Bare `⊤`/`⊥` were not found in any real formula string, so
  are omitted here rather than guessed at.
-/
import SFS

open Lean
open SFS

namespace SFS.Assert

/-! ## Syntax categories

All eight declared together, up front: `dslRange` and `dslWff` refer to each other
(a `dslWff` can quantify with an `in dslRange` clause; `dslRange` can itself be a bare
`dslWff` boolean guard, `\S`3.13.1's `RangeOrBoolean`), and `dslWff`'s generalized
`forall`/`exists` productions reference `dslParam`, declared much later in the source
otherwise (in the "`@Assert` top level" section, alongside its main other use). Lean
only requires a category to be *declared* (`declare_syntax_cat`) before it's named in
another category's `syntax` production -- the individual productions themselves can
still live wherever's most readable below, grouped by category as before. -/

declare_syntax_cat dslType
declare_syntax_cat dslTerm
declare_syntax_cat dslRange
declare_syntax_cat dslWff
declare_syntax_cat dslParam
declare_syntax_cat dslSep
declare_syntax_cat dslBody
declare_syntax_cat dslAssert

/-! ## Types (Appendix J `\S`J.4: `TYPE` is the `Type`/`Classifier` elements of the
design) -/

/-- A type name: `Occurrence`, `Instant`, `Region`, `Class`, `Anything`, .... -/
syntax ident : dslType

/-! ## Terms (Appendix J `\S`J.4: `PT`, built from `CON`/`VAR`/`FUNC` application) -/

/-- A variable or constant (`x`, `tau`, `d`, `now`, ...). -/
syntax ident : dslTerm

/-- KerML's own automatically-bound result variable (`Expression::result`,
`ExpressionSemantics.tex`), referenced inside a `result~Type | body` binding's own
body (e.g. `Location`'s `o L result`). A separate rule from the `ident` one above
because `"result"` is *also* used as a leading keyword (in `dslBody`'s result-binding
production), which reserves it out of plain `ident`. -/
syntax "result" : dslTerm

/-- Boolean literals (`Domain.kerml`'s own real `b = true`/`b = false`,
`GetChangeToTrue`/`GetChangeToFalse`). A separate rule from the `ident` one above,
same reason as `"result"` above but from the *other* direction: `Assert.lean` itself
never reserves `"true"`/`"false"`, but `Kernel.lean` (which imports `Assert.lean` for
`@Assert` wiring) does, for its own `kermlExpr` grammar -- once a `@Assert{...}`
formula's `f="..."` string gets re-parsed via `Lean.Parser.runParserCategory` inside
*that* file's environment (not this one), a bare `true`/`false` is no longer
available as a plain `ident` token, the same file-wide keyword-reservation collision
hit repeatedly elsewhere in this project. Explicit literal productions here make
`dslTerm`'s own boolean literals robust regardless of what other keywords get
registered by whatever file re-parses this text. -/
syntax "true" : dslTerm
syntax "false" : dslTerm

/-- A numeral. -/
syntax num : dslTerm

/-- N-ary function application, `f(t1,...,tn)`, `PT`'s `f^n_j(r_1,...,r_n)` clause. -/
syntax ident "(" dslTerm,* ")" : dslTerm

/-- The interpretation-bracket term `I[[d::f,tau]]`/`I[[d::f,now]]` (untimed:
`I[[d::f]]`), Appendix J `\S`J.5's `I_t`/`I[[·]]`. `::` is feature access (`d::f` reads
"feature `f` of `d`"); the trailing argument, when present, is the instant to evaluate
at (`tau`/`now`, or in general any `dslTerm`). -/
syntax "I[[" dslTerm "::" ident ("," dslTerm)? "]]" : dslTerm

/-- `timed E at τ` -- `\S`3.13.1's `NonExecutableExpression`, the ASCII-keyword spelling
of Appendix J's `E @ τ` for values (not found in a real `f="..."` string in this repo as
of writing; included for grammar completeness per `\S`3.13.1). -/
syntax "timed " dslTerm " at " dslTerm : dslTerm

/-- `shifted E by n` -- `\S`3.13.1's ASCII spelling of the discrete-time shift `E ^ n`
(Appendix J `\S`J.7). Same completeness caveat as `timed...at` above. -/
syntax "shifted " dslTerm " by " dslTerm : dslTerm

syntax:65 dslTerm:65 " + " dslTerm:66 : dslTerm
syntax:65 dslTerm:65 " - " dslTerm:66 : dslTerm
syntax:70 dslTerm:70 " * " dslTerm:71 : dslTerm
syntax:70 dslTerm:70 " / " dslTerm:71 : dslTerm
syntax:75 "-" dslTerm:75 : dslTerm

syntax "(" dslTerm ")" : dslTerm

/-! ## Ranges (`\S`3.13.1's `RangeOrBoolean`/`RangeSymbol`) -/

/-- `τ1 .. τ2` (closed), matching `df-bl.dd`. -/
syntax dslTerm " .. " dslTerm : dslRange
/-- `τ1 ,, τ2` (open), matching `df-bl.cc`. -/
syntax dslTerm " ,, " dslTerm : dslRange
/-- `τ1 ,. τ2` (open-left), matching `df-bl.cd`. -/
syntax dslTerm " ,. " dslTerm : dslRange
/-- `τ1 ., τ2` (open-right), matching `df-bl.dc`. -/
syntax dslTerm " ., " dslTerm : dslRange

/-- `RangeOrBoolean`'s other alternative (`ExpressionSemantics.tex` `\S`3.13.1): a
bare boolean guard instead of an interval, e.g. `exists t2~Instant in t2<t1 that ...`
(`RunTimeServices.kerml`) -- `t2<t1` isn't shaped like any of the four range symbols
above, it's an ordinary comparison. Unlike the interval forms, this guard is a
self-contained proposition over already-bound identifiers (not a per-variable
membership check), so its elaboration ignores the bound-variable argument entirely --
see `elabDslRangeGuard`'s corresponding case. -/
syntax dslWff : dslRange

/-! ## Well-formed formulas (Appendix J `df-bl0wff`/`df-blwff`) -/

/-- A bare proposition symbol (SFS.mm/`PROP`), e.g. `PartOf`'s own body `xPy`: an
otherwise-unparsed atomic formula name standing for some primitive relation. -/
syntax ident : dslWff

/-- N-ary predicate application, `P(t1,...,tn)`, e.g. `PartOf(x,y)`. Same concrete
syntax as `dslTerm`'s own `ident "(" ... ")"` production (both elaborate identically,
`$f $args*`), which is ambiguous whenever a `dslBody` is *only* a bare call with
nothing else disambiguating it (e.g. the anonymous form `<<during(self,
thisPerformance)>>`) -- `(priority := high)` makes the parser commit to this one
instead of leaving an unresolved `choice` node that `elabDslAssert`'s pattern match
can't see through. -/
syntax (priority := high) ident "(" dslTerm,* ")" : dslWff

/-- Infix binary relation, `x R y` -- e.g. `Location`'s own body `o L result` (`L` the
relation name). A separate production from the bare-`ident` and `P(args)` forms above:
those are a formula standing alone, or a name immediately applied to a parenthesized
argument list; this is a name used *between* two terms, KerML-relation-declaration
style (`o L result` reads "`o` is `Location`d at `result`"). -/
syntax dslTerm:71 ident dslTerm:71 : dslWff

syntax dslTerm " < " dslTerm : dslWff
syntax dslTerm " <= " dslTerm : dslWff
syntax dslTerm " > " dslTerm : dslWff
syntax dslTerm " >= " dslTerm : dslWff
syntax dslTerm " = " dslTerm : dslWff
/-- `X = A ,, B`, equality against an open-interval literal (`Occurrences.kerml`'s
`middleTimeSlice = startShot ,, endShot`) -- a dedicated `dslWff`-level production
for this exact three-`dslTerm` shape, not a general `,,`-producing `dslTerm`
alternative: giving `dslTerm` itself a `,,` production was tried first and rejected
-- `dslRange`'s own *existing* `,,` production (`elabDslRangeGuard`'s `$a:dslTerm ,,
$b:dslTerm` arm below) already embeds a literal `,,` inside a `dslTerm`-antiquotation
pattern, and once `dslTerm` can itself produce `,,`, that quotation becomes
genuinely unparseable (confirmed via a real build attempt, not assumed) -- the two
uses of `,,` recursively conflict when both are reachable from a bare `$x:dslTerm`
antiquotation. Scoping `,,` to this one three-operand `dslWff` shape sidesteps the
conflict entirely: `dslTerm` itself never gains a `,,` alternative. -/
syntax dslTerm " = " dslTerm " ,, " dslTerm : dslWff
/-- `≠`, e.g. `I[[d::f,tau]] <> I[[d::f,now]]`. -/
syntax dslTerm " <> " dslTerm : dslWff

/-- Set/region/surface membership, e.g. `p2 in Adj(p)`. Same token as the quantifier
binder's `in Range` clause below, disambiguated by context (a `dslWff` slot expects a
`dslTerm` on the right here, not a `dslRange`/`dslType`). -/
syntax dslTerm " in " dslTerm : dslWff

/-- `φ @ τ`, Appendix J's timed-evaluation primitive (`df-bl.at`/`SFS.lean`'s `atP`).
Not seen spelled this way in a real `f="..."` string (they go through `I[[·,τ]]`
instead), included for fidelity to `df-bl0wff`. -/
syntax dslWff " @ " dslTerm : dslWff

/-- `I[[d::e,tau]]`, the *predicate* reading of the interpretation-bracket notation --
same concrete syntax as `dslTerm`'s own `I[[...]]` production above, registered
separately under `dslWff` so the identical real text (`Domain.kerml`'s own
`GetBooleanChange`/`GetChangeToTrue`/`GetChangeToFalse`, e.g. bare `not
I[[d::e,t]]`/`I[[d::e,now]] and ...`) elaborates via `SFS.lean`'s `GetP` (a genuine
`Prop`) instead of `Get` (a `Set Item`) whenever it appears where a `dslWff` is
expected, disambiguated purely by grammatical position -- no new spelling, matching
KerML's own `\S`3.13.1 class-expression (`A`) vs. Boolean-expression (`φ`) split.
The untimed form (`I[[d::e]]`, no `tau`) has no `GetPC`-style counterpart -- no real
formula in this repo needs it yet, so it's a genuine (documented, not silent) macro
error rather than a guessed definition. **This makes a bare `I[[d::f,tau]]` genuinely
ambiguous** against `dslTerm`'s own identical-looking `I[[...]]` production (`Get`/
`GetNow`'s real `:=`-bodies are exactly this bare shape, needing the `dslTerm`/`Get`
reading) -- resolved not here but at `dslAssert`'s own level, see the dedicated
`:=`-body production below `dslBody`'s declaration, which realizes the `:`/`:=` split
`dslSep`'s own doc comment already promised but (until this ambiguity actually
existed) never needed to enforce. -/
syntax "I[[" dslTerm "::" ident ("," dslTerm)? "]]" : dslWff

syntax:75 "not " dslWff:75 : dslWff
syntax:40 dslWff:41 " and " dslWff:40 : dslWff
syntax:35 dslWff:36 " or " dslWff:35 : dslWff
syntax:30 dslWff:31 " implies " dslWff:30 : dslWff
syntax:25 dslWff:26 " iff " dslWff:25 : dslWff

/-- Bounded/unbounded universal quantification, `\S`3.13.1's `forall`, `df-bl.al`'s
ASCII form. `in Range` is optional in practice (real formulas often quantify over an
entire type with no range at all, e.g. `forall x~Class are not PartOf(x,x)`), though
`\S`3.13.1's own EBNF does not mark it so. Takes `dslParam,+` (not `\S`3.13.1's own
single-type `Identifier (',' Identifier)* ':' Type`) so a single `forall` can bind
several differently-typed groups at once, comma-separated -- e.g.
`RunTimeServices.kerml`'s `forall v~Anything, t1~Instant are ...` -- reusing the same
grammar/elaboration already needed for `@Assert`'s own parameter header. -/
syntax "forall " dslParam,+ (" in " dslRange)? " are " dslWff : dslWff

/-- `Regions.kerml`'s own idiom for the same thing as the comma-joined form above, but
spelled with a second `forall` keyword instead of a comma -- e.g. `forall x~Occurrence
forall r1,r2~Region are ...` (`LFU`/`LIN`/`EXPNS`/`APAR`). Not part of `\S`3.13.1's
EBNF; included because it's the form this repo's own Regions.kerml consistently uses. -/
syntax "forall " dslParam,+ (" in " dslRange)? " forall " dslParam,+ (" in " dslRange)? " are " dslWff : dslWff

/-- Bounded/unbounded existential quantification, `df-bl.ex`'s ASCII form. -/
syntax "exists " dslParam,+ (" in " dslRange)? " that " dslWff : dslWff

/-- Counting quantifier, value-producing (a `dslTerm`, not a `dslWff`) despite reading
like `exists`. -/
syntax "numberof " ident,+ "~" dslType (" in " dslRange)? " that " dslWff : dslTerm

/-- Indexed product, Appendix J's `\S`3.13.1 `productof`. -/
syntax "productof " ident,+ "~" dslType (" in " dslRange)? " that " dslTerm : dslTerm

/-- Indexed sum, `\S`3.13.1 `sumof`. -/
syntax "sumof " ident,+ "~" dslType (" in " dslRange)? " that " dslTerm : dslTerm

syntax "(" dslWff ")" : dslWff

/-! ## `@Assert` top level: `<<Name : params (: | :=) body>>` -/

/-- One parameter-group in the header: `x,y,z~Class` (identifiers sharing one type). -/
syntax ident,+ "~" dslType : dslParam

/-- The `: | :=` separator between the parameter list and the body: `:` for a
predicate/relation body (a `dslWff`), `:=` for a value-defining body (a `dslTerm`, or
the named-result form below). -/
syntax ":" : dslSep
syntax ":=" : dslSep

/-- A body is a formula, a term, or a named-result binding: `result~Type | wff`, e.g.
`Location`'s `result~Region | o L result`, or `RegionSurface`'s
`result~Surface | forall p~Point are ...`. `(priority := high)` on the `dslWff`
alternative: a bare `ident(args)` (or any other shape valid under both `dslWff`'s and
`dslTerm`'s own `ident(args)` productions) is ambiguous at *this* level too, not just
within `dslWff` itself (see that production's own note) -- `dslBody`'s two
alternatives being equal-priority by default left an unresolved `choice` node neither
of `elabDslAssert`'s pattern-match arms could destructure, breaking the anonymous
form whenever its entire body is a bare call (e.g. `<<during(self,
thisPerformance)>>`, `Performances.kerml`'s real usage). Preferring `dslWff` is the
sensible default -- `@Assert`/`inv{}` anonymous-form attachments are always
constraints (propositions), and no real `:=`-separated (term-valued) named-form body
is a bare call, so this doesn't affect that separator-disambiguated path. -/
syntax (priority := high) dslWff : dslBody
syntax dslTerm : dslBody
syntax "result" "~" dslType " | " dslWff : dslBody

/-- `<<Name : params sep body>>`, e.g. `<<next : tau1~Instant, tau2~Instant : (tau1 <
tau2 and not exists tau~Instant that (tau1 < tau and tau < tau2))>>`, or
`<<Get : d~Occurrence, f~Anything, tau~Instant := I[[d::f,tau]]>>`. -/
syntax "<<" ident ":" dslParam,* dslSep dslBody ">>" : dslAssert

/-- `:=`-separated bodies are always value-definitions (`dslTerm`), per `dslSep`'s own
doc comment (`:` for a `dslWff`, `:=` for a `dslTerm`) -- but the generic production
above doesn't actually *enforce* that split; it just tries `dslBody`'s `(priority :=
high) dslWff` alternative first, same as it would for a `:`-separated body. This was
harmless as long as no real `dslWff` production could also match a `:=`-body's own
text -- no longer true once `I[[...]]` became valid `dslWff` too (`Get`/`GetNow`'s
own real `:=`-bodies, `I[[d::f,tau]]`/`I[[d::f,now]]`, are exactly this bare shape,
needing `dslTerm`'s `Get` reading, not the new `dslWff` `GetP` one). `(priority :=
high)`, tried before the generic production above, so a genuine `:=` separator always
forces the `dslTerm` reading regardless of what else the body text could also parse
as. Only covers a bare `dslTerm` body (not `result~Type | wff`) -- no real `:=`-body
in this repo uses that shape; anything else still falls through to the generic
production's own `dslTerm : dslBody` alternative, unaffected by this addition. -/
syntax (priority := high) "<<" ident ":" dslParam,* ":=" dslTerm ">>" : dslAssert

/-- The anonymous form, `<<body>>` with no `Name :` header at all -- common in `inv{}`
attachments outside the SFS library folder proper (`Performances.kerml`,
`Objects.kerml`, `Occurrences.kerml`, `Links.kerml`), where the formula is just a bare
constraint on the surrounding element, not a reusable named definition, e.g.
`<< during(self, thisPerformance) >>`. Not covered by `\S`3.13.1's own EBNF (which only
describes the quantifier/timed/shifted forms, not the `<<...>>` wrapper itself) --
grounded directly in these real, unnamed `f="<<...>>"` strings. -/
syntax "<<" dslBody ">>" : dslAssert

/-! ## Elaboration

`<`/`<=` are overloaded across whatever the DSL's terms turn out to elaborate to
(`SFS.Time`, plain `ℝ`, ...) via this typeclass, resolved by Lean's *real* elaborator
once the surrounding term is fully built -- not guessed at macro-expansion time, when
the actual Lean type of an arbitrary sub-term isn't generally knowable. This is what
lets `tau1 < tau2` (both elaborating to `SFS.Time`) produce `SFS.tprec`-based
comparison while a real-valued `<` elsewhere in the same file produces plain `ℝ`
comparison, from the exact same generated `DSLLt.lt` call.

2026-08-27, at direct request ("Can the Kleene operators be removed?"): the whole
`Option Prop`-valued layer this section held (`DSLLt`/`DSLLe`/`DSLEq`/`DSLAnd`/
`DSLOr`'s `Option`-involving instances, `DSLNext` entirely) is retired.
`SFS.death`'s own partiality was the *only* thing ever routing a real formula
through them; now that `death(x)` calls in a formula are special-cased to
`SFS.effectiveEnd` instead (a total `Time`, see `elabDslTerm`'s matching case
below), nothing produces an `Option Prop`/`Option Time` operand here anymore. Two
type parameters would suffice now, but `α β : Type _`/`γ : outParam Type _` is kept
(mirroring Lean's own `HAdd`/`HMul` idiom) since it costs nothing and keeps the
door open if a genuinely partial value shows up here again. -/
class DSLLt (α β : Type _) (γ : outParam (Type _)) where lt : α → β → γ
class DSLLe (α β : Type _) (γ : outParam (Type _)) where le : α → β → γ

instance : DSLLt Time Time Prop := ⟨fun t1 t2 => t1.val ≺ t2.val⟩
instance : DSLLe Time Time Prop := ⟨fun t1 t2 => t1.val ≼ t2.val⟩
instance : DSLLt ℝ ℝ Prop := ⟨(· < ·)⟩
instance : DSLLe ℝ ℝ Prop := ⟨(· ≤ ·)⟩

/-- `in`'s dslWff sense (`x in y`, e.g. `PointInRegion`'s own body `point in region`) is
overloaded the same way `<`/`<=` are: `SFS.lean` doesn't model spatial containment via
Mathlib's `Membership` (`Point`/`Region`/`Surface` are opaque axiom types with no such
instance), it uses separate primitive relations (`InRegion`, `OnSurface`) instead, so a
generic `∈`-based elaboration would fail outright rather than just mismatch. Only the
two pairs actually used this way in real formulas get instances -- no generic
`[Membership α β]`-derived fallback, matching `DSLLt`/`DSLLe`'s own precedent of not
over-generalizing beyond what's observed. -/
class DSLMem (α : Type _) (β : Type _) where mem : α → β → Prop

instance : DSLMem Point Region := ⟨InRegion⟩
instance : DSLMem Point Surface := ⟨OnSurface⟩

/-- `=` is used generically across an open-ended set of types today (`Occurrence`,
`Bool`, `Set Item`, `Time`, ...) via bare Lean `Eq` -- a single generic fallback,
no fixed list of concrete instances needed (the `Option Time`-involving concrete
instances this used to need, to keep `none = none` from silently elaborating to
`True`, are gone along with `death`'s own partiality -- see this section's header
note). -/
class DSLEq (α β : Type _) (γ : outParam (Type _)) where eq : α → β → γ

instance {α : Type _} : DSLEq α α Prop := ⟨Eq⟩

/-- `and`/`or` are used generically on plain `Prop` (every `@Assert` formula, now
that nothing here is `Option`-valued). Field names are `conj`/`disj`, not `and`/
`or` -- the latter are this file's own `dslWff` syntax keywords (`syntax ... "
and " ...` above), so `where and : ...` would parse `and` as that keyword, not a
field name. -/
class DSLAnd (α β : Type _) (γ : outParam (Type _)) where conj : α → β → γ
class DSLOr (α β : Type _) (γ : outParam (Type _)) where disj : α → β → γ

instance : DSLAnd Prop Prop Prop := ⟨And⟩
instance : DSLOr Prop Prop Prop := ⟨Or⟩

/-- `dslType` → the `SFS.lean` type it names. Recognized DSL type names are mapped to
their `SFS.lean` counterpart; anything else is passed through as a bare identifier
(so it resolves if some matching Lean declaration happens to exist, and fails with an
honest "unknown identifier" otherwise, rather than being silently mismapped).
`"Class"` was removed 2026-08-21 -- `Mereology.kerml`'s own `x~Class` params (the
only real use of that name anywhere in the repo) were changed to `x~Occurrence` in
the KerML source itself, and `SFS.lean`'s own `Part` type they used to map to was
retired the same day (`PartOf` etc. are `Occurrence`-typed now); leaving `"Class"`
mapped to a nonexistent (or, worse, Mathlib's *own* unrelated `Part`) target would be
a live footgun, not dead code worth keeping around. -/
def elabDslType : TSyntax `dslType → MacroM (TSyntax `term)
  | `(dslType| $t:ident) => do
    match t.getId.toString with
    | "Instant" => `(Time)
    | "Occurrence" => `(Occurrence)
    | "Region" => `(Region)
    | "Point" => `(Point)
    | "Surface" => `(Surface)
    | "Anything" => `(KerML.Root.Element)
    | "BooleanEvaluation" => `(KerML.Root.Element)
    | _ => `($t)
  | _ => Macro.throwUnsupported

/-- Programmatically-built identifier for KerML's automatically-bound `result`
variable, used instead of writing bare `result` inside a quotation: `"result"` is a
reserved keyword (via `dslTerm`'s and `dslBody`'s own `syntax` declarations above),
so Lean's own term parser would reject a literal `result` token, even though building
an `Ident` node directly for it (bypassing tokenization) is completely fine. -/
def resultIdent : Ident := mkIdent `result

/-- `dslParam` (`x,y,z~Class`) → one `(name, elaborated-type)` pair per identifier in
the group, sharing the group's single type. Defined ahead of the `mutual` block below
(rather than alongside `elabDslAssert`, its main other caller) because the generalized
`forall`/`exists` elaboration inside that block now calls it too. -/
def elabDslParam : TSyntax `dslParam → MacroM (Array (TSyntax `ident × TSyntax `term))
  | `(dslParam| $xs:ident,* ~ $ty:dslType) => do
    let ty' ← elabDslType ty
    pure (xs.getElems.map (·, ty'))
  | _ => Macro.throwUnsupported

/-- Recursively splits a compound dotted identifier `a.b.c...` into nested function
application `c (b a)`, reusing whatever real Lean identifiers already exist for each
segment -- no new `SFS.lean` objects needed for an arbitrary-length chain, just
repeated application of the single-level trick already established for `x.openLeft`
(2026-08-27, at direct request: "there will be many references... sometimes names
which will be a sequence of identifiers separated by periods. Can you interpret such
references without adding new objects?"). Lean's *lexer* fuses an unspaced `a.b.c`
into one compound `ident` token before any grammar-level choice runs (same reasoning
as the original single-level fix's own doc note), so this is still the only way to
reach it -- a `dslTerm "." ident` grammar production could never fire for real,
unspaced formula text. `now` is special-cased at the base case exactly as before,
only reachable when the *whole* chain is just `now` (a dotted `now.x` would be
strange and isn't attempted). A chain segment that isn't a real Lean identifier still
fails honestly (unresolved identifier), not guessed at. -/
partial def elabDotChain (x : Ident) : MacroM (TSyntax `term) := do
  match x.getId with
  | .str pre s =>
    if pre == .anonymous then
      if x.getId == `now then `((⟨now, dl_nowt⟩ : Time)) else pure x
    else
      let f := mkIdentFrom x (Name.mkSimple s)
      let recv ← elabDotChain (mkIdentFrom x pre)
      `($f $recv)
  | _ => pure x

/-- The root/base identifier of a dotted chain `a.b.c...` -- `a` itself, recursed
all the way down rather than peeling one level (`freeIdentsInTerm`'s counterpart to
`elabDotChain` above: only the base is a genuine free identifier needing binding,
every other segment is a call head). -/
partial def dotChainBase (n : Name) : Name :=
  match n with
  | .str pre _ => if pre == .anonymous then n else dotChainBase pre
  | _ => n

mutual

/-- `dslTerm` → the `SFS.lean`/Lean term it denotes. -/
partial def elabDslTerm : TSyntax `dslTerm → MacroM (TSyntax `term)
  | `(dslTerm| result) => `($resultIdent)
  | `(dslTerm| true) => `(Bool.true)
  | `(dslTerm| false) => `(Bool.false)
  | `(dslTerm| $x:ident) => elabDotChain x
  | `(dslTerm| $n:num) => `($n)
  | `(dslTerm| $f:ident($args,*)) => do
    let args ← args.getElems.mapM elabDslTerm
    -- `death(...)` is special-cased to `SFS.effectiveEnd` (2026-08-27, "Can the
    -- Kleene operators be removed?"): every real `@Assert` formula's `death(x)`
    -- now means "A's real end if known, else now" -- `SFS.death` itself (still
    -- Option-valued, the faithful structural fact) is untouched, only what a
    -- *formula* means by "death" changes. Every other `ident(args)` term keeps
    -- plain application.
    if f.getId == `death then
      match args with
      | #[a] => `(SFS.effectiveEnd $a)
      | _ => `($f $args*)
    else
      `($f $args*)
  | `(dslTerm| I[[ $d:dslTerm :: $f:ident $[, $tau:dslTerm]? ]]) => do
    let d' ← elabDslTerm d
    match tau with
    | some tau => do let tau' ← elabDslTerm tau; `(Get $d' $f $tau')
    | none => `(GetC $d' $f)
  | `(dslTerm| timed $e:dslTerm at $tau:dslTerm) => do
    let e' ← elabDslTerm e; let tau' ← elabDslTerm tau
    `(interpValAt $e' $tau')
  | `(dslTerm| shifted $_e:dslTerm by $_n:dslTerm) =>
    Macro.throwError "shifted...by: the step size D isn't part of this syntax form \
      (SFS.lean's shiftEvalC needs both D and n), so this can't be elaborated yet"
  | `(dslTerm| $a:dslTerm + $b:dslTerm) => do `($(← elabDslTerm a) + $(← elabDslTerm b))
  | `(dslTerm| $a:dslTerm - $b:dslTerm) => do `($(← elabDslTerm a) - $(← elabDslTerm b))
  | `(dslTerm| $a:dslTerm * $b:dslTerm) => do `($(← elabDslTerm a) * $(← elabDslTerm b))
  | `(dslTerm| $a:dslTerm / $b:dslTerm) => do `($(← elabDslTerm a) / $(← elabDslTerm b))
  | `(dslTerm| -$a:dslTerm) => do `(-$(← elabDslTerm a))
  | `(dslTerm| ($a:dslTerm)) => elabDslTerm a
  | `(dslTerm| numberof $_xs,* ~ $_ty $[in $_r]? that $_body:dslWff) =>
    Macro.throwError "numberof: not yet supported (needs Finset.sum/Set.ncard-style \
      integration, same as SFS.lean's df-bl.atsum scope note)"
  | `(dslTerm| productof $_xs,* ~ $_ty $[in $_r]? that $_body:dslTerm) =>
    Macro.throwError "productof: not yet supported (needs Finset.prod integration, \
      same as SFS.lean's df-bl.atsum scope note)"
  | `(dslTerm| sumof $_xs,* ~ $_ty $[in $_r]? that $_body:dslTerm) =>
    Macro.throwError "sumof: not yet supported (needs Finset.sum integration, same \
      as SFS.lean's df-bl.atsum scope note)"
  | _ => Macro.throwUnsupported

/-- `dslRange` → a `Prop`-valued membership guard for a given (already-elaborated)
bound-variable term, matching `SFS.lean`'s own `Set.Icc`/`Set.Ioo`/`Set.Ioc`/`Set.Ico`
convention for the four interval shapes (`dl_alldd`/`dl_allcc`/`dl_allcd`/`dl_alldc`). -/
partial def elabDslRangeGuard (x : TSyntax `term) : TSyntax `dslRange → MacroM (TSyntax `term)
  | `(dslRange| $a:dslTerm .. $b:dslTerm) => do
    `($x ∈ Set.Icc $(← elabDslTerm a) $(← elabDslTerm b))
  | `(dslRange| $a:dslTerm ,, $b:dslTerm) => do
    `($x ∈ Set.Ioo $(← elabDslTerm a) $(← elabDslTerm b))
  | `(dslRange| $a:dslTerm ,. $b:dslTerm) => do
    `($x ∈ Set.Ioc $(← elabDslTerm a) $(← elabDslTerm b))
  | `(dslRange| $a:dslTerm ., $b:dslTerm) => do
    `($x ∈ Set.Ico $(← elabDslTerm a) $(← elabDslTerm b))
  | `(dslRange| $φ:dslWff) => do
    match collectionRangeName φ with
    | some name => mkCollectionGuard name x
    | none => elabDslWff φ
  | _ => Macro.throwUnsupported

/-- Recognizes a bare-`ident` `dslWff` naming one of the `composite`-flagged
association-derived collections found so far across the Kernel Semantic Library
(`Occurrences.kerml`'s `suboccurrences`/`immediatePredecessors`/
`immediateSuccessors`; `Performances.kerml`'s `subperformances`, which genuinely
`subsets suboccurrences` in the real KerML, so it reuses the same
`IsSuboccurrenceOf` relation rather than getting its own) by checking its *name*,
rather than adding new dedicated `dslRange` grammar for them: a dedicated
`syntax "suboccurrences" : dslRange` was tried first and rejected -- it reserves
the word as a literal token file-wide, which collides with `kermlFeature`'s own
declared-name position (`feature suboccurrences: ...`, needed as a plain
identifier there), confirmed via a real build error. Same "check the name, don't
reserve the token" fix `elabDslWff`'s own `next` special-case already uses. Used
by both `elabDslRangeGuard`'s own bare-guard case above and `wrapForall`/
`wrapExists`'s own dedicated bare-`dslWff`-range short-circuit below -- the latter
is the *actually*-exercised path for `forall x~T in RANGE are ...` (confirmed the
hard way: an earlier version of this fix lived only in `elabDslRangeGuard`, which
`wrapForall`/`wrapExists` never call for this shape at all, and it silently never
fired). Not a general "range over any named collection" mechanism -- only these
specific, observed names get a production, same "no over-generalization"
discipline as `DSLMem`'s own hard-coded pairs; grows one name at a time as
`composite` features get their own `@Assert` added across the library. -/
partial def collectionRangeName (φ : TSyntax `dslWff) : Option Name :=
  match φ with
  | `(dslWff| $rangeName:ident) =>
    if rangeName.getId == `suboccurrences ∨ rangeName.getId == `immediatePredecessors ∨
        rangeName.getId == `immediateSuccessors ∨ rangeName.getId == `subperformances then
      some rangeName.getId
    else none
  | _ => none

/-- The guard itself for one of `collectionRangeName`'s recognized names,
given the bound-variable term `x`. Unlike a genuine guard (which ignores the bound
variable entirely, see `wrapForall`/`wrapExists`'s other branch), these genuinely
depend on it: `IsSuboccurrenceOf $x self`, not a free-standing condition.
`self`/`this` aren't declared here -- they're spliced directly into the elaborated
term, relying on every real formula using one of these ranges to *also*
mention `self`/`this` elsewhere in the same body (true of every real case so
far), so the ordinary free-identifier auto-binder discovers and types them from
that other occurrence. -/
partial def mkCollectionGuard (name : Name) (x : TSyntax `term) : MacroM (TSyntax `term) := do
  -- `mkIdent`, not a bare literal `self`/`this` in the quotation -- a plain
  -- unquoted identifier here gets hygienically renamed (confirmed via a real
  -- build error, "Unknown identifier self✝") since it looks like a fresh local
  -- reference to Lean's macro hygiene, not the free outer-scope name that needs
  -- to line up with `self`/`this`'s *other* occurrence elsewhere in the same
  -- formula (see this function's own doc comment above). Same fix `resultIdent`
  -- already established for exactly this shape of problem.
  let selfIdent := mkIdent `self
  let thisIdent := mkIdent `this
  if name == `suboccurrences ∨ name == `subperformances then
    `(SFS.IsSuboccurrenceOf $x $selfIdent)
  else if name == `immediatePredecessors then `(SFS.IsImmediatePredecessorOf $x $thisIdent)
  else `(SFS.IsImmediateSuccessorOf $x $thisIdent)

/-- Shared by the plain and chained `forall` productions: nests `∀` over every
`(name, type)` binder, with an optional trailing range/guard. An *interval*-shaped
range (`..`/`,,`/`,.`/`.,`) is checked per-variable, exactly as before generalizing to
multi-group binders (each bound name gets its own `x ∈ range` conjunct/hypothesis) --
the only real formula using this shape (`Domain.kerml`'s `in tau ., now`) has a single
binder anyway, so this never had to handle the multi-binder case. A *boolean*-shaped
range (the new `dslWff`-as-`dslRange` alternative, e.g. `in t1<t2`) is a single
self-contained proposition over the already-bound names, so it's applied exactly once,
at the innermost position, not duplicated per binder. -/
partial def wrapForall (binders : Array (TSyntax `ident × TSyntax `term))
    (r : Option (TSyntax `dslRange)) (base : TSyntax `term) : MacroM (TSyntax `term) := do
  match r with
  | some rr =>
    match rr with
    | `(dslRange| $φ:dslWff) =>
      match collectionRangeName φ with
      | some name => binders.foldrM (fun b acc => do
          let g ← mkCollectionGuard name (← `($(b.1)))
          `(∀ ($(b.1) : $(b.2)), $g → $acc)) base
      | none => do
        let inner ← `($(← elabDslWff φ) → $base)
        binders.foldrM (fun b acc => `(∀ ($(b.1) : $(b.2)), $acc)) inner
    | _ => binders.foldrM (fun b acc => do
        let g ← elabDslRangeGuard (← `($(b.1))) rr
        `(∀ ($(b.1) : $(b.2)), $g → $acc)) base
  | none => binders.foldrM (fun b acc => `(∀ ($(b.1) : $(b.2)), $acc)) base

/-- `exists` counterpart of `wrapForall`, same interval-vs-boolean range handling. Built
via plain `fun`/`Exists`, not `∃`-notation, for the same hygiene reason documented at
the original single-group `exists` case this replaced. -/
partial def wrapExists (binders : Array (TSyntax `ident × TSyntax `term))
    (r : Option (TSyntax `dslRange)) (base : TSyntax `term) : MacroM (TSyntax `term) := do
  match r with
  | some rr =>
    match rr with
    | `(dslRange| $φ:dslWff) =>
      match collectionRangeName φ with
      | some name => binders.foldrM (fun b acc => do
          let g ← mkCollectionGuard name (← `($(b.1)))
          `(Exists (fun ($(b.1) : $(b.2)) => $g ∧ $acc))) base
      | none => do
        let inner ← `($(← elabDslWff φ) ∧ $base)
        binders.foldrM (fun b acc => `(Exists (fun ($(b.1) : $(b.2)) => $acc))) inner
    | _ => binders.foldrM (fun b acc => do
        let g ← elabDslRangeGuard (← `($(b.1))) rr
        `(Exists (fun ($(b.1) : $(b.2)) => $g ∧ $acc))) base
  | none => binders.foldrM (fun b acc => `(Exists (fun ($(b.1) : $(b.2)) => $acc))) base

/-- `dslWff` → the `Prop` it denotes. -/
partial def elabDslWff : TSyntax `dslWff → MacroM (TSyntax `term)
  | `(dslWff| $x:ident) => elabDotChain x
  | `(dslWff| $f:ident($args,*)) => do
    let args ← args.getElems.mapM elabDslTerm
    `($f $args*)
  | `(dslWff| $a:dslTerm $r:ident $b:dslTerm) => do
    `($r $(← elabDslTerm a) $(← elabDslTerm b))
  | `(dslWff| $a:dslTerm < $b:dslTerm) => do `(DSLLt.lt $(← elabDslTerm a) $(← elabDslTerm b))
  | `(dslWff| $a:dslTerm <= $b:dslTerm) => do `(DSLLe.le $(← elabDslTerm a) $(← elabDslTerm b))
  | `(dslWff| $a:dslTerm > $b:dslTerm) => do `(DSLLt.lt $(← elabDslTerm b) $(← elabDslTerm a))
  | `(dslWff| $a:dslTerm >= $b:dslTerm) => do `(DSLLe.le $(← elabDslTerm b) $(← elabDslTerm a))
  | `(dslWff| $a:dslTerm = $b:dslTerm ,, $c:dslTerm) => do
    `(DSLEq.eq $(← elabDslTerm a) (SFS.mkOpenInterval $(← elabDslTerm b) $(← elabDslTerm c)))
  | `(dslWff| $a:dslTerm = $b:dslTerm) => do `(DSLEq.eq $(← elabDslTerm a) $(← elabDslTerm b))
  | `(dslWff| $a:dslTerm <> $b:dslTerm) => do `($(← elabDslTerm a) ≠ $(← elabDslTerm b))
  | `(dslWff| $a:dslTerm in $b:dslTerm) => do
    `(DSLMem.mem $(← elabDslTerm a) $(← elabDslTerm b))
  | `(dslWff| $φ:dslWff @ $tau:dslTerm) => do
    `(interpAt $(← elabDslWff φ) $(← elabDslTerm tau))
  | `(dslWff| I[[ $d:dslTerm :: $f:ident $[, $tau:dslTerm]? ]]) => do
    let d' ← elabDslTerm d
    match tau with
    | some tau => do let tau' ← elabDslTerm tau; `(GetP $d' $f $tau')
    | none => Macro.throwError "I[[d::f]] (untimed) as a wff: no GetPC-style \
        predicate reading is defined yet -- every real formula using this position \
        gives an explicit time (I[[d::f,tau]])"
  | `(dslWff| not $φ:dslWff) => do `(¬ $(← elabDslWff φ))
  | `(dslWff| $φ:dslWff and $ψ:dslWff) => do `(DSLAnd.conj $(← elabDslWff φ) $(← elabDslWff ψ))
  | `(dslWff| $φ:dslWff or $ψ:dslWff) => do `(DSLOr.disj $(← elabDslWff φ) $(← elabDslWff ψ))
  | `(dslWff| $φ:dslWff implies $ψ:dslWff) => do `($(← elabDslWff φ) → $(← elabDslWff ψ))
  | `(dslWff| $φ:dslWff iff $ψ:dslWff) => do `($(← elabDslWff φ) ↔ $(← elabDslWff ψ))
  | `(dslWff| forall $ps,* $[in $r:dslRange]? are $body:dslWff) => do
    let groups ← ps.getElems.mapM elabDslParam
    let binders := groups.foldl (· ++ ·) #[]
    wrapForall binders r (← elabDslWff body)
  | `(dslWff| forall $ps1,* $[in $r1:dslRange]? forall $ps2,* $[in $r2:dslRange]? are $body:dslWff) => do
    let groups1 ← ps1.getElems.mapM elabDslParam
    let binders1 := groups1.foldl (· ++ ·) #[]
    let groups2 ← ps2.getElems.mapM elabDslParam
    let binders2 := groups2.foldl (· ++ ·) #[]
    let inner ← wrapForall binders2 r2 (← elabDslWff body)
    wrapForall binders1 r1 inner
  | `(dslWff| exists $ps,* $[in $r:dslRange]? that $body:dslWff) => do
    let groups ← ps.getElems.mapM elabDslParam
    let binders := groups.foldl (· ++ ·) #[]
    wrapExists binders r (← elabDslWff body)
  | `(dslWff| ($φ:dslWff)) => elabDslWff φ
  | _ => Macro.throwUnsupported

end

/-! ## Scope-visible identifiers (repo `CLAUDE.md`: "The `<<Name : var~Type, ... :
body>>` header only needs to declare identifiers that aren't otherwise resolvable. An
identifier already visible in the lexical scope where the `@Assert` appears... does
not need to be re-listed as a formula parameter"). Real formulas rely on this
throughout the standard library, *outside* the SFS library's own formula-defining
files -- e.g. `Performances.kerml`'s `<< during(self, thisPerformance) >>`,
`Occurrences.kerml`'s `<< middleTimeSlice = startShot ,, endShot >>`,
`Links.kerml`'s `<< thisThing = sameThing >>` -- where `self`/`thisPerformance`/
`middleTimeSlice`/`startShot`/`endShot`/`thisThing`/`sameThing` are features of
whatever KerML element the `@Assert`/`@Invariant` is attached to (or KerML's own
implicit `self`), never declared in any header (these are all the *anonymous*
`<<body>>` form, with no header at all) and not existing `SFS.lean` names either.

Since this file has no access to the actual KerML element's feature list (no symbol
table -- same "structural only" scope `Root.lean`/`Core.lean`/`Kernel.lean` already
established), such names are handled by **auto-binding**: any identifier used in a
`dslTerm`-leaf position (a call argument, an infix-relation operand, an arithmetic
operand, ...) that isn't a header parameter, a quantifier-bound name, or `result`,
becomes an additional, *untyped* `fun` binder wrapping the elaborated body -- Lean's
own elaborator then infers its type from how it's used (e.g. `during self
thisPerformance` against `SFS.lean`'s real `during : Occurrence → Occurrence →
Option Prop` pins both to `Occurrence`). This is exactly `Elab.Term.elabTerm`'s existing
job for `now`'s special case already did for one name; generalized here to any name.

**Deliberately not extended to `dslWff`'s own bare-identifier case** (`xPy`-style,
`syntax ident : dslWff` -- a WFF that's *only* one atomic name, not an argument to
anything) -- unlike the cases above, no real formula was found using this position
for a genuine scope-visible name; `Mereology.kerml`'s `PartOf`'s own body (`xPy`,
informal "x P y" shorthand) is the one real instance, and it's *supposed* to keep
failing honestly (per this file's own header note) rather than silently succeed as
`fun xPy => xPy`, a vacuous, misleadingly type-correct term that would no longer
mean "PartOf x y" at all. So `freeIdentsInWff`'s own bare-`ident` case always
returns empty -- auto-binding only reaches names through `freeIdentsInTerm`. -/

mutual

/-- Free (unbound) identifiers in a `dslTerm`, given the names already bound by an
enclosing header/quantifier/`result`. Call heads (`f` in `f(args)`) and infix
relation names (`R` in `a R b`, in `freeIdentsInWff` below) are *never* free --
they're meant to resolve as existing `SFS.lean` names, same as today. -/
partial def freeIdentsInTerm (bound : List Name) : TSyntax `dslTerm → MacroM (List Name)
  | `(dslTerm| result) => pure []
  | `(dslTerm| true) => pure []
  | `(dslTerm| false) => pure []
  | `(dslTerm| $x:ident) => pure (
      -- `x.f`/`a.b.c...` dot-access sugar (see `elabDotChain`): only the *base*
      -- receiver is a real free identifier -- every other segment is a call head,
      -- excluded the same way `f(args)`'s own `$_f` is above. `dotChainBase`
      -- recurses to the root, not just one level (2026-08-27, generalizing the
      -- original single-dot fix the same way `elabDotChain` itself was).
      match x.getId with
      | .str pre _ =>
        if pre == .anonymous then
          (if x.getId == `now || bound.contains x.getId then [] else [x.getId])
        else
          let base := dotChainBase x.getId
          (if bound.contains base then [] else [base])
      | _ => [])
  | `(dslTerm| $_n:num) => pure []
  | `(dslTerm| $_f:ident($args,*)) => do
    args.getElems.foldlM (fun acc a => return acc ++ (← freeIdentsInTerm bound a)) []
  | `(dslTerm| I[[ $d:dslTerm :: $_f:ident $[, $tau:dslTerm]? ]]) => do
    let s1 ← freeIdentsInTerm bound d
    match tau with
    | some t => return s1 ++ (← freeIdentsInTerm bound t)
    | none => return s1
  | `(dslTerm| timed $e:dslTerm at $tau:dslTerm) => do
    return (← freeIdentsInTerm bound e) ++ (← freeIdentsInTerm bound tau)
  | `(dslTerm| shifted $e:dslTerm by $n:dslTerm) => do
    return (← freeIdentsInTerm bound e) ++ (← freeIdentsInTerm bound n)
  | `(dslTerm| $a:dslTerm + $b:dslTerm) => return (← freeIdentsInTerm bound a) ++ (← freeIdentsInTerm bound b)
  | `(dslTerm| $a:dslTerm - $b:dslTerm) => return (← freeIdentsInTerm bound a) ++ (← freeIdentsInTerm bound b)
  | `(dslTerm| $a:dslTerm * $b:dslTerm) => return (← freeIdentsInTerm bound a) ++ (← freeIdentsInTerm bound b)
  | `(dslTerm| $a:dslTerm / $b:dslTerm) => return (← freeIdentsInTerm bound a) ++ (← freeIdentsInTerm bound b)
  | `(dslTerm| -$a:dslTerm) => freeIdentsInTerm bound a
  | `(dslTerm| ($a:dslTerm)) => freeIdentsInTerm bound a
  | `(dslTerm| numberof $xs,* ~ $_ty $[in $r:dslRange]? that $body:dslWff) => do
    let bound' := bound ++ xs.getElems.toList.map (·.getId)
    let s1 ← match r with | some rr => freeIdentsInRange bound' rr | none => pure []
    return s1 ++ (← freeIdentsInWff bound' body)
  | `(dslTerm| productof $xs,* ~ $_ty $[in $r:dslRange]? that $body:dslTerm) => do
    let bound' := bound ++ xs.getElems.toList.map (·.getId)
    let s1 ← match r with | some rr => freeIdentsInRange bound' rr | none => pure []
    return s1 ++ (← freeIdentsInTerm bound' body)
  | `(dslTerm| sumof $xs,* ~ $_ty $[in $r:dslRange]? that $body:dslTerm) => do
    let bound' := bound ++ xs.getElems.toList.map (·.getId)
    let s1 ← match r with | some rr => freeIdentsInRange bound' rr | none => pure []
    return s1 ++ (← freeIdentsInTerm bound' body)
  | _ => pure []

/-- Free identifiers in a `dslRange` (interval bounds, or a bare `dslWff` guard). -/
partial def freeIdentsInRange (bound : List Name) : TSyntax `dslRange → MacroM (List Name)
  | `(dslRange| $a:dslTerm .. $b:dslTerm) => return (← freeIdentsInTerm bound a) ++ (← freeIdentsInTerm bound b)
  | `(dslRange| $a:dslTerm ,, $b:dslTerm) => return (← freeIdentsInTerm bound a) ++ (← freeIdentsInTerm bound b)
  | `(dslRange| $a:dslTerm ,. $b:dslTerm) => return (← freeIdentsInTerm bound a) ++ (← freeIdentsInTerm bound b)
  | `(dslRange| $a:dslTerm ., $b:dslTerm) => return (← freeIdentsInTerm bound a) ++ (← freeIdentsInTerm bound b)
  | `(dslRange| $φ:dslWff) => freeIdentsInWff bound φ
  | _ => pure []

/-- Free identifiers in a `dslWff`. The standalone bare-identifier case (`syntax
ident : dslWff`) always contributes nothing -- see this section's header note. -/
partial def freeIdentsInWff (bound : List Name) : TSyntax `dslWff → MacroM (List Name)
  | `(dslWff| $_x:ident) => pure []
  | `(dslWff| $_f:ident($args,*)) => do
    args.getElems.foldlM (fun acc a => return acc ++ (← freeIdentsInTerm bound a)) []
  | `(dslWff| $a:dslTerm $_r:ident $b:dslTerm) =>
    return (← freeIdentsInTerm bound a) ++ (← freeIdentsInTerm bound b)
  | `(dslWff| $a:dslTerm < $b:dslTerm) => return (← freeIdentsInTerm bound a) ++ (← freeIdentsInTerm bound b)
  | `(dslWff| $a:dslTerm <= $b:dslTerm) => return (← freeIdentsInTerm bound a) ++ (← freeIdentsInTerm bound b)
  | `(dslWff| $a:dslTerm > $b:dslTerm) => return (← freeIdentsInTerm bound a) ++ (← freeIdentsInTerm bound b)
  | `(dslWff| $a:dslTerm >= $b:dslTerm) => return (← freeIdentsInTerm bound a) ++ (← freeIdentsInTerm bound b)
  | `(dslWff| $a:dslTerm = $b:dslTerm ,, $c:dslTerm) =>
    return (← freeIdentsInTerm bound a) ++ (← freeIdentsInTerm bound b) ++ (← freeIdentsInTerm bound c)
  | `(dslWff| $a:dslTerm = $b:dslTerm) => return (← freeIdentsInTerm bound a) ++ (← freeIdentsInTerm bound b)
  | `(dslWff| $a:dslTerm <> $b:dslTerm) => return (← freeIdentsInTerm bound a) ++ (← freeIdentsInTerm bound b)
  | `(dslWff| $a:dslTerm in $b:dslTerm) => return (← freeIdentsInTerm bound a) ++ (← freeIdentsInTerm bound b)
  | `(dslWff| $φ:dslWff @ $tau:dslTerm) => return (← freeIdentsInWff bound φ) ++ (← freeIdentsInTerm bound tau)
  | `(dslWff| not $φ:dslWff) => freeIdentsInWff bound φ
  | `(dslWff| $φ:dslWff and $ψ:dslWff) => return (← freeIdentsInWff bound φ) ++ (← freeIdentsInWff bound ψ)
  | `(dslWff| $φ:dslWff or $ψ:dslWff) => return (← freeIdentsInWff bound φ) ++ (← freeIdentsInWff bound ψ)
  | `(dslWff| $φ:dslWff implies $ψ:dslWff) => return (← freeIdentsInWff bound φ) ++ (← freeIdentsInWff bound ψ)
  | `(dslWff| $φ:dslWff iff $ψ:dslWff) => return (← freeIdentsInWff bound φ) ++ (← freeIdentsInWff bound ψ)
  | `(dslWff| forall $ps,* $[in $r:dslRange]? are $body:dslWff) => do
    let bound' ← ps.getElems.foldlM (fun s p => return s ++ (← paramNames p)) bound
    let s1 ← match r with | some rr => freeIdentsInRange bound' rr | none => pure []
    return s1 ++ (← freeIdentsInWff bound' body)
  | `(dslWff| forall $ps1,* $[in $r1:dslRange]? forall $ps2,* $[in $r2:dslRange]? are $body:dslWff) => do
    let bound1 ← ps1.getElems.foldlM (fun s p => return s ++ (← paramNames p)) bound
    let bound2 ← ps2.getElems.foldlM (fun s p => return s ++ (← paramNames p)) bound1
    let s1 ← match r1 with | some rr => freeIdentsInRange bound1 rr | none => pure []
    let s2 ← match r2 with | some rr => freeIdentsInRange bound2 rr | none => pure []
    let s3 ← freeIdentsInWff bound2 body
    return s1 ++ s2 ++ s3
  | `(dslWff| exists $ps,* $[in $r:dslRange]? that $body:dslWff) => do
    let bound' ← ps.getElems.foldlM (fun s p => return s ++ (← paramNames p)) bound
    let s1 ← match r with | some rr => freeIdentsInRange bound' rr | none => pure []
    return s1 ++ (← freeIdentsInWff bound' body)
  | `(dslWff| ($φ:dslWff)) => freeIdentsInWff bound φ
  | _ => pure []

/-- The bound names a single `dslParam` group (`x,y,z~Class`) introduces. -/
partial def paramNames : TSyntax `dslParam → MacroM (List Name)
  | `(dslParam| $xs:ident,* ~ $_ty:dslType) => pure (xs.getElems.toList.map (·.getId))
  | _ => pure []

end

/-- Wraps `acc` in an *untyped* `fun` binder for a scope-visible identifier found by
`freeIdentsInTerm`/`freeIdentsInWff` above -- no type ascription, since this file has
no way to know the identifier's real KerML feature type; Lean's own elaborator infers
it from how the identifier is used inside `acc` (unification against whatever
`SFS.lean` function/relation it's passed to). -/
def mkAutoFun (id : Name) (acc : TSyntax `term) : MacroM (TSyntax `term) := do
  `(fun $(mkIdent id) => $acc)

/-- `<<Name : params sep body>>` → a curried Lean term over `params`: a `Prop`-valued
function for a `:`-separated `dslWff` body, an ordinary value-valued function for a
`:=`-separated `dslTerm` body, or (for the named-result form) a `Prop`-valued relation
between `params` and an explicit trailing `result` parameter. -/
def elabDslAssert : TSyntax `dslAssert → MacroM (TSyntax `term)
  | `(dslAssert| << $_name:ident : $params,* := $t:dslTerm >>) => do
    let paramGroups ← params.getElems.mapM elabDslParam
    let binders := paramGroups.foldl (· ++ ·) #[]
    let headerNames := binders.toList.map (·.1.getId)
    let withAuto ← (← freeIdentsInTerm headerNames t).eraseDups.foldrM mkAutoFun (← elabDslTerm t)
    binders.foldrM (fun (b : TSyntax `ident × TSyntax `term) (acc : TSyntax `term) =>
      `(fun ($(b.1) : $(b.2)) => $acc)) withAuto
  | `(dslAssert| << $_name:ident : $params,* $_sep:dslSep $body:dslBody >>) => do
    let paramGroups ← params.getElems.mapM elabDslParam
    let binders := paramGroups.foldl (· ++ ·) #[]
    let headerNames := binders.toList.map (·.1.getId)
    let mkFun (b : TSyntax `ident × TSyntax `term) (acc : TSyntax `term) : MacroM (TSyntax `term) :=
      `(fun ($(b.1) : $(b.2)) => $acc)
    match body with
    | `(dslBody| $φ:dslWff) => do
      let withAuto ← (← freeIdentsInWff headerNames φ).eraseDups.foldrM mkAutoFun (← elabDslWff φ)
      binders.foldrM mkFun withAuto
    | `(dslBody| $t:dslTerm) => do
      let withAuto ← (← freeIdentsInTerm headerNames t).eraseDups.foldrM mkAutoFun (← elabDslTerm t)
      binders.foldrM mkFun withAuto
    | `(dslBody| result ~ $rty:dslType | $φ:dslWff) => do
      let rty' ← elabDslType rty
      let inner ← `(fun ($resultIdent : $rty') => $(← elabDslWff φ))
      let withAuto ← (← freeIdentsInWff (headerNames ++ [`result]) φ).eraseDups.foldrM mkAutoFun inner
      binders.foldrM mkFun withAuto
    | _ => Macro.throwUnsupported
  | `(dslAssert| << $body:dslBody >>) => do
    match body with
    | `(dslBody| $φ:dslWff) => do
      (← freeIdentsInWff [] φ).eraseDups.foldrM mkAutoFun (← elabDslWff φ)
    | `(dslBody| $t:dslTerm) => do
      (← freeIdentsInTerm [] t).eraseDups.foldrM mkAutoFun (← elabDslTerm t)
    | `(dslBody| result ~ $rty:dslType | $φ:dslWff) => do
      let rty' ← elabDslType rty
      let inner ← `(fun ($resultIdent : $rty') => $(← elabDslWff φ))
      (← freeIdentsInWff [`result] φ).eraseDups.foldrM mkAutoFun inner
    | _ => Macro.throwUnsupported
  | _ => Macro.throwUnsupported

/-! ## `domain%` and smoke tests

`domain% <<...>>` elaborates the enclosed `@Assert` formula string into a real term,
via `elabDslAssert`. The `#check`s below are real: each is an actual `SFS.lean` term,
type-checked by Lean, not just a parse-only stub. -/

elab "domain% " a:dslAssert : term => do
  let stx ← Elab.liftMacroM (elabDslAssert a)
  Elab.Term.elabTerm stx none

-- SFS.mm/Mereology.kerml `PAR`. `x~Occurrence` (not `x~Class`) since 2026-08-21 --
-- Mereology.kerml's own real params were changed from `Class` to `Occurrence` in
-- the KerML source, and `SFS.lean`'s `PartOf` etc. followed the same day.
#check domain% << PAR : : forall x~Occurrence are not PartOf(x,x) >>

-- Mereology.kerml `PTR`.
#check domain% << PTR : : forall x,y,z~Occurrence are
  ( (PartOf(x,y) and PartOf(y,z)) implies PartOf(x,z) ) >>

-- Mereology.kerml `PartOverlap`.
#check domain% << PartOverlap : x~Occurrence, y~Occurrence :
  exists z~Occurrence that ( PartOf(z,x) and PartOf(z,y) ) >>

-- Mereology.kerml `PartUnderlap`.
#check domain% << PartUnderlap : x~Occurrence, y~Occurrence :
  exists z~Occurrence that ( PartOf(x,z) and PartOf(y,z) ) >>

-- Mereology.kerml `ImproperPart`.
#check domain% << ImproperPart : x~Occurrence, y~Occurrence : PartOf(x,y) or x=y >>

-- Mereology.kerml `PartDisjoint`.
#check domain% << PartDisjoint : x~Occurrence, y~Occurrence : not PartOverlap(x,y) >>

-- Mereology.kerml `PCH`.
#check domain% << PCH : : forall x,y~Occurrence are
  ( (x=y or PartOf(x,y) or PartOf(y,x) or PartDisjoint(x,y))
    and not (PartOf(x,y) and PartOf(y,x)) ) >>

-- Domain.kerml `next`: this formula text still elaborates fine on its own (a
-- plain Prop, independent of whatever `next` happens to mean), but no longer
-- equals `SFS.lean`'s own `next` (2026-08-26: redefined from "no `Time` value
-- strictly between" -- provably vacuous on dense `ℝ`, see the retired
-- `next_dense` -- to "consecutive shared ticks," via the new `finitePartition`
-- axiom). The formula text below is the OLD reading; expressing the new
-- tick-adjacency reading would need real new DSL grammar (an `isTick`/`ticks`
-- primitive), not attempted here -- same "documented gap" treatment as
-- `PartOf`'s own `xPy` placeholder, `Location`'s missing `L` alias, etc.
-- Updating `Domain.kerml`'s own `@Assert` text to match is a separate,
-- KerML-source-level follow-up, also not attempted here.
#check domain% <<next : tau1~Instant, tau2~Instant : (tau1 < tau2 and
  not exists tau~Instant that (tau1 < tau and tau < tau2) )  >>

-- Domain.kerml `Get`, exercising `I[[d::f,tau]]` → `Get d f tau`.
#check domain% <<Get : d~Occurrence, f~Anything, tau~Instant := I[[d::f,tau]] >>

example : domain% <<Get : d~Occurrence, f~Anything, tau~Instant := I[[d::f,tau]] >> = Get := rfl

-- Domain.kerml `GetChangeToTrue`, exercising `I[[...]]`'s *predicate* reading (new):
-- a bare `I[[d::e,now]]` as the left operand of `and`, and `not I[[d::e,t]]` --
-- both `GetP`, a genuine `Prop`, not `Get`'s `Set Item`.
#check domain% <<GetChangeToTrue : d~Occurrence, e~BooleanEvaluation, tau~Instant :
  (I[[d::e,now]] and forall t~Instant in tau ., now are not I[[d::e,t]] )
    implies b = true >>

-- Regions.kerml `NOINTP`.
#check domain% << NOINTP : : forall r1,r2~Region are
  RegionOverlap(r1,r2) implies (RegionContainment(r1,r2) or RegionContainment(r2,r1)) >>

-- Domain.kerml `SetNow`: `v` is a scope-visible identifier, not declared in this
-- formula's own header (`d~Occurrence, f~Anything` only) -- per `CLAUDE.md`'s
-- convention, presumably the `in`/`out` feature of the surrounding `.kerml`
-- operation whose value is being set. Auto-bound by `freeIdentsInWff`/`mkAutoFun`
-- above; its type (`Set Item`) is inferred from unifying against `Get`'s own result
-- type, not declared anywhere in this formula string. `v~Anything` was tried in the
-- header directly (2026-08-21) and rejected: `Anything` maps to `KerML.Root.Element`
-- (correct for `f`, a genuine feature reference), but `v` needs `Set Item` (matching
-- `Get`'s own return type) -- a real type conflict, not fixable by picking a
-- different name for the same clash. Elaborates to *exactly* `SFS.lean`'s own new
-- `SetNow` (2026-08-21) -- not a coincidence, `SetNow`'s own definition is this
-- formula's elaborated content, verbatim.
#check domain% <<SetNow : d~Occurrence, f~Anything : I[[d::f,now]] = v >>

example : domain% <<SetNow : d~Occurrence, f~Anything : I[[d::f,now]] = v >> = SetNow := rfl

-- Domain.kerml `GetChange`: `v` is scope-visible (the surrounding behavior's own
-- `out feature v`), same auto-binding as `SetNow`'s `v` above. Elaborates to exactly
-- `SFS.lean`'s own new `GetChange` (2026-08-21).
#check domain% <<GetChange : d~Occurrence, f~Anything, tau~Instant : (I[[d::f,tau]] <> I[[d::f,now]]
  and forall t~Instant in tau ., now are I[[d::f,t]] = I[[d::f,tau]]) implies v = I[[d::f,now]] >>

example : domain% <<GetChange : d~Occurrence, f~Anything, tau~Instant : (I[[d::f,tau]] <> I[[d::f,now]]
  and forall t~Instant in tau ., now are I[[d::f,t]] = I[[d::f,tau]]) implies v = I[[d::f,now]] >> = GetChange := rfl

-- Domain.kerml `GetBooleanChange`: `b` is scope-visible (the surrounding behavior's
-- own `out feature b`), same auto-binding pattern. Elaborates to exactly `SFS.lean`'s
-- own new `GetBooleanChange` (2026-08-21) -- itself defined as `GetChange d e tau b`,
-- mirroring `GetBooleanChange :> GetChange`'s real KerML specialization.
#check domain% <<GetBooleanChange : d~Occurrence, e~BooleanEvaluation, tau~Instant : (I[[d::e,tau]] <> I[[d::e,now]]
  and forall t~Instant in tau ., now are I[[d::e,t]] = I[[d::e,tau]]) implies b = I[[d::e,now]] >>

example : domain% <<GetBooleanChange : d~Occurrence, e~BooleanEvaluation, tau~Instant : (I[[d::e,tau]] <> I[[d::e,now]]
  and forall t~Instant in tau ., now are I[[d::e,t]] = I[[d::e,tau]]) implies b = I[[d::e,now]] >> = GetBooleanChange := rfl

-- Performances.kerml's own `<< during(self, thisPerformance) >>` (anonymous form, no
-- header at all): both `self` and `thisPerformance` are scope-visible (KerML's
-- implicit self-reference and a redefinable feature of `Performance`), auto-bound
-- here with their types inferred from `SFS.lean`'s real `during : Occurrence →
-- Occurrence → Prop`.
#check domain% << during(self, thisPerformance) >>

-- Allen.kerml's own real `@Assert` formulas, verbatim. `death(x)`/`death(y)`
-- special-case to `SFS.effectiveEnd x`/`SFS.effectiveEnd y` (`elabDslTerm`'s
-- matching case above), a plain `Time` -- so `<`/`=`/`and`/`or` here go through
-- the ordinary total instances, same as everywhere else in this file. Each
-- `example ... := rfl` below confirms the elaborated form is *exactly* `SFS.lean`'s
-- own `precedes`/`meets`/`overlaps`/`during`/`nonoverlaps`, not merely something
-- that happens to type-check. `nearlyMeets`'s own `next(death(x), birth(y))` call
-- needs no special handling at all now (`next : Time → Time → Prop` applies
-- directly) -- its `#check`/`example` live further down, after `coincident`.
#check domain% <<precedes : x~Occurrence, y~Occurrence : death(x) < birth(y) >>

example : domain% <<precedes : x~Occurrence, y~Occurrence : death(x) < birth(y) >> = precedes := rfl

#check domain% <<meets : x~Occurrence, y~Occurrence : death(x) = birth(y) >>

example : domain% <<meets : x~Occurrence, y~Occurrence : death(x) = birth(y) >> = meets := rfl

#check domain% <<overlaps : x~Occurrence, y~Occurrence : birth(y) <  death(x)>>

example : domain% <<overlaps : x~Occurrence, y~Occurrence : birth(y) <  death(x)>> = overlaps := rfl

#check domain% <<during : x~Occurrence, y~Occurrence : birth(y) <= birth(x) and death(x) <= death(y)>>

example : domain% <<during : x~Occurrence, y~Occurrence : birth(y) <= birth(x) and death(x) <= death(y)>> = during := rfl

#check domain% <<nonoverlaps : x~Occurrence, y~Occurrence : birth(y) > death(x) or birth(x) > death(y)>>

example : domain% <<nonoverlaps : x~Occurrence, y~Occurrence : birth(y) > death(x) or birth(x) > death(y)>> = nonoverlaps := rfl

-- `starts`/`finishes`/`coincident`, now that dot-access (`x.openLeft`/`y.openRight`)
-- has real grammar support, and `SFS.lean`'s own definitions (2026-08-26) gained
-- the `openLeft`/`openRight` conjunct they had been missing: `example ... := rfl`
-- below confirms exact agreement, same as `precedes`/`meets`/`overlaps`/`during`/
-- `nonoverlaps` above.
#check domain% <<starts : x~Occurrence, y~Occurrence :
  birth(x) = birth(y) and death(y) < death(x)
  and x.openLeft = y.openLeft >>

example : domain% <<starts : x~Occurrence, y~Occurrence :
  birth(x) = birth(y) and death(y) < death(x)
  and x.openLeft = y.openLeft >> = starts := rfl

#check domain% <<finishes : x~Occurrence, y~Occurrence :
  birth(y) < birth(x) and death(x) = death(y)
  and x.openRight = y.openRight >>

example : domain% <<finishes : x~Occurrence, y~Occurrence :
  birth(y) < birth(x) and death(x) = death(y)
  and x.openRight = y.openRight >> = finishes := rfl

#check domain% <<coincident : x~Occurrence, y~Occurrence :
  birth(y) = birth(x) and death(x) = death(y) and x.openLeft = y.openLeft
  and x.openRight = y.openRight >>

example : domain% <<coincident : x~Occurrence, y~Occurrence :
  birth(y) = birth(x) and death(x) = death(y) and x.openLeft = y.openLeft
  and x.openRight = y.openRight >> = coincident := rfl

-- `nearlyMeets`, the last Allen predicate: `next(death(x), birth(y))` is now a
-- plain `next` call on two `Time`s (`death(x)` → `effectiveEnd x`), no lifting
-- needed.
#check domain% <<nearlyMeets : x~Occurrence, y~Occurrence :
  (birth(y) = death(x) and (x.openRight or y.openLeft)) or next(death(x), birth(y))>>

example : domain% <<nearlyMeets : x~Occurrence, y~Occurrence :
  (birth(y) = death(x) and (x.openRight or y.openLeft)) or next(death(x), birth(y))>>
    = nearlyMeets := rfl

/- Formulas deliberately *not* included as live `#check`s here, because they are
expected to fail to elaborate, honestly, rather than being forced:
- `Mereology.kerml`'s `PartOf`'s own body, `<< PartOf : x~Occurrence, y~Occurrence :
  xPy >>` --
  `xPy` is a standalone bare-`dslWff`-identifier (informal "x P y" shorthand, not a
  real scope-visible name), which `freeIdentsInWff`'s own bare-identifier case
  deliberately never auto-binds (see that section's header note) -- still fails with
  "unknown identifier xPy", honestly, exactly as before.
- `<< Location : o~Occurrence := result~Region | o L result >>` -- `SFS.lean` now has
  a real, function-valued `Location : Occurrence → Region` (2026-08-21, at direct
  request, matching this formula's own functional declaration exactly), but the
  infix `L` notation this formula's own *body* uses (`o L result`) was deliberately
  not wired up alongside it -- no `L` alias added, disregarded on purpose per that
  same request, not a leftover gap. `SFS.lean` genuinely has no `L`; this one still
  fails, honestly, for that specific and only that reason (confirmed via a real
  build). `LFU`/`LIN`/`EXPNS`/`APAR` (`Regions.kerml`), by contrast, call
  `Location(x)` as a one-argument function -- now that `Location` really is one,
  all four elaborate live (see `Kernel.lean`'s own `#check`s), no longer excluded
  here. -/

end SFS.Assert
