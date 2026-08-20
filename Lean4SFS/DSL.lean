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
uses infix `L`, but `SFS.lean` only has `Location : Part → Region → Prop`, a different
argument type than this formula's `Occurrence` subject) is *expected* to fail with an
honest "unknown identifier"/type-mismatch error, not silently coerced into something
that type-checks but doesn't mean what the formula says.

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

namespace SFS.DSL

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
`result~Surface | forall p~Point are ...`. -/
syntax dslWff : dslBody
syntax dslTerm : dslBody
syntax "result" "~" dslType " | " dslWff : dslBody

/-- `<<Name : params sep body>>`, e.g. `<<next : tau1~Instant, tau2~Instant : (tau1 <
tau2 and not exists tau~Instant that (tau1 < tau and tau < tau2))>>`, or
`<<Get : d~Occurrence, f~Anything, tau~Instant := I[[d::f,tau]]>>`. -/
syntax "<<" ident ":" dslParam,* dslSep dslBody ">>" : dslAssert

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
comparison, from the exact same generated `DSLLt.lt` call. -/
class DSLLt (α : Type _) where lt : α → α → Prop
class DSLLe (α : Type _) where le : α → α → Prop

instance : DSLLt Time := ⟨fun t1 t2 => t1.val ≺ t2.val⟩
instance : DSLLe Time := ⟨fun t1 t2 => t1.val ≼ t2.val⟩
instance : DSLLt ℝ := ⟨(· < ·)⟩
instance : DSLLe ℝ := ⟨(· ≤ ·)⟩

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

/-- `dslType` → the `SFS.lean` type it names. Recognized DSL type names are mapped to
their `SFS.lean` counterpart; anything else is passed through as a bare identifier
(so it resolves if some matching Lean declaration happens to exist, and fails with an
honest "unknown identifier" otherwise, rather than being silently mismapped). -/
def elabDslType : TSyntax `dslType → MacroM (TSyntax `term)
  | `(dslType| $t:ident) => do
    match t.getId.toString with
    | "Instant" => `(Time)
    | "Occurrence" => `(Occurrence)
    | "Region" => `(Region)
    | "Point" => `(Point)
    | "Surface" => `(Surface)
    | "Class" => `(Part)
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

mutual

/-- `dslTerm` → the `SFS.lean`/Lean term it denotes. -/
partial def elabDslTerm : TSyntax `dslTerm → MacroM (TSyntax `term)
  | `(dslTerm| result) => `($resultIdent)
  | `(dslTerm| $x:ident) => do
    -- `now` is special-cased: every real formula uses it in a `Time`-typed position
    -- (`I[[d::f,now]]`'s `tau` argument, or a range's upper bound alongside another
    -- `Time`-typed term like `tau`), never as bare `ℝ`, but `SFS.now : ℝ` is the raw
    -- unrestricted constant. `dl_nowt : now ∈ TIME` closes the gap, matching how
    -- `Time := ↥TIME` is threaded everywhere else `SFS.lean` needs an in-range instant.
    if x.getId == `now then `((⟨now, dl_nowt⟩ : Time)) else `($x)
  | `(dslTerm| $n:num) => `($n)
  | `(dslTerm| $f:ident($args,*)) => do
    let args ← args.getElems.mapM elabDslTerm
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
  | `(dslRange| $φ:dslWff) => elabDslWff φ
  | _ => Macro.throwUnsupported

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
    | `(dslRange| $φ:dslWff) => do
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
    | `(dslRange| $φ:dslWff) => do
      let inner ← `($(← elabDslWff φ) ∧ $base)
      binders.foldrM (fun b acc => `(Exists (fun ($(b.1) : $(b.2)) => $acc))) inner
    | _ => binders.foldrM (fun b acc => do
        let g ← elabDslRangeGuard (← `($(b.1))) rr
        `(Exists (fun ($(b.1) : $(b.2)) => $g ∧ $acc))) base
  | none => binders.foldrM (fun b acc => `(Exists (fun ($(b.1) : $(b.2)) => $acc))) base

/-- `dslWff` → the `Prop` it denotes. -/
partial def elabDslWff : TSyntax `dslWff → MacroM (TSyntax `term)
  | `(dslWff| $x:ident) => `($x)
  | `(dslWff| $f:ident($args,*)) => do
    let args ← args.getElems.mapM elabDslTerm
    `($f $args*)
  | `(dslWff| $a:dslTerm $r:ident $b:dslTerm) => do
    `($r $(← elabDslTerm a) $(← elabDslTerm b))
  | `(dslWff| $a:dslTerm < $b:dslTerm) => do `(DSLLt.lt $(← elabDslTerm a) $(← elabDslTerm b))
  | `(dslWff| $a:dslTerm <= $b:dslTerm) => do `(DSLLe.le $(← elabDslTerm a) $(← elabDslTerm b))
  | `(dslWff| $a:dslTerm > $b:dslTerm) => do `(DSLLt.lt $(← elabDslTerm b) $(← elabDslTerm a))
  | `(dslWff| $a:dslTerm >= $b:dslTerm) => do `(DSLLe.le $(← elabDslTerm b) $(← elabDslTerm a))
  | `(dslWff| $a:dslTerm = $b:dslTerm) => do `($(← elabDslTerm a) = $(← elabDslTerm b))
  | `(dslWff| $a:dslTerm <> $b:dslTerm) => do `($(← elabDslTerm a) ≠ $(← elabDslTerm b))
  | `(dslWff| $a:dslTerm in $b:dslTerm) => do
    `(DSLMem.mem $(← elabDslTerm a) $(← elabDslTerm b))
  | `(dslWff| $φ:dslWff @ $tau:dslTerm) => do
    `(interpAt $(← elabDslWff φ) $(← elabDslTerm tau))
  | `(dslWff| not $φ:dslWff) => do `(¬ $(← elabDslWff φ))
  | `(dslWff| $φ:dslWff and $ψ:dslWff) => do `($(← elabDslWff φ) ∧ $(← elabDslWff ψ))
  | `(dslWff| $φ:dslWff or $ψ:dslWff) => do `($(← elabDslWff φ) ∨ $(← elabDslWff ψ))
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

/-- `<<Name : params sep body>>` → a curried Lean term over `params`: a `Prop`-valued
function for a `:`-separated `dslWff` body, an ordinary value-valued function for a
`:=`-separated `dslTerm` body, or (for the named-result form) a `Prop`-valued relation
between `params` and an explicit trailing `result` parameter. -/
def elabDslAssert : TSyntax `dslAssert → MacroM (TSyntax `term)
  | `(dslAssert| << $_name:ident : $params,* $_sep:dslSep $body:dslBody >>) => do
    let paramGroups ← params.getElems.mapM elabDslParam
    let binders := paramGroups.foldl (· ++ ·) #[]
    let mkFun (b : TSyntax `ident × TSyntax `term) (acc : TSyntax `term) : MacroM (TSyntax `term) :=
      `(fun ($(b.1) : $(b.2)) => $acc)
    match body with
    | `(dslBody| $φ:dslWff) => do binders.foldrM mkFun (← elabDslWff φ)
    | `(dslBody| $t:dslTerm) => do binders.foldrM mkFun (← elabDslTerm t)
    | `(dslBody| result ~ $rty:dslType | $φ:dslWff) => do
      let rty' ← elabDslType rty
      let inner ← `(fun ($resultIdent : $rty') => $(← elabDslWff φ))
      binders.foldrM mkFun inner
    | _ => Macro.throwUnsupported
  | `(dslAssert| << $body:dslBody >>) => do
    match body with
    | `(dslBody| $φ:dslWff) => elabDslWff φ
    | `(dslBody| $t:dslTerm) => elabDslTerm t
    | `(dslBody| result ~ $rty:dslType | $φ:dslWff) => do
      let rty' ← elabDslType rty
      `(fun ($resultIdent : $rty') => $(← elabDslWff φ))
    | _ => Macro.throwUnsupported
  | _ => Macro.throwUnsupported

/-! ## `domain%` and smoke tests

`domain% <<...>>` elaborates the enclosed `@Assert` formula string into a real term,
via `elabDslAssert`. The `#check`s below are real: each is an actual `SFS.lean` term,
type-checked by Lean, not just a parse-only stub. -/

elab "domain% " a:dslAssert : term => do
  let stx ← Elab.liftMacroM (elabDslAssert a)
  Elab.Term.elabTerm stx none

-- SFS.mm/Mereology.kerml `PAR`.
#check domain% << PAR : : forall x~Class are not PartOf(x,x) >>

-- Mereology.kerml `PTR`.
#check domain% << PTR : : forall x,y,z~Class are
  ( (PartOf(x,y) and PartOf(y,z)) implies PartOf(x,z) ) >>

-- Mereology.kerml `PartOverlap`.
#check domain% << PartOverlap : x~Class, y~Class :
  exists z~Class that ( PartOf(z,x) and PartOf(z,y) ) >>

-- Mereology.kerml `PartUnderlap`.
#check domain% << PartUnderlap : x~Class, y~Class :
  exists z~Class that ( PartOf(x,z) and PartOf(y,z) ) >>

-- Mereology.kerml `ImproperPart`.
#check domain% << ImproperPart : x~Class, y~Class : PartOf(x,y) or x=y >>

-- Mereology.kerml `PartDisjoint`.
#check domain% << PartDisjoint : x~Class, y~Class : not PartOverlap(x,y) >>

-- Mereology.kerml `PCH`.
#check domain% << PCH : : forall x,y~Class are
  ( (x=y or PartOf(x,y) or PartOf(y,x) or PartDisjoint(x,y))
    and not (PartOf(x,y) and PartOf(y,x)) ) >>

-- Domain.kerml `next`: elaborates to *exactly* SFS.lean's own `next` definition.
#check domain% <<next : tau1~Instant, tau2~Instant : (tau1 < tau2 and
  not exists tau~Instant that (tau1 < tau and tau < tau2) )  >>

example : domain% <<next : tau1~Instant, tau2~Instant : (tau1 < tau2 and
  not exists tau~Instant that (tau1 < tau and tau < tau2) )  >> = next := rfl

-- Domain.kerml `Get`, exercising `I[[d::f,tau]]` → `Get d f tau`.
#check domain% <<Get : d~Occurrence, f~Anything, tau~Instant := I[[d::f,tau]] >>

example : domain% <<Get : d~Occurrence, f~Anything, tau~Instant := I[[d::f,tau]] >> = Get := rfl

-- Regions.kerml `NOINTP`.
#check domain% << NOINTP : : forall r1,r2~Region are
  RegionOverlap(r1,r2) implies (RegionContainment(r1,r2) or RegionContainment(r2,r1)) >>

/- Formulas deliberately *not* included as live `#check`s here, because they are
expected to fail to elaborate, honestly, rather than being forced:
- `<<SetNow : d~Occurrence, f~Anything : I[[d::f,now]] = v >>` -- `v` is never bound
  by this formula's own header (per `CLAUDE.md`'s convention, it's presumably an
  `in`/`out` feature of the surrounding `.kerml` operation, visible in that lexical
  scope but not this standalone one) -- fails with "unknown identifier v".
- `<< Location : o~Occurrence := result~Region | o L result >>` -- `SFS.lean` has no
  `L`; its own `Location : Part → Region → Prop` also has a different (and
  incompatible) subject type (`Part`, not `Occurrence`) from this formula's `o`, so
  even adding an `L := Location` alias would not make this one type-check. This is a
  genuine mismatch between the DSL formula and `SFS.lean`'s Mereology/Region
  axiomatization, not a `DSL.lean` bug -- surfaced here, not hidden. -/

end SFS.DSL
