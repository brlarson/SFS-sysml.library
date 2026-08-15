/-
Lean 4 syntax categories for the `@Assert`/`@Invariant` formula language used throughout
this repository (`f="<<Name : params : body>>"`, or `Assertion::Assert` in `.kerml`
files / `Assert::Assert` in `.sysml` files -- see the repo's `CLAUDE.md`).

## Scope

This file declares `syntax` categories and productions -- a real, working *parser* for
the `<< ... >>` formula strings -- so they can be written and parsed as genuine Lean
syntax (see the `domain%` smoke tests at the end). It does **not** elaborate them into
`Prop`/`SFS.lean` terms: there is no semantic connection yet between a parsed
`dslAssert` and `SFS.lean`'s `TProp`/`interp`/`atP`/etc. Wiring that up (interpreting
`forall x~Occurrence are φ` as an actual `∀ x : Occurrence, ...`, `I[[d::f,tau]]` as an
actual `interpAt`/`atC` application, and so on) is a separate, considerably larger
undertaking -- this file is the grammar layer only, the same way `SFS.mm`'s `wtp`/`wat`/
`wts` etc. are bare *syntax* axioms, with meaning given separately by `df-bl.before`/
`df-bl.at`/`df-bl.ts`.

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
import Lean

namespace SFS.DSL

/-! ## Types (Appendix J `\S`J.4: `TYPE` is the `Type`/`Classifier` elements of the
design) -/

declare_syntax_cat dslType

/-- A type name: `Occurrence`, `Instant`, `Region`, `Class`, `Anything`, .... -/
syntax ident : dslType

/-! ## Terms (Appendix J `\S`J.4: `PT`, built from `CON`/`VAR`/`FUNC` application) -/

declare_syntax_cat dslTerm

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

declare_syntax_cat dslRange

/-- `τ1 .. τ2` (closed), matching `df-bl.dd`. -/
syntax dslTerm " .. " dslTerm : dslRange
/-- `τ1 ,, τ2` (open), matching `df-bl.cc`. -/
syntax dslTerm " ,, " dslTerm : dslRange
/-- `τ1 ,. τ2` (open-left), matching `df-bl.cd`. -/
syntax dslTerm " ,. " dslTerm : dslRange
/-- `τ1 ., τ2` (open-right), matching `df-bl.dc`. -/
syntax dslTerm " ., " dslTerm : dslRange

/-! ## Well-formed formulas (Appendix J `df-bl0wff`/`df-blwff`) -/

declare_syntax_cat dslWff

/-- A bare proposition symbol (SFS.mm/`PROP`), e.g. `PartOf`'s own body `xPy`: an
otherwise-unparsed atomic formula name standing for some primitive relation. -/
syntax ident : dslWff

/-- N-ary predicate application, `P(t1,...,tn)`, e.g. `PartOf(x,y)`. -/
syntax ident "(" dslTerm,* ")" : dslWff

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
`\S`3.13.1's own EBNF does not mark it so. -/
syntax "forall " ident,+ "~" dslType (" in " dslRange)? " are " dslWff : dslWff

/-- Bounded/unbounded existential quantification, `df-bl.ex`'s ASCII form. -/
syntax "exists " ident,+ "~" dslType (" in " dslRange)? " that " dslWff : dslWff

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
declare_syntax_cat dslParam
syntax ident,+ "~" dslType : dslParam

/-- The `: | :=` separator between the parameter list and the body: `:` for a
predicate/relation body (a `dslWff`), `:=` for a value-defining body (a `dslTerm`, or
the named-result form below). -/
declare_syntax_cat dslSep
syntax ":" : dslSep
syntax ":=" : dslSep

/-- A body is a formula, a term, or a named-result binding: `result~Type | wff`, e.g.
`Location`'s `result~Region | o L result`, or `RegionSurface`'s
`result~Surface | forall p~Point are ...`. -/
declare_syntax_cat dslBody
syntax dslWff : dslBody
syntax dslTerm : dslBody
syntax "result" "~" dslType " | " dslWff : dslBody

declare_syntax_cat dslAssert

/-- `<<Name : params sep body>>`, e.g. `<<next : tau1~Instant, tau2~Instant : (tau1 <
tau2 and not exists tau~Instant that (tau1 < tau and tau < tau2))>>`, or
`<<Get : d~Occurrence, f~Anything, tau~Instant := I[[d::f,tau]]>>`. -/
syntax "<<" ident ":" dslParam,* dslSep dslBody ">>" : dslAssert

/-! ## Smoke tests

`domain%` embeds a `dslAssert` in ordinary Lean term syntax purely so it can be written
in `#check`-able position -- confirming the grammar above actually *parses* real
`@Assert` formula strings, not asserting anything about their meaning (the elaborator
below just expands to `()` unconditionally; see the file-level scope note). -/

macro "domain% " _a:dslAssert : term => `(())

-- SFS.mm/Mereology.kerml `PAR`.
#check domain% << PAR : : forall x~Class are not PartOf(x,x) >>

-- Mereology.kerml `PTR`.
#check domain% << PTR : : forall x,y,z~Class are
  ( (PartOf(x,y) and PartOf(y,z)) implies PartOf(x,z) ) >>

-- Mereology.kerml `PartOverlap`.
#check domain% << PartOverlap : x~Class, y~Class :
  exists z~Class that ( PartOf(z,x) and PartOf(z,y) ) >>

-- Mereology.kerml `ImproperPart`.
#check domain% << ImproperPart : x~Class, y~Class : PartOf(x,y) or x=y >>

-- Domain.kerml `next`.
#check domain% <<next : tau1~Instant, tau2~Instant : (tau1 < tau2 and
  not exists tau~Instant that (tau1 < tau and tau < tau2) )  >>

-- Domain.kerml `Get`.
#check domain% <<Get : d~Occurrence, f~Anything, tau~Instant := I[[d::f,tau]] >>

-- Domain.kerml `SetNow`.
#check domain% <<SetNow : d~Occurrence, f~Anything : I[[d::f,now]] = v >>

-- Regions.kerml `Location` (named-result form).
#check domain% << Location : o~Occurrence := result~Region | o L result >>

-- Regions.kerml `NOINTP`.
#check domain% << NOINTP : : forall r1,r2~Region are
  RegionOverlap(r1,r2) implies (RegionContainment(r1,r2) or RegionContainment(r2,r1)) >>

-- Domain.kerml `SetNow`-family time-range quantifier (`in Range`, `<>`).
#check domain% <<X : d~Occurrence, f~Anything, tau~Instant, v~Anything :
  (I[[d::f,tau]] <> I[[d::f,now]] and forall t~Instant in tau ., now are
    I[[d::f,t]] = I[[d::f,tau]]) implies v = I[[d::f,now]] >>

end SFS.DSL
