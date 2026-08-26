/-
Lean 4 formalization of `~/git3/set.mm/SFS.mm` (the Metamath database backing this
repository's `@Assert`/`@Invariant` "Supplemental Formal Semantics" content).

## Scope (project decision, three-part)

- **Skipped entirely**: SFS.mm lines 1-970 ("BLESS Helpers" -- wff-lists, class-lists,
  and multiterm-arithmetic machinery that exists only because Metamath has no native
  n-ary/variadic connectives or associative operators). None of it carries independent
  mathematical content; Lean's `∧`/`∨`/`+`/`*` are already n-ary, associative, and
  commutative where appropriate, so nothing here needs restating.
- **Real definitions** (SFS.mm lines 973-2726, "BLESS Logic" plus the `@`/`^.`
  operators): `TIME`, temporal precedence, and the interpretation-function (`𝐈⟦·⟧`)
  machinery are given concrete Lean definitions, chosen so the ~200 "distribute `@`
  (or `^.`) over connective/operator X" theorems in SFS.mm become provable one-liners
  (frequently `rfl`) instead of a wall of separately-axiomatized near-duplicates.
- **Axioms** (SFS.mm lines 2726-3150): Mereology, Region/Location, Allen's Intervals,
  `next` and its supporting lemmas, and the KerML element-kind enumeration are stated
  as `axiom`s mirroring SFS.mm's own `$c`/`$a` structure ("everything as axioms,
  first pass").

## A finding surfaced while grounding the semantics

SFS.mm's untimed interpretation `boldI[[ph]]` is described in prose as "tautologies"
i.e. things true at every instant -- the standard modal *necessity* (`□`) reading,
which this file implements literally as `interp φ := ∀ t, φ t`. Under that reading
(the only one consistent with SFS.mm's own commentary), `□` distributes over `∧`/`∀`
both ways (`df-bl.an`, `df-bl.al` are sound) but, as with any normal modal box
operator, only *one direction* is valid for `∨`/`¬`/`→`/`↔`/`∃` in general (classic
K-axiom asymmetry). SFS.mm nonetheless states `df-bl.or`, `df-bl.not`, `df-bl.im`,
`df-bl.bi`, and (via `bl.dfrex2`) `bl.ex` as full, unconditional biconditionals. Below,
each of these is witnessed by a two-instant counterexample showing the "extra"
direction is false in general, so only the sound direction is proved -- this file does
not axiomatize the unsound direction. This is the same character of issue as the
pre-existing `df-exc`/`df-flmc` class-typed-existential bug documented in
`reference_metamath_sfs_toolchain.md`: a `$a` axiom that doesn't survive contact with
a concrete model. Not in scope to fix in SFS.mm itself here.

## Second-pass audit (2026-08-13)

A full cross-check of every SFS.mm `$a`/`$p` label in the in-scope range against this
file found: the entire "Distribute `^.` over logic/arithmetic/relations/quantifiers"
section (SFS.mm lines ~2896-3070ish) had been silently skipped (the first pass read up
through `bl.tscomci` and stopped); `@`/`^.` distributing over `=`/`<`/`≤`/`∀`/`∃`; the
`@`/value congruence axioms `df-bl.atbi`/`df-bl.ateqc`; `ax-bl.bi`/`ax-bl.eq`;
`bl.ty`/`bl.tyt`; `df-bl.ralt`/`df-bl.rext`; `bl.3an`; untimed value arithmetic for
`-`/`×`/`÷`/negation (only `+` had been done); and `df-pch` in Mereology. All are now
present below, each tagged with the SFS.mm label(s) it covers. Left deliberately out of
scope, same reasoning as the first pass: anything depending on the skipped multiterm-
list plumbing (`bl.atad`/`atmul`/`tsani`/`tsori`/`tsadi`/`tsmuli` and friends), and `@`/
`^.` distributing over `sum_`/`prod_`/`if` (`df-bl.atsum`/`atprod`/`atqq` and their
`^.` analogues, plus the `bl.tsoi` side-condition helper) -- these would need real
`Finset.sum`/conditional-expression integration, not just unfolding a `def`.

## Third pass: restrict everything to `TIME` (2026-08-15)

`TVal`/`TProp` (and everything built on them: `interp`/`interpAt`/`interpValAt`/
`interpVal`, and every downstream section) now range over `Time := ↥TIME`, not all of
`Instant = ℝ`. Only the handful of theorems genuinely *about* temporal precedence
itself (`tprec`/`tprecEq`/`dl_before`/`dl_beforeeq`/`tprec_congr1`/
`tprec_congr2`/`dl_nowt`, just above) stay on bare `Instant` -- matching SFS.mm's own
`wtp`/`wtpe`, which are similarly unrestricted syntax axioms whose *meaning* is only
pinned to `<`/`≤` within `TIME` (`df-bl.before`/`df-bl.beforeeq`). This is more
faithful to SFS.mm than the first two passes: nearly every SFS.mm theorem in the
BLESS-Logic/`@`/`^.` sections carries an explicit `t0 ∈ TIME` (or `t1,t2 ∈ TIME`,
...) hypothesis, which the first two passes only sometimes threaded through; making
`Time` a genuine type forces it everywhere at once, and those hypotheses simply
vanish (they're now automatic from `t0 : Time`'s own type).

The one place this has real mathematical teeth, not just bookkeeping: `^.`
(`shiftP`/`shiftC` in the earlier passes) shifts an instant by a real offset, which
can leave `TIME` even when the starting instant doesn't -- exactly why SFS.mm's own
`df-bl.ts`/`bl.tsi` carry a `(t0+D×A) ∈ TIME` side condition. Under the second pass's
design (`TVal`/`TProp` as functions on all of `ℝ`) this was silently ignorable. Under
this pass it cannot be: `shiftP`/`shiftC` are replaced by `shiftEval`/`shiftEvalC`,
which take the landing-in-`TIME` proof as an explicit argument rather than pretending
the shift is always defined. (A "default to `False`/unshifted-value when out of
`TIME`" alternative was tried first and rejected: it makes `shiftP` total again, but
breaks negation -- `shiftP(¬ₜφ)`'s default is `False` while `¬ₜ(shiftP φ)`'s default
is `¬False = True`, so no fixed junk value keeps both sides consistent. The
hypothesis-carrying design sidesteps this because it never evaluates outside `TIME`
at all.)
-/
import Mathlib
import Root
import Core

namespace SFS

/-! ## Time (SFS.mm lines 1002-1099) -/

/-- SFS.mm `cnow`/`df-bl.nowrr`: a fixed nonnegative real, the end of recorded time.
Class-based (2026-08-26, at direct request, porting the `Lifetimes` recipe here
too): `now` needs no guard the way `birth`/`death`/`timeof` did -- "does a
nonnegative real exist" is trivially true (witnessed by `0` itself) -- so this is
the simplest instance of the pattern: no new axiom, `Classical.choice` alone
(already one of Lean's own standard axioms) is enough to build a real model. -/
class Now where
  now : ℝ
  now_nonneg : 0 ≤ now

export Now (now now_nonneg)

/-- The consistency certificate, exactly as trivial as the class itself: `0` is a
genuine witness, `Classical.choose` just picks *some* nonnegative real (opaquely,
matching what `axiom now : ℝ` asserted directly before) rather than committing to
`0` specifically -- fixing `now := 0` here would be wrong, not just inelegant:
`TIME := Set.Icc 0 now` would collapse to the single point `{0}`, degenerating
everything built on `Time` (density arguments, `next`'s distinctness, ...). -/
noncomputable instance nowModel : Now :=
  ⟨Classical.choose (⟨0, le_refl (0:ℝ)⟩ : ∃ x : ℝ, 0 ≤ x),
    Classical.choose_spec (⟨0, le_refl (0:ℝ)⟩ : ∃ x : ℝ, 0 ≤ x)⟩

abbrev Instant := ℝ

/-- SFS.mm `ctime`/`df-bl.time`. -/
def TIME : Set Instant := Set.Icc 0 now

theorem TIME_nonempty : (0 : Instant) ∈ TIME := ⟨le_refl 0, now_nonneg⟩

-- SFS.mm `ctops` (`$c tops $.`/`class tops`) is declared but never used anywhere
-- else in SFS.mm -- no defining axiom, no citations -- so there is nothing to
-- translate.
-- SFS.mm `bl.rt`/`bl.ert`/`bl.etir`/`bl.etial0`/`bl.etiamn` (`TIME ⊆ ℝ`/`ℝ*`, and
-- every time is a real `≥ 0`) are all vacuous here: `Instant := ℝ` already, and
-- `TIME := Set.Icc 0 now` is a `Set ℝ` by construction, so `TIME ⊆ ℝ` isn't a fact
-- to separately state or prove, and "every `t1 ∈ TIME` is real and `≥ 0`" is just
-- `Set.mem_Icc`, unfolded automatically wherever a `t1 ∈ TIME` hypothesis is used.

/-- SFS.mm `wtp`/`df-bl.before`: temporal precedence, defined directly as `<` on all
of `ℝ` rather than only characterized on `TIME`. Consequently its Leibniz congruence
(`bl.tpeq1`/`bl.tpeq2` in SFS.mm -- needed there as *extra axioms* because `wtp` is a
bare primitive, not built via the generic `wbr` relation mechanism `breq1`/`breq2`
apply to) is just `congrArg`, free of charge; see [[reference_metamath_sfs_toolchain]]
for why that mattered in the Metamath development. -/
def tprec (t1 t2 : Instant) : Prop := t1 < t2
infix:50 " ≺ " => tprec

/-- SFS.mm `df-bl.before`. -/
theorem dl_before {t1 t2 : Instant} (_ : t1 ∈ TIME) (_ : t2 ∈ TIME) :
    (t1 ≺ t2) ↔ t1 < t2 := Iff.rfl

/-- SFS.mm `bl.tpeq1`, free (`congrArg (· ≺ _)`), not an axiom here. -/
theorem tprec_congr1 {A B : Instant} (h : A = B) (C : Instant) : (A ≺ C) ↔ (B ≺ C) := h ▸ Iff.rfl

/-- SFS.mm `bl.tpeq2`, free. -/
theorem tprec_congr2 {A B : Instant} (h : A = B) (C : Instant) : (C ≺ A) ↔ (C ≺ B) := h ▸ Iff.rfl

/-- SFS.mm `wtpe`/`df-bl.beforeeq`. -/
def tprecEq (t1 t2 : Instant) : Prop := t1 ≤ t2
infix:50 " ≼ " => tprecEq

theorem dl_beforeeq {t1 t2 : Instant} (_ : t1 ∈ TIME) (_ : t2 ∈ TIME) :
    (t1 ≼ t2) ↔ (t1 < t2 ∨ t1 = t2) := le_iff_lt_or_eq

/-- SFS.mm `bl.nowt`: `now` is itself a time. -/
theorem dl_nowt : now ∈ TIME := ⟨now_nonneg, le_refl now⟩

/-- The actual domain temporal values/predicates are evaluated over -- an instant
*together with* a proof it's in `TIME`, not a bare `Instant`. Everything from here
down (`TVal`/`TProp`/`interp`/`interpAt`/`interpValAt`/`interpVal` and everything
built on them) uses this, not `Instant`; see the file-level "Third pass" doc comment
for why. -/
abbrev Time := ↥TIME

/-- A BLESS-logic temporal value: what SFS.mm's `A` denotes when read as varying
with the world/instant -- one plain value per instant. -/
abbrev TVal (α : Type*) := Time → α

/-- A BLESS-logic temporal predicate: SFS.mm's `ph`, read as a function from instants
to truth values rather than an opaque schema letter, so every "interpretation
distributes over connective X" fact below is an ordinary fact about pointwise-defined
functions. -/
abbrev TProp := Time → Prop

/-- SFS.mm `wboldit`, i.e. `boldI [[ ph , t_0 ]]`: interpretation at a specific
instant. Definitionally just application, since `TProp` already *is* "value at each
instant". -/
def interpAt (φ : TProp) (t0 : Time) : Prop := φ t0

/-- SFS.mm `wboldi`, i.e. `boldI [[ ph ]]`: untimed/"always" interpretation -- `φ`
holds at every instant (the modal `□`, matching SFS.mm's own gloss "Tautologies are
expressed as `boldI [[ ph ]]`"). -/
def interp (φ : TProp) : Prop := ∀ t, φ t

/-- SFS.mm `ax-bl.taut`. Provable here, not axiomatized: a plain (non-temporal)
Metamath wff `ph`, embedded as a `TProp` via the constant function, is trivially
`interp`-true once any instant exists (`TIME_nonempty` guarantees one). -/
theorem ax_dl_taut {p : Prop} : p → interp (fun (_ : Time) => p) := fun h _ => h

/-- SFS.mm `bl.ty` (SFS.mm's own `$= ?`, unproven there). Same constant-embedding
argument as `ax_dl_taut`: a plain set-membership fact `A ∈ B` is trivially
`interp`-true once embedded. -/
theorem dl_ty {α} {A : α} {B : Set α} : A ∈ B → interp (fun (_ : Time) => A ∈ B) :=
  ax_dl_taut

/-- SFS.mm `ax-bl.models`. The `t_0 ∈ TIME` hypothesis SFS.mm carries is no longer
stated separately: it's now automatic from `t0`'s type. -/
theorem ax_dl_models {φ : TProp} {t0 : Time} : interp φ → interpAt φ t0 := fun h => h t0

/-- SFS.mm `bl.tyt` (SFS.mm's own `$= ?`, unproven there). Timed counterpart of
`bl.ty`, same argument, now trivially both directions since `interpAt` is literal
evaluation. -/
theorem dl_tyt {α} {A : α} {B : Set α} {t0 : Time} : A ∈ B ↔ interpAt (fun _ => A ∈ B) t0 := Iff.rfl

/-- SFS.mm `ax-bl.bi`. Read with `ph`/`ps` as ordinary (non-temporally-varying) Props,
embedded the same constant way as `ax_dl_taut`/`bl.ty` -- the only reading under which
the axiom's antecedent `(ph <-> ps)`, a bare untimed biconditional with no `boldI`
wrapper at all, is well-formed independent of any instant. Under that reading it is
`Iff.rfl`, not a fresh axiom. SFS.mm's `t_1,t_2 ∈ TIME` hypotheses are likewise
automatic now, from `t1 t2 : Time`. -/
theorem ax_dl_bi {p q : Prop} {t1 t2 : Time} (_ : t1 = t2) :
    (p ↔ q) ↔ (interpAt (fun (_ : Time) => p) t1 ↔ interpAt (fun (_ : Time) => q) t2) := Iff.rfl

/-- SFS.mm `wboldic`/`wboldict`: untimed and timed interpretation of *values*.
Timed is again literal evaluation; untimed is anchored at instant `0` (`0 ∈ TIME` via
`TIME_nonempty`). Unlike predicate-`interp` this is not a `∀`-aggregation, so it
commutes with every pointwise-defined value operator unconditionally (see
`interpVal_add` etc. below) -- SFS.mm's `ax-bl.modelsc` (only meaningful when `A`
is actually constant) is not restated as an axiom since it is not needed to make any
of the value-side distribution facts below provable. -/
def interpValAt {α} (A : TVal α) (t0 : Time) : α := A t0
def interpVal {α} (A : TVal α) : α := A ⟨0, TIME_nonempty⟩

/-- SFS.mm `ax-bl.eq`, the value-level counterpart of `ax_dl_bi` above, same reading
(`A`/`B` as ordinary, non-temporally-varying values). -/
theorem ax_dl_eq {α} {A B : α} {t1 t2 : Time} (_ : t1 = t2) :
    (A = B) ↔ (interpValAt (fun (_ : Time) => A) t1 = interpValAt (fun (_ : Time) => B) t2) :=
  Iff.rfl

/-! ### Temporal interval quantification (SFS.mm lines 1100-1174)

`bl.alldd`/`bl.allcd`/`bl.allcc`/`bl.alldc` just unfold what membership in a
closed/open-left/open/open-right interval means arithmetically -- already exactly
Mathlib's `Set.mem_Icc`/`Set.mem_Ioc`/`Set.mem_Ioo`/`Set.mem_Ico`. SFS.mm carries
`t1,t2 ∈ TIME` as an explicit `$e` hypothesis on this family (unlike `bl.exdd` and
friends below, which have none) -- `t1 t2 : Time` here makes that automatic instead.
`bl.exdd`/`bl.excc`/`bl.excd`/`bl.exdc` are the same generic classical fact
(`∃x,Px ↔ ¬∀x,¬Px`) instantiated at each of the four intervals in turn -- proved
once below (`exists_iff_not_forall_not`), not four times; their `t1,t2` stay plain
`Instant`s, matching SFS.mm's own (hypothesis-free) statement of them -- only the
bound `x` is forced to `Time`, by `φ`'s type. -/

theorem dl_alldd (t1 t2 : Time) (φ : TProp) :
    (∀ x : Time, x.val ∈ Set.Icc t1.val t2.val ∧ φ x) ↔
      (∀ x : Time, t1.val ≤ x.val ∧ x.val ≤ t2.val ∧ φ x) := by
  simp [Set.mem_Icc, and_assoc]

theorem dl_allcd (t1 t2 : Time) (φ : TProp) :
    (∀ x : Time, x.val ∈ Set.Ioc t1.val t2.val ∧ φ x) ↔
      (∀ x : Time, t1.val < x.val ∧ x.val ≤ t2.val ∧ φ x) := by
  simp [Set.mem_Ioc, and_assoc]

theorem dl_allcc (t1 t2 : Time) (φ : TProp) :
    (∀ x : Time, x.val ∈ Set.Ioo t1.val t2.val ∧ φ x) ↔
      (∀ x : Time, t1.val < x.val ∧ x.val < t2.val ∧ φ x) := by
  simp [Set.mem_Ioo, and_assoc]

theorem dl_alldc (t1 t2 : Time) (φ : TProp) :
    (∀ x : Time, x.val ∈ Set.Ico t1.val t2.val ∧ φ x) ↔
      (∀ x : Time, t1.val ≤ x.val ∧ x.val < t2.val ∧ φ x) := by
  simp [Set.mem_Ico, and_assoc]

/-- The common shape behind `bl.exdd`/`bl.excc`/`bl.excd`/`bl.exdc`: plain classical
De Morgan, nothing interval-specific about it. -/
theorem exists_iff_not_forall_not {D : Type*} (P : D → Prop) : (∃ x, P x) ↔ ¬ ∀ x, ¬ P x := by
  constructor
  · rintro ⟨x, hx⟩ h; exact h x hx
  · intro h; by_contra hne; exact h (fun x hx => hne ⟨x, hx⟩)

/-- SFS.mm `bl.exdd`. -/
theorem dl_exdd (t1 t2 : Instant) (φ : TProp) :
    (∃ x : Time, x.val ∈ Set.Icc t1 t2 ∧ φ x) ↔ ¬ ∀ x : Time, ¬ (x.val ∈ Set.Icc t1 t2 ∧ φ x) :=
  exists_iff_not_forall_not _
/-- SFS.mm `bl.excc`. -/
theorem dl_excc (t1 t2 : Instant) (φ : TProp) :
    (∃ x : Time, x.val ∈ Set.Ioo t1 t2 ∧ φ x) ↔ ¬ ∀ x : Time, ¬ (x.val ∈ Set.Ioo t1 t2 ∧ φ x) :=
  exists_iff_not_forall_not _
/-- SFS.mm `bl.excd`. -/
theorem dl_excd (t1 t2 : Instant) (φ : TProp) :
    (∃ x : Time, x.val ∈ Set.Ioc t1 t2 ∧ φ x) ↔ ¬ ∀ x : Time, ¬ (x.val ∈ Set.Ioc t1 t2 ∧ φ x) :=
  exists_iff_not_forall_not _
/-- SFS.mm `bl.exdc`. -/
theorem dl_exdc (t1 t2 : Instant) (φ : TProp) :
    (∃ x : Time, x.val ∈ Set.Ico t1 t2 ∧ φ x) ↔ ¬ ∀ x : Time, ¬ (x.val ∈ Set.Ico t1 t2 ∧ φ x) :=
  exists_iff_not_forall_not _

/-! ### Logic operators, pointwise (SFS.mm's `boldI`-distribution sections) -/

def tand (φ ψ : TProp) : TProp := fun t => φ t ∧ ψ t
def tor (φ ψ : TProp) : TProp := fun t => φ t ∨ ψ t
def tnot (φ : TProp) : TProp := fun t => ¬ φ t
def timp (φ ψ : TProp) : TProp := fun t => φ t → ψ t
def tiff (φ ψ : TProp) : TProp := fun t => φ t ↔ ψ t

infixr:70 " ∧ₜ " => tand
infixr:65 " ∨ₜ " => tor
prefix:75 "¬ₜ" => tnot
infixr:60 " →ₜ " => timp
infix:55 " ↔ₜ " => tiff

/- SFS.mm `df-bl.ant` (timed conjunction) and every other *timed* two- or three-place
connective distribution law (`df-bl.ort`, `df-bl.imt`, `df-bl.bit`, `df-bl.nott`,
`bl.an3t`, `bl.or3t`, ...): all `rfl`, since `interpAt` is literal evaluation and
every `t_` combinator above is defined pointwise. One proof stands for the whole
family regardless of arity or nesting. -/
-- (illustrative `example`s below cannot themselves carry a `/-- -/` docstring)
example (φ ψ : TProp) (t0 : Time) : interpAt (φ ∧ₜ ψ) t0 ↔ (interpAt φ t0 ∧ interpAt ψ t0) := Iff.rfl
example (φ ψ : TProp) (t0 : Time) : interpAt (φ ∨ₜ ψ) t0 ↔ (interpAt φ t0 ∨ interpAt ψ t0) := Iff.rfl
example (φ ψ : TProp) (t0 : Time) : interpAt (φ →ₜ ψ) t0 ↔ (interpAt φ t0 → interpAt ψ t0) := Iff.rfl
example (φ ψ : TProp) (t0 : Time) : interpAt (φ ↔ₜ ψ) t0 ↔ (interpAt φ t0 ↔ interpAt ψ t0) := Iff.rfl
example (φ : TProp) (t0 : Time) : interpAt (¬ₜφ) t0 ↔ ¬ interpAt φ t0 := Iff.rfl

/-- SFS.mm `df-bl.an` (untimed). Sound: `□` distributes over `∧` (`forall_and`). -/
theorem dl_an (φ ψ : TProp) : interp (φ ∧ₜ ψ) ↔ (interp φ ∧ interp ψ) := forall_and

/-- SFS.mm `df-bl.al` (untimed universal quantification exportation). Sound: swapping
two `∀`s is always valid. -/
theorem dl_al {D : Type*} (φ : D → TProp) : interp (fun t => ∀ x, φ x t) ↔ ∀ x, interp (φ x) :=
  forall_comm

/-- SFS.mm `bl.3an` (untimed, three terms): a direct corollary of `dl_an`
(applied to the flat right-associated shape), not a fresh axiom. -/
theorem dl_3an (φ ψ ch : TProp) : interp (φ ∧ₜ ψ ∧ₜ ch) ↔ (interp φ ∧ interp ψ ∧ interp ch) := by
  simp only [interp, tand, forall_and]

/-- SFS.mm `bl.dfrex2` (untimed). Unlike `bl.ex` below, this one *is* sound: it
compares `interp` of two *pointwise*-equivalent `TProp`s (`∃x∈A,φxt` and
`¬∀x∈A,¬φxt` are classically equivalent for every fixed `t`, no swap of `∀t` past
`∃x` involved), so it is a congruence fact, not a K-axiom-asymmetry one. -/
theorem dl_dfrex2 {D : Type*} (A : Set D) (φ : D → TProp) :
    interp (fun t => ∃ x ∈ A, φ x t) ↔ interp (fun t => ¬ ∀ x ∈ A, ¬ φ x t) := by
  apply forall_congr'
  intro t
  constructor
  · rintro ⟨x, hx, hφ⟩ h
    exact h x hx hφ
  · intro h
    by_contra hne
    push Not at hne
    exact h hne

/-- SFS.mm `df-bl.or` (untimed), sound direction only. The converse
(`interp (φ ∨ₜ ψ) → interp φ ∨ interp ψ`) is **false** in general: witnessed on
`TIME` as soon as it has two distinct instants `t1 ≠ t2` by `φ := (· = t1)`,
`ψ := (· = t2)` -- `φ ∨ₜ ψ` holds at every instant in `{t1, t2}` but neither disjunct
holds at both, so `interp (φ ∨ₜ ψ)` restricted to `{t1,t2}` would hold while
`interp φ ∨ interp ψ` fails. SFS.mm's `df-bl.or` states the full (unsound)
biconditional; not restated here. See the file-level doc comment. -/
theorem dl_or_sound (φ ψ : TProp) : (interp φ ∨ interp ψ) → interp (φ ∨ₜ ψ) := by
  rintro (h | h) t
  · exact Or.inl (h t)
  · exact Or.inr (h t)

/-- SFS.mm `bl.3or` (untimed, three terms), sound direction only -- same asymmetry
as `df-bl.or`, one level deeper. -/
theorem dl_3or_sound (φ ψ ch : TProp) : (interp φ ∨ interp ψ ∨ interp ch) → interp (φ ∨ₜ ψ ∨ₜ ch) := by
  rintro (h | h | h) t
  · exact Or.inl (h t)
  · exact Or.inr (Or.inl (h t))
  · exact Or.inr (Or.inr (h t))

-- Witness that the converse of `df-bl.or` (untimed) is not derivable. `interp` now
-- quantifies over all of `Time` (i.e. `TIME = [0,now]`), so the earlier `ℝ`-wide
-- witness (`φ := 0≤·`, `ψ := ·<0`) no longer even makes sense as a counterexample --
-- every `t : Time` already satisfies `0 ≤ t.val`. Split `TIME` at its own midpoint
-- instead: `φ := (·.val ≤ now/2)`, `ψ := (now/2 < ·.val)`. `∀t,φt∨ψt` is trichotomy,
-- unconditionally true. Disproving `∀t,φt` needs `TIME` to have more than one point
-- (`0 < now`) -- if `now = 0`, `TIME = {0}` and `φ` would be a tautology too, so this
-- hypothesis is genuinely necessary here, not just convenient.
example (_hgt : 0 < now) :
    interp ((fun t : Time => t.val ≤ now / 2) ∨ₜ (fun t : Time => now / 2 < t.val)) := by
  intro t
  by_cases h : t.val ≤ now / 2
  · exact Or.inl h
  · exact Or.inr (not_le.mp h)

example (hgt : 0 < now) : ¬ interp (fun t : Time => t.val ≤ now / 2) :=
  fun h => absurd (h ⟨now, dl_nowt⟩) (not_le.mpr (by linarith))

example : ¬ interp (fun t : Time => now / 2 < t.val) :=
  fun h => absurd (h ⟨0, TIME_nonempty⟩) (not_lt.mpr (by linarith [now_nonneg]))

/-- SFS.mm `df-bl.not` (untimed), sound direction only: `interp(¬ₜφ) → ¬interp φ`
is the valid direction (if `φ` fails at every instant it certainly doesn't hold at
every instant). The converse is **false** in general, same K-axiom-asymmetry
character as `df-bl.or`: reusing `φ := (·.val ≤ now/2)` from above, `interp(¬ₜφ)` is
false (`φ` holds, doesn't fail, at `0`) regardless of `interp φ`. Not restated as a
full axiom; see the file-level doc comment. -/
theorem dl_not_sound (φ : TProp) : interp (¬ₜφ) → ¬ interp φ :=
  fun h hall => h ⟨0, TIME_nonempty⟩ (hall ⟨0, TIME_nonempty⟩)

example : ¬ interp (¬ₜ(fun t : Time => t.val ≤ now / 2)) :=
  fun h => h ⟨0, TIME_nonempty⟩ (by linarith [now_nonneg])

/-- SFS.mm `df-bl.im` (untimed), sound direction only (the modal K-axiom shape). The
converse fails by the same shape as `df-bl.or` (take `ψ := fun _ => False` so
`φ →ₜ ψ` becomes `¬ₜφ`, reducing to the `¬` case). Not restated as an axiom; see the
file-level doc comment. -/
theorem dl_im_sound (φ ψ : TProp) : interp (φ →ₜ ψ) → (interp φ → interp ψ) :=
  fun h hφ t => h t (hφ t)

/-- SFS.mm `df-bl.bi` (untimed), sound direction only, same K-axiom-asymmetry
character as `df-bl.or`/`df-bl.not`/`df-bl.im`. Unlike those three, the file-level doc
comment above named this one as unsound too but never supplied its own witness -- added
here (and the counterexample just below) to actually establish that claim before it's
used to justify weakening `SFS.mm`'s `df-bl.bi`. -/
theorem dl_bi_sound (φ ψ : TProp) : interp (φ ↔ₜ ψ) → (interp φ ↔ interp ψ) :=
  fun h => ⟨fun hφ t => (h t).mp (hφ t), fun hψ t => (h t).mpr (hψ t)⟩

-- Witness that the converse of `df-bl.bi` (untimed) is not derivable: `φ := (·=0)`,
-- `ψ := (·=now)` are both non-tautological on `TIME` (each fails at the other's unique
-- point, given `0 < now`), so `interp φ ↔ interp ψ` holds vacuously (`False ↔ False`),
-- while `φ ↔ₜ ψ` itself fails at `0` (`φ` holds there, `ψ` doesn't), so
-- `interp (φ ↔ₜ ψ)` is false -- `(True) → (False)`, the implication fails.
example (hgt : 0 < now) :
    (interp (fun t : Time => t.val = (0 : Instant)) ↔ interp (fun t : Time => t.val = now)) ∧
    ¬ interp ((fun t : Time => t.val = (0 : Instant)) ↔ₜ (fun t : Time => t.val = now)) := by
  have hφ0 : ¬ interp (fun t : Time => t.val = (0 : Instant)) :=
    fun h => absurd (h ⟨now, dl_nowt⟩) (by linarith)
  have hψ0 : ¬ interp (fun t : Time => t.val = now) :=
    fun h => absurd (h ⟨0, TIME_nonempty⟩) (by linarith)
  refine ⟨⟨fun h => (hφ0 h).elim, fun h => (hψ0 h).elim⟩, fun h => ?_⟩
  have h0 := h ⟨0, TIME_nonempty⟩
  exact absurd (h0.mp rfl) (by intro he; linarith [he.symm])

/-- SFS.mm `bl.dfrex2`/`bl.ex` (untimed existential exportation), sound direction
only. The converse (`interp (fun t => ∃ x, φ x t) → ∃ x, interp (φ x)`) is the classic
invalid `∀∃`-to-`∃∀` swap: different instants may need different witnesses. Not
restated as an axiom; see the file-level doc comment. -/
theorem dl_ex_sound {D : Type*} (φ : D → TProp) :
    (∃ x, interp (φ x)) → interp (fun t => ∃ x, φ x t) :=
  fun ⟨x, hx⟩ t => ⟨x, hx t⟩

/-- SFS.mm `df-bl.ralt`, timed restricted universal quantification: `rfl`, same
reason every other timed fact is -- `interpAt` is literal evaluation. -/
theorem dl_ralt {D : Type*} (φ : D → TProp) (A : Set D) (t0 : Time) :
    interpAt (fun t => ∀ x ∈ A, φ x t) t0 ↔ ∀ x, x ∈ A → interpAt (φ x) t0 := Iff.rfl

/-- SFS.mm `df-bl.rext`, timed restricted existential quantification. -/
theorem dl_rext {D : Type*} (φ : D → TProp) (A : Set D) (t0 : Time) :
    interpAt (fun t => ∃ x ∈ A, φ x t) t0 ↔ ∃ x, x ∈ A ∧ interpAt (φ x) t0 := Iff.rfl

/-! ### Value-level operators (SFS.mm's arithmetic `boldI`-distribution sections) -/

/-- SFS.mm `df-bl.addt`/`df-bl.add`/`df-bl.subt`/`df-bl.sub`/`df-bl.mult`/`df-bl.mul`/
`df-bl.divt`/`df-bl.div`/`df-bl.umt`/`df-bl.um`: all `rfl`. `interpVal`/`interpValAt`
are point evaluation (at `0`, resp. `t0`) of ordinary Mathlib `Pi`-instance pointwise
arithmetic on `Instant → ℝ`, and point evaluation always commutes with pointwise
operators -- no constancy assumption needed, unlike the predicate case above. -/
example (A B : TVal ℝ) (t0 : Time) : interpValAt (A + B) t0 = interpValAt A t0 + interpValAt B t0 := rfl
example (A B : TVal ℝ) : interpVal (A + B) = interpVal A + interpVal B := rfl
example (A B : TVal ℝ) (t0 : Time) : interpValAt (A - B) t0 = interpValAt A t0 - interpValAt B t0 := rfl
example (A B : TVal ℝ) : interpVal (A - B) = interpVal A - interpVal B := rfl
example (A B : TVal ℝ) (t0 : Time) : interpValAt (A * B) t0 = interpValAt A t0 * interpValAt B t0 := rfl
example (A B : TVal ℝ) : interpVal (A * B) = interpVal A * interpVal B := rfl
example (A B : TVal ℝ) (t0 : Time) : interpValAt (A / B) t0 = interpValAt A t0 / interpValAt B t0 := rfl
example (A B : TVal ℝ) : interpVal (A / B) = interpVal A / interpVal B := rfl
example (A : TVal ℝ) (t0 : Time) : interpValAt (-A) t0 = -interpValAt A t0 := rfl
example (A : TVal ℝ) : interpVal (-A) = -interpVal A := rfl

/-- SFS.mm `df-bl.eq`/`df-bl.eqt`/`df-bl.lt`/`df-bl.ltt`/`df-bl.am`/`df-bl.amt`:
relations between temporal values, lifted pointwise the same way. -/
def teq (A B : TVal ℝ) : TProp := fun t => A t = B t
def tlt (A B : TVal ℝ) : TProp := fun t => A t < B t
def tle (A B : TVal ℝ) : TProp := fun t => A t ≤ B t

example (A B : TVal ℝ) (t0 : Time) : interpAt (teq A B) t0 ↔ interpValAt A t0 = interpValAt B t0 := Iff.rfl
example (A B : TVal ℝ) (t0 : Time) : interpAt (tlt A B) t0 ↔ interpValAt A t0 < interpValAt B t0 := Iff.rfl
example (A B : TVal ℝ) (t0 : Time) : interpAt (tle A B) t0 ↔ interpValAt A t0 ≤ interpValAt B t0 := Iff.rfl

/-- SFS.mm `bl.bitrit`: transitivity of timed `boldI`-biconditional -- literally
`Iff.trans`, not a fresh fact, since `interpAt` is just evaluation. -/
theorem dl_bitrit {φ ψ ch : TProp} {t0 : Time} (h1 : interpAt (φ ↔ₜ ψ) t0)
    (h2 : interpAt (ψ ↔ₜ ch) t0) : interpAt (φ ↔ₜ ch) t0 := h1.trans h2

/-! ## The `@` operator (SFS.mm lines 1560-2067) -/

/-- SFS.mm `wat`/`clat0`, i.e. `(ph @ t_0)`/`(A @ t_0)`: evaluate at `t0`, freezing
the result into a *constant* temporal predicate/value (so it can validly be `@`'d
again, matching `df-bl.at2`'s "double `@` is inconsequential"). Because the result is
constant, `@` distributing over any pointwise-defined connective or operator is `rfl`
-- this one construction subsumes SFS.mm's entire "Distribute Temporal Operator @"
section (`bl.atan2i`/`bl.atan3i`/`bl.atan3ri`/`bl.atan3li`/`bl.ator2i`/... and their
value/arithmetic analogues, ~100 theorems), for arbitrary composition depth, not just
the specific two- or three-term/left/right shapes SFS.mm had to spell out one by one. -/
def atP (φ : TProp) (t0 : Time) : TProp := fun _ => φ t0
def atC {α} (A : TVal α) (t0 : Time) : TVal α := fun _ => A t0

/-- SFS.mm `df-bl.at`. -/
theorem dl_at (φ : TProp) (t0 : Time) : interp (atP φ t0) ↔ interpAt φ t0 :=
  ⟨fun h => h t0, fun h _ => h⟩

/-- SFS.mm `df-bl.atc`. -/
theorem dl_atc {α} (A : TVal α) (t0 : Time) : interpVal (atC A t0) = interpValAt A t0 := rfl

/-- SFS.mm `df-bl.at2`: double `@` collapses to the first (outer) evaluation. -/
theorem dl_at2 (φ : TProp) (t1 t2 : Time) : interp (atP (atP φ t1) t2) ↔ interpAt φ t1 :=
  (dl_at (atP φ t1) t2).trans Iff.rfl

/-- SFS.mm `df-bl.at2c`. -/
theorem dl_at2c {α} (A : TVal α) (t1 t2 : Time) :
    interpVal (atC (atC A t1) t2) = interpValAt A t1 := rfl

/-- SFS.mm `bl.atintro`. SFS.mm's `t_0 ∈ TIME` hypothesis is automatic now. -/
theorem dl_atintro {φ : TProp} {t0 : Time} : interp φ → interp (atP φ t0) :=
  fun h _ => h t0

/-- General @-distributes-over-any-pointwise-binary-connective fact, SFS.mm
`bl.atan2i`/`bl.ator2i`/... in one shot. -/
theorem atP_binop (g : Prop → Prop → Prop) (φ ψ : TProp) (t0 : Time) :
    atP (fun t => g (φ t) (ψ t)) t0 = fun _ => g (φ t0) (ψ t0) := rfl

/-- SFS.mm `df-bl.atan2`/`bl.atan2i`. -/
theorem atP_and (φ ψ : TProp) (t0 : Time) : atP (φ ∧ₜ ψ) t0 = atP φ t0 ∧ₜ atP ψ t0 := rfl
/-- SFS.mm `df-bl.ator2`/`bl.ator2i`. -/
theorem atP_or (φ ψ : TProp) (t0 : Time) : atP (φ ∨ₜ ψ) t0 = atP φ t0 ∨ₜ atP ψ t0 := rfl
/-- SFS.mm `df-bl.atnot`/`bl.atnoti`. -/
theorem atP_not (φ : TProp) (t0 : Time) : atP (¬ₜφ) t0 = ¬ₜ(atP φ t0) := rfl
theorem atP_imp (φ ψ : TProp) (t0 : Time) : atP (φ →ₜ ψ) t0 = atP φ t0 →ₜ atP ψ t0 := rfl
/-- SFS.mm `df-bl.atbid`/`bl.atbidi`. -/
theorem atP_iff (φ ψ : TProp) (t0 : Time) : atP (φ ↔ₜ ψ) t0 = atP φ t0 ↔ₜ atP ψ t0 := rfl
/- Three-term, and any-nesting, conjunction/disjunction all fall out of `atP_and`/
`atP_or` for free (SFS.mm `bl.atan3i`/`bl.atan3ri`/`bl.atan3li`/`bl.ator3i`/
`bl.ator3ri`/`bl.ator3li`): e.g. `(φ ∧ₜ ψ) ∧ₜ ch` is already `fun t => (φ ∧ₜ ψ) t ∧ ch t`,
so `atP_and` applied twice covers it, no separate lemma needed. -/
example (φ ψ ch : TProp) (t0 : Time) :
    atP (φ ∧ₜ ψ ∧ₜ ch) t0 = atP φ t0 ∧ₜ atP ψ t0 ∧ₜ atP ch t0 := rfl

/-- SFS.mm `df-bl.atad2`/`bl.atad2i`. -/
theorem atC_add (A B : TVal ℝ) (t0 : Time) : atC (A + B) t0 = atC A t0 + atC B t0 := rfl
/-- SFS.mm `df-bl.atsub`/`bl.atsubi`. -/
theorem atC_sub (A B : TVal ℝ) (t0 : Time) : atC (A - B) t0 = atC A t0 - atC B t0 := rfl
/-- SFS.mm `df-bl.atmul2`/`bl.atmul2i`. -/
theorem atC_mul (A B : TVal ℝ) (t0 : Time) : atC (A * B) t0 = atC A t0 * atC B t0 := rfl
/-- SFS.mm `df-bl.atdiv`/`bl.atdivi`. -/
theorem atC_div (A B : TVal ℝ) (t0 : Time) : atC (A / B) t0 = atC A t0 / atC B t0 := rfl
/-- SFS.mm `df-bl.atum`/`bl.atumi`. -/
theorem atC_neg (A : TVal ℝ) (t0 : Time) : atC (-A) t0 = -atC A t0 := rfl

-- SFS.mm `bl.atad3`/`bl.atad3l`/`bl.atad`/`bl.atmul3`/`bl.atmul3l`/`bl.atmul` (the
-- 3-term and "generic list" `+(cl_1,cl_2)x`/`*(cl_1,cl_2)x` variants) depend on the
-- multiterm-arithmetic-list machinery from SFS.mm's skipped lines 1-970; out of
-- scope for the same reason those lines are. `atC_add`/`atC_mul` already give the
-- 2-term case, and the 3-term case is `atC_add`/`atC_mul` applied twice, same as
-- the `@`-over-conjunction 3-term case above.

/-- SFS.mm `df-bl.ateq`/`bl.ateq`. -/
theorem atP_teq (A B : TVal ℝ) (t0 : Time) : atP (teq A B) t0 = teq (atC A t0) (atC B t0) := rfl
/-- SFS.mm `df-bl.atlt`/`bl.atlti`. -/
theorem atP_tlt (A B : TVal ℝ) (t0 : Time) : atP (tlt A B) t0 = tlt (atC A t0) (atC B t0) := rfl
/-- SFS.mm `bl.atami`. -/
theorem atP_tle (A B : TVal ℝ) (t0 : Time) : atP (tle A B) t0 = tle (atC A t0) (atC B t0) := rfl

/-- SFS.mm `df-bl.atal`, `@` distributing over restricted universal quantification. -/
theorem atP_ralt {D : Type*} (φ : D → TProp) (A : Set D) (t0 : Time) :
    atP (fun t => ∀ x ∈ A, φ x t) t0 = fun t => ∀ x ∈ A, atP (φ x) t0 t := rfl

/-- SFS.mm `df-bl.atexi`, `@` distributing over restricted existential quantification. -/
theorem atP_rext {D : Type*} (φ : D → TProp) (A : Set D) (t0 : Time) :
    atP (fun t => ∃ x ∈ A, φ x t) t0 = fun t => ∃ x ∈ A, atP (φ x) t0 t := rfl

-- SFS.mm `df-bl.atsum`/`df-bl.atprod`/`df-bl.atqq` (`@` distributing over `sum_`/
-- `prod_`/conditional expressions) are out of scope: unlike every fact above, these
-- would need real `Finset.sum`/`if`-`then`-`else` integration, not just unfolding a
-- `def`, and are a different (and larger) undertaking from the rest of this section.

/-- SFS.mm `df-bl.atbi`: `@`-congruence for predicates. `ph`/`ps` read as pointwise-
equivalent `TProp`s (`interp (φ ↔ₜ ψ)`), the same convention as `ax_dl_bi`/`ax_dl_eq`
extended to genuinely temporal (not just constant-embedded) predicates -- this is
what "`(ph<->ps)`, no `boldI` wrapper, no time index" must mean for `ph`/`ps` that
*do* vary with time, since a bare `<->` between two `Instant → Prop`s doesn't
otherwise typecheck as a single `Prop`. SFS.mm's `bl.atbii` is the same fact with
its hypotheses spelled out as separate premises; not restated separately. -/
theorem dl_atbi {φ ψ : TProp} {t1 t2 : Time} (ht : t1 = t2) (hpq : interp (φ ↔ₜ ψ)) :
    interp (atP φ t1) ↔ interp (atP ψ t2) := by
  rw [dl_at, dl_at, ht]
  exact hpq t2

/-- SFS.mm `df-bl.ateqc`: `@`-congruence for values, literal substitution (`A = B`
and `t1 = t2` as actual equalities, unlike `dl_atbi`'s pointwise-iff reading,
since values genuinely can be compared by `=`). SFS.mm's `bl.ateqci` is the same
fact with hypotheses spelled out separately; not restated. -/
theorem dl_ateqc {α} {A B : TVal α} {t1 t2 : Time} (ht : t1 = t2) (hAB : A = B) :
    interpVal (atC A t1) = interpVal (atC B t2) := by subst ht; subst hAB; rfl

-- SFS.mm `bl.atintroc` and `df-bl.atrt` are not restated: `bl.atintroc` ("a constant
-- value's `@`-frozen value is still that constant") needs the same "`A` is actually
-- constant" side condition `ax-bl.modelsc` needed and wasn't restated for (see the
-- `interpVal`/`interpValAt` doc comment above) -- `atC A t0`'s value only matches
-- `interpVal A`'s *anchor-at-`0`* value when `A` doesn't vary, which isn't assumed
-- here. `df-bl.atrt` ("applying `@` retains type") is automatic in a typed setting:
-- if `A : TVal α` then `atC A t0 : TVal α` by construction, nothing to prove.

/-! ## The `^.` operator (SFS.mm lines 2067-2726)

`shiftP`/`shiftC` from earlier passes are gone. A shift by `D×n` can carry an instant
outside `TIME` even when the starting instant is inside it -- exactly why SFS.mm's own
`df-bl.ts`/`bl.tsi` carry a `(t0+D×A) ∈ TIME` side condition (`bl.tsi`'s fourth
hypothesis) that earlier passes here could silently ignore (`TVal`/`TProp` ranged over
all of `ℝ` then). Now that they range over `Time`, that hypothesis is unavoidable, so
`shiftEval`/`shiftEvalC` take it as an explicit argument rather than pretending the
shift is always defined; see the file-level "Third pass" doc comment for why a
"default when out of `TIME`" alternative doesn't work (it breaks negation). Every
theorem below is `rfl`/`Iff.rfl` all the same -- the hypothesis is threaded, not
discharged by a tactic. -/

/-- SFS.mm `wts`/`clats`: evaluate `φ`/`A` shifted by `n` whole multiples of step
size `D` from `t0`, given that lands back in `TIME`. `Prop`/value-valued (not
`TProp`/`TVal`-valued): tied to one specific `t0` together with its validity proof,
matching `df-bl.ts`'s own shape (`boldI[[(ph^.A),t0]] <-> boldI[[ph,(t0+D×A)]]`,
itself only characterized under this same side condition) rather than trying to keep
`^.` reusable as a free-standing operator the way `@` (`atP`/`atC`) is -- `@` needs no
such condition, since freezing at an already-valid `t0` can't leave `TIME`. -/
def shiftEval (φ : TProp) (t0 : Time) (D : ℝ) (n : ℤ) (h : t0.val + D * n ∈ TIME) : Prop :=
  φ ⟨t0.val + D * n, h⟩

/-- Value-level counterpart of `shiftEval`. -/
def shiftEvalC {α} (A : TVal α) (t0 : Time) (D : ℝ) (n : ℤ) (h : t0.val + D * n ∈ TIME) : α :=
  A ⟨t0.val + D * n, h⟩

/-- SFS.mm `df-bl.ts`/`bl.tsi`. -/
theorem dl_ts (φ : TProp) (t0 : Time) (D : ℝ) (n : ℤ) (h : t0.val + D * n ∈ TIME) :
    shiftEval φ t0 D n h = interpAt φ ⟨t0.val + D * n, h⟩ := rfl

/-- SFS.mm `df-bl.tsc`/`bl.tsci`. -/
theorem dl_tsc {α} (A : TVal α) (t0 : Time) (D : ℝ) (n : ℤ) (h : t0.val + D * n ∈ TIME) :
    shiftEvalC A t0 D n h = interpValAt A ⟨t0.val + D * n, h⟩ := rfl

/-- SFS.mm `bl.ts0`: an unspecified shift is a shift by `0`. -/
theorem dl_ts0 (φ : TProp) (t0 : Time) (D : ℝ) (h : t0.val + D * (0 : ℤ) ∈ TIME) :
    shiftEval φ t0 D 0 h ↔ interpAt φ t0 := by
  have heq : (⟨t0.val + D * (0 : ℤ), h⟩ : Time) = t0 := Subtype.ext (by push_cast; ring)
  simp only [shiftEval, interpAt, heq]

/-- SFS.mm `bl.tsc0`, value-level counterpart. -/
theorem dl_tsc0 {α} (A : TVal α) (t0 : Time) (D : ℝ) (h : t0.val + D * (0 : ℤ) ∈ TIME) :
    shiftEvalC A t0 D 0 h = interpValAt A t0 := by
  have heq : (⟨t0.val + D * (0 : ℤ), h⟩ : Time) = t0 := Subtype.ext (by push_cast; ring)
  simp only [shiftEvalC, interpValAt, heq]

/-- SFS.mm `bl.tscomi`: composing two shifts by the same step size adds the
multipliers. -/
theorem dl_tscomi (φ : TProp) (t0 : Time) (D : ℝ) (m n : ℤ)
    (h1 : t0.val + D * m ∈ TIME) (h2 : (t0.val + D * m) + D * n ∈ TIME)
    (h3 : t0.val + D * ((m + n : ℤ) : ℝ) ∈ TIME) :
    shiftEval φ ⟨t0.val + D * m, h1⟩ D n h2 ↔ shiftEval φ t0 D (m + n) h3 := by
  have heq : (⟨(t0.val + D * m) + D * n, h2⟩ : Time) = ⟨t0.val + D * ((m + n : ℤ) : ℝ), h3⟩ :=
    Subtype.ext (by push_cast; ring)
  simp only [shiftEval, heq]

/-- SFS.mm `bl.tscomci`, value-level counterpart. -/
theorem dl_tscomci {α} (A : TVal α) (t0 : Time) (D : ℝ) (m n : ℤ)
    (h1 : t0.val + D * m ∈ TIME) (h2 : (t0.val + D * m) + D * n ∈ TIME)
    (h3 : t0.val + D * ((m + n : ℤ) : ℝ) ∈ TIME) :
    shiftEvalC A ⟨t0.val + D * m, h1⟩ D n h2 = shiftEvalC A t0 D (m + n) h3 := by
  have heq : (⟨(t0.val + D * m) + D * n, h2⟩ : Time) = ⟨t0.val + D * ((m + n : ℤ) : ℝ), h3⟩ :=
    Subtype.ext (by push_cast; ring)
  simp only [shiftEvalC, heq]

/-- SFS.mm `bl.tsbii`: `^.`-congruence for predicates, same pointwise-iff convention
as `dl_atbi`. -/
theorem dl_tsbii {φ ψ : TProp} {D : ℝ} {m n : ℤ} (hpq : interp (φ ↔ₜ ψ)) (hmn : m = n)
    {t0 : Time} {h : t0.val + D * m ∈ TIME} {h' : t0.val + D * n ∈ TIME} :
    shiftEval φ t0 D m h ↔ shiftEval ψ t0 D n h' := by
  subst hmn; exact hpq ⟨t0.val + D * m, h⟩

/-- SFS.mm `bl.tseqi`: `^.`-congruence for values. -/
theorem dl_tseqi {α} {A B : TVal α} {D : ℝ} {m n : ℤ} (hAB : A = B) (hmn : m = n)
    {t0 : Time} {h : t0.val + D * m ∈ TIME} {h' : t0.val + D * n ∈ TIME} :
    shiftEvalC A t0 D m h = shiftEvalC B t0 D n h' := by subst hAB; subst hmn; rfl

/-! ### Distribute `^.` over logic -/

/-- SFS.mm `bl.tsan2i`. -/
theorem shiftEval_and (φ ψ : TProp) (t0 : Time) (D : ℝ) (n : ℤ) (h : t0.val + D * n ∈ TIME) :
    shiftEval (φ ∧ₜ ψ) t0 D n h ↔ shiftEval φ t0 D n h ∧ shiftEval ψ t0 D n h := Iff.rfl
/-- SFS.mm `bl.tsor2i`. -/
theorem shiftEval_or (φ ψ : TProp) (t0 : Time) (D : ℝ) (n : ℤ) (h : t0.val + D * n ∈ TIME) :
    shiftEval (φ ∨ₜ ψ) t0 D n h ↔ shiftEval φ t0 D n h ∨ shiftEval ψ t0 D n h := Iff.rfl
theorem shiftEval_not (φ : TProp) (t0 : Time) (D : ℝ) (n : ℤ) (h : t0.val + D * n ∈ TIME) :
    shiftEval (¬ₜφ) t0 D n h ↔ ¬ shiftEval φ t0 D n h := Iff.rfl
theorem shiftEval_imp (φ ψ : TProp) (t0 : Time) (D : ℝ) (n : ℤ) (h : t0.val + D * n ∈ TIME) :
    shiftEval (φ →ₜ ψ) t0 D n h ↔ (shiftEval φ t0 D n h → shiftEval ψ t0 D n h) := Iff.rfl
theorem shiftEval_iff (φ ψ : TProp) (t0 : Time) (D : ℝ) (n : ℤ) (h : t0.val + D * n ∈ TIME) :
    shiftEval (φ ↔ₜ ψ) t0 D n h ↔ (shiftEval φ t0 D n h ↔ shiftEval ψ t0 D n h) := Iff.rfl

-- SFS.mm `bl.tsan3i`/`bl.tsan3ri`/`bl.tsan3li`/`bl.tsor3i`/`bl.tsor3ri`/`bl.tsor3li`
-- (3-term/left/right variants) fall out of `shiftEval_and`/`shiftEval_or` applied
-- twice, same as the `@`-over-conjunction 3-term case earlier; `bl.tsani`/`bl.tsori`
-- (wff-list variants) depend on the skipped multiterm-list plumbing, same as
-- `bl.atad3` etc. above.

/-! ### Distribute `^.` over arithmetic -/

/-- SFS.mm `bl.tsad2i`. -/
theorem shiftEvalC_add (A B : TVal ℝ) (t0 : Time) (D : ℝ) (n : ℤ) (h : t0.val + D * n ∈ TIME) :
    shiftEvalC (A + B) t0 D n h = shiftEvalC A t0 D n h + shiftEvalC B t0 D n h := rfl
/-- SFS.mm `bl.tssubi`. -/
theorem shiftEvalC_sub (A B : TVal ℝ) (t0 : Time) (D : ℝ) (n : ℤ) (h : t0.val + D * n ∈ TIME) :
    shiftEvalC (A - B) t0 D n h = shiftEvalC A t0 D n h - shiftEvalC B t0 D n h := rfl
/-- SFS.mm `bl.tsmul2i`. -/
theorem shiftEvalC_mul (A B : TVal ℝ) (t0 : Time) (D : ℝ) (n : ℤ) (h : t0.val + D * n ∈ TIME) :
    shiftEvalC (A * B) t0 D n h = shiftEvalC A t0 D n h * shiftEvalC B t0 D n h := rfl
/-- SFS.mm `bl.tsdivi`. -/
theorem shiftEvalC_div (A B : TVal ℝ) (t0 : Time) (D : ℝ) (n : ℤ) (h : t0.val + D * n ∈ TIME) :
    shiftEvalC (A / B) t0 D n h = shiftEvalC A t0 D n h / shiftEvalC B t0 D n h := rfl
/-- SFS.mm `bl.tsumi`. -/
theorem shiftEvalC_neg (A : TVal ℝ) (t0 : Time) (D : ℝ) (n : ℤ) (h : t0.val + D * n ∈ TIME) :
    shiftEvalC (-A) t0 D n h = -shiftEvalC A t0 D n h := rfl

-- SFS.mm `bl.tsad3ri`/`bl.tsad3li`/`bl.tsmul3ri`/`bl.tsmul3li` (3-term variants)
-- fall out of `shiftEvalC_add`/`shiftEvalC_mul` applied twice; `bl.tsadi`/`bl.tsmuli`
-- (list variants) depend on the skipped multiterm-list plumbing, same as above.

/-! ### Distribute `^.` over relations and quantifiers -/

/-- SFS.mm `bl.tsdeqi`. -/
theorem shiftEval_teq (A B : TVal ℝ) (t0 : Time) (D : ℝ) (n : ℤ) (h : t0.val + D * n ∈ TIME) :
    shiftEval (teq A B) t0 D n h ↔ shiftEvalC A t0 D n h = shiftEvalC B t0 D n h := Iff.rfl
/-- SFS.mm `bl.tslti`. -/
theorem shiftEval_tlt (A B : TVal ℝ) (t0 : Time) (D : ℝ) (n : ℤ) (h : t0.val + D * n ∈ TIME) :
    shiftEval (tlt A B) t0 D n h ↔ shiftEvalC A t0 D n h < shiftEvalC B t0 D n h := Iff.rfl
/-- SFS.mm `bl.tsami`. -/
theorem shiftEval_tle (A B : TVal ℝ) (t0 : Time) (D : ℝ) (n : ℤ) (h : t0.val + D * n ∈ TIME) :
    shiftEval (tle A B) t0 D n h ↔ shiftEvalC A t0 D n h ≤ shiftEvalC B t0 D n h := Iff.rfl

/-- SFS.mm `df-bl.tsali`. -/
theorem shiftEval_ralt {D' : Type*} (φ : D' → TProp) (A : Set D') (t0 : Time) (D : ℝ) (n : ℤ)
    (h : t0.val + D * n ∈ TIME) :
    shiftEval (fun t => ∀ x ∈ A, φ x t) t0 D n h ↔ ∀ x ∈ A, shiftEval (φ x) t0 D n h := Iff.rfl
/-- SFS.mm `df-bl.tsexi`. -/
theorem shiftEval_rext {D' : Type*} (φ : D' → TProp) (A : Set D') (t0 : Time) (D : ℝ) (n : ℤ)
    (h : t0.val + D * n ∈ TIME) :
    shiftEval (fun t => ∃ x ∈ A, φ x t) t0 D n h ↔ ∃ x ∈ A, shiftEval (φ x) t0 D n h := Iff.rfl

-- SFS.mm `df-bl.tssumi`/`df-bl.tsprodi`/`df-bl.tsqq` (`^.` distributing over `sum_`/
-- `prod_`/conditional expressions), and `bl.tsoi` (the `TIME`-membership
-- side-condition helper for converting `^.` into `@`), are out of scope for the
-- same reasons `df-bl.atsum`/`atprod`/`atqq` were: real `Finset.sum`/`if`-`then`-
-- `else` integration, or a technical side lemma about hypotheses rather than
-- independent content.

/-! ## Domain ontology (SFS.mm lines 2726-3150)

Everything below mirrors SFS.mm's own `$c`/`$a` declarations, per the project's
"everything as axioms, first pass" decision -- but honoring SFS.mm's own `df-`
naming discipline: a `df-X` statement in SFS.mm *defines* a new derived symbol `X`
purely in terms of already-introduced primitives and ordinary logic (Metamath uses
`$a` for these only because it lacks an automatic eliminable-definition checker for
this shape, not because they are independently axiomatic), so those become Lean
`def`s with the stated biconditional following as `Iff.rfl`/`rfl`. Genuinely
primitive relations (`PartOf`, `Location`, `InRegion`, `OnSurface`, `birth`,
`death`, ...) and the non-`df`-named constraints *on* them (`df-par`, `df-ptr`,
`df-lfu`, `df-lin`, `df-rdi`, `df-apar`, `df-pec`, `df-rni`, `df-birth`,
`df-death`) remain `axiom`s, since nothing here can derive them.

Opaque carrier types stand in for SFS.mm's Metamath typecodes `part`/`region`/
`point`/`surface`. -/

/-- Carrier for what an occurrence's temporal extent is a set *of*; SFS.mm leaves
this fully generic (its `A` is an unconstrained class). Moved up from its original
position under "Time -- Allen's Intervals" below (still where SFS.mm itself
introduces it, line-number-wise) -- `Mereology`'s own `PartOf` now needs `Occurrence`
to already exist, per the 2026-08-21 `Part`-retirement (see that axiom's own doc
comment); genuine forward-reference, not a reorganization for its own sake.

**Class-based (2026-08-26, at direct request, extending the `Now` recipe to every
axiom with no characterizing law at all)**: unlike `birth`/`death`/`timeof`/`now`,
`Item` (and every other axiom converted alongside it below -- `Region`/`Point`/
`Surface`/`PartOf`/`Location`/`InRegion`/`OnSurface`/`Adjacent`/`featureAccess`/
`featureAccessProp`/`wonce`/`trueItem`/`falseItem`) never asserted a satisfiability
condition to begin with (no biconditional, no guard) -- `axiom Item : Type` just
posited a free constant of that type, with nothing to prove consistent. Converting
these still shrinks `#print axioms`' trust footprint for the same reason `now` did:
each becomes a `Classical.choose` witness of a *trivial* `∃ x : T, True` rather than
an independent axiom, so it's derived from Lean's standard classical axioms (already
present) instead of adding new ones. `Classical.choose` (not a concrete pick like
`ℕ`) is used throughout this batch for the same reason it was for `now`: it keeps
the witness opaque, so nothing downstream can accidentally exploit structure (e.g.
`ℕ`'s successor/order) that an opaque primitive was never meant to have. -/
class ItemT where
  Item : Type

export ItemT (Item)

noncomputable instance itemModel : ItemT :=
  ⟨Classical.choose (⟨ℕ, trivial⟩ : ∃ _ : Type, True)⟩

/-- SFS.mm's implicit type for `A` in `exists`/`birth`/`death`/Allen's-relations: a
temporal value whose extent, at each instant, is a set of `Item`s (empty = doesn't
exist then). Reuses the real `TVal`/`interpValAt` machinery from the BLESS-logic
section above rather than re-axiomatizing evaluation-at-an-instant. -/
abbrev Occurrence := TVal (Set Item)

/-! ### Mereology (SFS.mm lines 2726-2816) -/

/-- SFS.mm `wpartof`: primitive. **Typed over `Occurrence`, not a separate opaque
`Part` carrier type** -- `Mereology.kerml` itself (the real KerML source, not a
translation choice made independently here) declares `PartOf`'s own `x`/`y` as
`Occurrence`, not a distinct `Part` classifier (2026-08-21 edit, matching this file's
change the same day). The formerly-separate `axiom Part : Type` is retired
entirely -- every definition/theorem below that used to be `Part`-typed (and
`Location`/`lfu`/`lin`/`AtomicRegion`/`apar`/`expansivity` further down, which share
the same variable with `PartOf`/`AtomPart` calls) is `Occurrence`-typed now too, not
just this one axiom, since a stale `Part` anywhere in this cluster would no longer
type-check against the others.

**Class-based (2026-08-26, at direct request, upgrading the earlier bare
`PartOfRel` conversion): `PartOf`/`par`/`ptr`/`pch` bundled together**, unlike the
`Item`-style batch above -- `par`/`ptr`/`pch` are genuine constraints (not derivable
from a bare `PartOf` alone), so eliminating them as `axiom`s (per the axiom survey's
category 3) needs an actual constructed relation satisfying all three at once, not
just a trivial existence witness for `PartOf`'s own type. `pch`'s `PartDisjoint x y`
conjunct is inlined here as `¬ ∃ z, PartOf z x ∧ PartOf z y` (its unfolding) rather
than calling the `PartDisjoint`/`Overlap` `def`s below, since those are defined
*in terms of* this class's own exported `PartOf` and so can't be referenced from
inside the class that produces it -- definitionally identical either way. -/
class Mereology where
  PartOf : Occurrence → Occurrence → Prop
  par : ∀ x, ¬ PartOf x x
  ptr : ∀ {x y z}, PartOf x y → PartOf y z → PartOf x z
  pch : ∀ x y, ((PartOf x y ∨ PartOf y x) ∨ (x = y ∨ ¬ ∃ z, PartOf z x ∧ PartOf z y)) ∧
      ¬ (PartOf x y ∧ PartOf y x)

export Mereology (PartOf par ptr pch)

/-- The consistency certificate's existence half: the "nothing is ever part of
anything" relation genuinely satisfies `par`/`ptr`/`pch` all three at once --
`ptr`/`par` vacuously (their hypotheses are always `False`), and `pch`'s only real
content (comparability) holds because an always-`False` `PartOf` makes `Overlap`
always `False` too, so every pair is unconditionally `PartDisjoint`, satisfying
`pch`'s fourth disjunct unconditionally. This doesn't commit `PartOf` itself to
this trivial relation (`mereologyModel` below goes through `Classical.choose`, same
as `Lifetimes`/`Now`, so the actual witness stays opaque) -- it only certifies *a*
model exists, which is what turns `par`/`ptr`/`pch` from assumed to proven. -/
theorem mereology_exists :
    ∃ R : Occurrence → Occurrence → Prop,
      (∀ x, ¬ R x x) ∧
      (∀ x y z, R x y → R y z → R x z) ∧
      (∀ x y, ((R x y ∨ R y x) ∨ (x = y ∨ ¬ ∃ z, R z x ∧ R z y)) ∧ ¬ (R x y ∧ R y x)) := by
  refine ⟨fun _ _ => False, fun _ h => h, fun _ _ _ h _ => h, fun _ _ => ?_⟩
  simp

noncomputable instance mereologyModel : Mereology where
  PartOf := Classical.choose mereology_exists
  par := (Classical.choose_spec mereology_exists).1
  ptr {x y z} := (Classical.choose_spec mereology_exists).2.1 x y z
  pch := (Classical.choose_spec mereology_exists).2.2

/-- SFS.mm `df-pov`. -/
def Overlap (x y : Occurrence) : Prop := ∃ z, PartOf z x ∧ PartOf z y

/-- SFS.mm `df-pun`. -/
def Underlap (x y : Occurrence) : Prop := ∃ z, PartOf x z ∧ PartOf y z

/-- SFS.mm `df-pim`. -/
def ImproperPart (x y : Occurrence) : Prop := PartOf x y ∨ x = y

/-- SFS.mm `df-pdj`. SFS.mm's own text reads `p_x Disjoint p_y <-> -. p_y Overlap
p_y` (self-overlap of `y`, not overlap of `x` and `y`) -- almost certainly a
transcription slip for `-. p_x Overlap p_y`, which is what is used here; flagged,
not corrected in SFS.mm itself. -/
def PartDisjoint (x y : Occurrence) : Prop := ¬ Overlap x y

/-- SFS.mm `df-pch`: despite the `df-` name this doesn't define a new symbol -- it's
purely a constraint (any two parts are comparable, equal, or disjoint, and not
mutually part of each other), not derivable from `df-par`/`df-ptr` alone. Now a real
theorem (see `Mereology`'s own `pch` field far above), restated here in terms of
`PartDisjoint` -- its original, non-inlined shape -- since `PartDisjoint` itself
wasn't in scope yet at the class declaration. -/
theorem pch' (x y : Occurrence) :
    ((PartOf x y ∨ PartOf y x) ∨ (x = y ∨ PartDisjoint x y)) ∧ ¬ (PartOf x y ∧ PartOf y x) :=
  pch x y

/-- SFS.mm `df-pat`. -/
def AtomPart (x : Occurrence) : Prop := ¬ ∃ z, PartOf z x

/-- SFS.mm `df-pwh`. -/
def WholePart (x : Occurrence) : Prop := ∀ z, PartOf z x ∨ x = z

-- SFS.mm's `povrfl`/`punrfl`/`pimrfl`/`pdjrfl` are unproven placeholders (`$= ?`)
-- there too (see `reference_metamath_sfs_toolchain.md`'s baseline-placeholder list).
-- Three are, in fact, real theorems here, needing no axiom:
theorem povrfl (x y : Occurrence) : Overlap x y ↔ Overlap y x :=
  exists_congr fun _ => and_comm
theorem punrfl (x y : Occurrence) : Underlap x y ↔ Underlap y x :=
  exists_congr fun _ => and_comm
theorem pdjrfl (x y : Occurrence) : PartDisjoint x y ↔ PartDisjoint y x := by
  unfold PartDisjoint; rw [povrfl]
-- `pimrfl` (`ImproperPart x y ↔ ImproperPart y x`, i.e. `PartOf x y ∨ x=y ↔
-- PartOf y x ∨ y=x`) is deliberately *not* translated: given only `df-par`
-- (antireflexive) and `df-ptr` (transitive) for `PartOf`, it is not provable, and
-- for any concrete antisymmetric part-of relation (the ordinary reading of
-- mereological parthood) it is false whenever `x` is a proper part of `y`.
-- Asserting it as an axiom would make the axiom set inconsistent with such a
-- model; SFS.mm itself leaves it as an unproven `$= ?`, never cited elsewhere.

/-! ### Region and Location (SFS.mm lines 2816-2962) -/

/-- Generic (`Region`/`Point` still free) restatements of `RegionOverlap`/
`RegionContainment`/`AtomicRegion` below, needed *before* `RegionModel` exists so
`lin`/`rdi`/`apar`/`expansivity` can be stated as fields of the very class that
produces `Region`/`Point`/`Location`/`InRegion` -- same forward-reference problem
`Mereology`'s `pch` field solved by inlining, here solved by parameterizing instead
(cleaner given how much these three get reused across `rdi`/`apar`/`expansivity`).
Once `RegionModel`'s fields are exported, `RegionOverlap r1 r2` etc. below are
definitionally identical to these applied to the exported `InRegion`/`Location`. -/
private def regionOverlapOf {Region Point : Type} (InRegion : Point → Region → Prop)
    (r1 r2 : Region) : Prop := ∃ p, InRegion p r1 ∧ InRegion p r2

private def regionContainmentOf {Region Point : Type} (InRegion : Point → Region → Prop)
    (r1 r2 : Region) : Prop := ∀ p, InRegion p r2 → InRegion p r1

private def atomicRegionOf {Region Point : Type} (Location : Occurrence → Region)
    (InRegion : Point → Region → Prop) (r0 : Region) : Prop :=
  ∀ (x : Occurrence) (r1 : Region), Location x = r1 ∧ regionContainmentOf InRegion r0 r1 → r0 = r1

/-- **Class-based (2026-08-26, at direct request, upgrading the earlier separate
`RegionT`/`PointT`/`LocationFn`/`InRegionRel` conversions): `Region`/`Point`/
`Location`/`InRegion` bundled together with `lin`/`rdi`/`apar`/`expansivity`**, same
upgrade `Mereology` got over the bare `PartOfRel` conversion -- these four are
genuine constraints tying `Location`/`InRegion` to each other and to `PartOf`, so
eliminating them needs one jointly-constructed model, not independent trivial
witnesses per primitive (which is why the earlier `RegionT`/`PointT` witnesses
carried no relationship between `Region`'s size and `Occurrence`'s -- fine for
`Item`-style axioms with no law, fatal for `lin`, which needs `Location` injective).

**`expansivity`'s conclusion is `RegionContainment r2 r1`, not `r1 r2`** --
`Regions.kerml`'s own real `EXPNS` formula (`Kernel.lean`'s `#check kernel%
@Assert{n="EXPNS";...}` block) concludes `RegionContainment(r2,r1)` (whole's region
contains part's region), but the axiom this replaced had `r1 r2` (part contains
whole) -- a transcription slip discovered while building this model, same kind as
the already-flagged `df-pdj`/`PartDisjoint` one earlier in the file. Fixed here to
match the real source, not silently carried forward.

**`no_interpenetration` folded in too (2026-08-26, at direct request, extending this
same class rather than a fresh one)**: unlike `lin`/`rdi`/`apar`/`expansivity`,
`no_interpenetration` isn't tied to `Location`/`AtomPart` at all -- it's a bare
laminarity statement about `InRegion` and `PartOf` (any two overlapping regions must
be nested), so it needed re-verifying against the *same* witness below (`region_exists`'s
own proof), not a new one: given a common point `p` of `r1`/`r2`, `pch`'s own
comparable-or-disjoint guarantee (with the "disjoint" branch directly contradicted by
`p` itself) forces `r1`/`r2` into exactly the cases `expansivity`'s own transitivity
argument already handles. -/
class RegionModel where
  Region : Type
  Point : Type
  Location : Occurrence → Region
  InRegion : Point → Region → Prop
  lin : ∀ {x y : Occurrence} {r : Region}, Location x = r → Location y = r → x = y
  rdi : ∀ {r1 r2 : Region}, atomicRegionOf Location InRegion r1 → atomicRegionOf Location InRegion r2 →
      ¬ regionOverlapOf InRegion r1 r2 ∨ r1 = r2
  apar : ∀ {x : Occurrence} {r0 : Region}, Location x = r0 → AtomPart x →
      atomicRegionOf Location InRegion r0
  expansivity : ∀ {x y : Occurrence} {r1 r2 : Region}, Location x = r1 → Location y = r2 →
      PartOf x y → regionContainmentOf InRegion r2 r1
  no_interpenetration : ∀ {r1 r2 : Region}, regionOverlapOf InRegion r1 r2 →
      regionContainmentOf InRegion r1 r2 ∨ regionContainmentOf InRegion r2 r1

export RegionModel (Region Point Location InRegion lin rdi apar expansivity
  no_interpenetration)

/-- The consistency certificate's existence half: `Region := Point := Occurrence`,
`Location := id` (trivially injective, giving `lin` for free), and
`InRegion p r := (p = r) ∨ PartOf p r` (a point "is in" a region iff it equals it or
is a `PartOf` it). Under this witness `atomicRegionOf ... r0` turns out to be
*exactly* `AtomPart r0` (nothing is ever `PartOf` `r0`) -- which makes `apar` an
identity, `rdi` follow from atoms-can't-overlap, and `expansivity` follow directly
from `ptr` (transitivity). This doesn't commit `Region`/`Location`/`InRegion` to
this specific witness (`regionModel` below goes through `Classical.choose`, same as
`Mereology`/`Lifetimes`/`Now`, so the actual values stay opaque) -- it only
certifies *a* model exists. -/
theorem region_exists :
    ∃ (Region Point : Type) (Location : Occurrence → Region) (InRegion : Point → Region → Prop),
      (∀ {x y : Occurrence} {r : Region}, Location x = r → Location y = r → x = y) ∧
      (∀ {r1 r2 : Region}, atomicRegionOf Location InRegion r1 → atomicRegionOf Location InRegion r2 →
          ¬ regionOverlapOf InRegion r1 r2 ∨ r1 = r2) ∧
      (∀ {x : Occurrence} {r0 : Region}, Location x = r0 → AtomPart x →
          atomicRegionOf Location InRegion r0) ∧
      (∀ {x y : Occurrence} {r1 r2 : Region}, Location x = r1 → Location y = r2 →
          PartOf x y → regionContainmentOf InRegion r2 r1) ∧
      (∀ {r1 r2 : Region}, regionOverlapOf InRegion r1 r2 →
          regionContainmentOf InRegion r1 r2 ∨ regionContainmentOf InRegion r2 r1) := by
  refine ⟨Occurrence, Occurrence, id, fun p r => p = r ∨ PartOf p r, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y r hx hy
    exact hx.trans hy.symm
  · intro r1 r2 h1 h2
    by_cases heq : r1 = r2
    · exact Or.inr heq
    · refine Or.inl ?_
      have hno1 : ¬ ∃ z, PartOf z r1 := by
        rintro ⟨z, hz⟩
        have hcont : regionContainmentOf (fun p r => p = r ∨ PartOf p r) r1 z := by
          intro q hq
          rcases hq with hq | hq
          · exact hq ▸ Or.inr hz
          · exact Or.inr (ptr hq hz)
        have hz' : z = r1 := (h1 z z (And.intro rfl hcont)).symm
        exact par r1 (hz' ▸ hz)
      have hno2 : ¬ ∃ z, PartOf z r2 := by
        rintro ⟨z, hz⟩
        have hcont : regionContainmentOf (fun p r => p = r ∨ PartOf p r) r2 z := by
          intro q hq
          rcases hq with hq | hq
          · exact hq ▸ Or.inr hz
          · exact Or.inr (ptr hq hz)
        have hz' : z = r2 := (h2 z z (And.intro rfl hcont)).symm
        exact par r2 (hz' ▸ hz)
      rintro ⟨p, hp1, hp2⟩
      rcases hp1 with hp1 | hp1
      · rcases hp2 with hp2 | hp2
        · exact heq (hp1.symm.trans hp2)
        · exact hno2 ⟨r1, hp1 ▸ hp2⟩
      · exact hno1 ⟨p, hp1⟩
  · intro x r0 hloc hatom x' r1' hyp
    have hloc' : x = r0 := hloc
    obtain ⟨hx', hcont⟩ := hyp
    rcases hcont r1' (Or.inl rfl) with h | h
    · exact h.symm
    · exact absurd ⟨r1', hloc'.symm ▸ h⟩ hatom
  · intro x y r1 r2 hx hy hxy p hp
    have hx' : x = r1 := hx
    have hy' : y = r2 := hy
    subst hx'
    subst hy'
    rcases hp with hp | hp
    · subst hp
      exact Or.inr hxy
    · exact Or.inr (ptr hp hxy)
  · intro r1 r2 hover
    have partOf_contains : ∀ {x y : Occurrence}, PartOf x y →
        ∀ p, (p = x ∨ PartOf p x) → (p = y ∨ PartOf p y) := by
      intro x y hxy p hp
      rcases hp with hp | hp
      · subst hp; exact Or.inr hxy
      · exact Or.inr (ptr hp hxy)
    obtain ⟨p, hp1, hp2⟩ := hover
    rcases hp1 with hp1 | hp1
    · rcases hp2 with hp2 | hp2
      · left
        have heq : r1 = r2 := hp1.symm.trans hp2
        subst heq
        exact fun q hq => hq
      · right
        have hpr : PartOf r1 r2 := by subst hp1; exact hp2
        exact partOf_contains hpr
    · rcases hp2 with hp2 | hp2
      · left
        have hpr : PartOf r2 r1 := by subst hp2; exact hp1
        exact partOf_contains hpr
      · rcases (pch r1 r2).1 with (hc | hc) | (heq | hdisj)
        · right; exact partOf_contains hc
        · left; exact partOf_contains hc
        · left; subst heq; exact fun q hq => hq
        · exact absurd ⟨p, hp1, hp2⟩ hdisj

noncomputable instance regionModelInstance : RegionModel where
  Region := (Classical.choose region_exists)
  Point := (Classical.choose (Classical.choose_spec region_exists))
  Location := Classical.choose (Classical.choose_spec (Classical.choose_spec region_exists))
  InRegion := Classical.choose
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec region_exists)))
  lin := (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec region_exists)))).1
  rdi := (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec region_exists)))).2.1
  apar := (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec region_exists)))).2.2.1
  expansivity := (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec region_exists)))).2.2.2.1
  no_interpenetration := (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec region_exists)))).2.2.2.2

/- SFS.mm `wrp`/`won`: `Surface`/`OnSurface` themselves are now produced by
`SurfaceModel` further below (bundled with `RegionSurface`/`RegionInterior`/
`regionSurfaceProp`/`regionInteriorProp`, for the same reason `Region`/`Point`/
`Location`/`InRegion` had to be: those four genuinely tie `Surface`/`OnSurface` to
`RegionSurface`/`RegionInterior`, so eliminating them needs one jointly-constructed
model, not independent trivial witnesses per primitive. -/

/- SFS.mm `wloc`/`win`: `Location`/`InRegion` themselves are now produced by
`RegionModel` far above (bundled with `lin`/`rdi`/`apar`/`expansivity`, since those
tie `Location`/`InRegion` together and to `PartOf` and so can't be witnessed
independently). **Function-valued (`Occurrence → Region`), not a relation** --
2026-08-21 change, at direct request: `Regions.kerml`'s own real `Location` is
declared as a function (`o~Occurrence := result~Region | o L result`, a `:=`-body,
KerML's own functional shape for it), and `LFU`/`LIN`/`EXPNS`/`APAR` all call
`Location(x)` as a one-argument function returning a `Region`, not a two-argument
predicate. Deliberately does **not** attempt to wire up the infix `L` notation
those same real formulas' own *definitions* use (`o L result`) -- disregarded at
request, `SFS.lean` still has no `L`, and `Location`'s own `@Assert` formula is
expected to keep failing for that specific reason; see `Assert.lean`'s own note. -/

/-- `Regions.kerml`'s own real `Adj(p)` ("the set of adjacent points to `p`"),
`df-adjp`, was previously genuinely unformalized -- `Regions.kerml`'s own comment
already called it future work, and it was never attempted in `SFS.mm` either. Added
2026-08-21, at direct request, as a real primitive relation (not translating any
`SFS.mm` content -- same "new primitive, not an `SFS.mm` translation" status as
`featureAccess`/`Get` above): `p1`/`p2` are infinitesimally close points. No further
constraint (symmetry, irreflexivity, ...) is asserted -- none was requested, and
inventing one would be exactly the kind of forced semantics this file avoids
elsewhere. `Regions.kerml`'s own `RegionSurface`/`RegionFilm` formulas, which used to
call the now-real `Adjacent` via the set-membership idiom `p2 in Adj(p)`, are updated
to call it directly as `Adjacent(p, p2)` instead -- a proper predicate application,
not the informal `xPy`-style bare-identifier form `Adjacent`'s *own* `@Assert`
formula uses (see `Regions.kerml`), so those two formulas now elaborate live.
Class-based, same batch/treatment as `Item` above. -/
class AdjacentRel where
  Adjacent : Point → Point → Prop
export AdjacentRel (Adjacent)
noncomputable instance adjacentModel : AdjacentRel :=
  ⟨Classical.choose (⟨fun _ _ => True, trivial⟩ : ∃ _ : Point → Point → Prop, True)⟩

/-- SFS.mm `df-lfu`: locational functionality. Was a genuine axiom (a constraint on
a *relation*, not derivable); now a real theorem, since a Lean function is
automatically single-valued -- `Location`'s own new function-valued type already
proves this, `lfu` just restates it in the `Location x = r1 → Location x = r2 →
r1 = r2` shape downstream content still expects. -/
theorem lfu {x : Occurrence} {r1 r2 : Region} (h1 : Location x = r1) (h2 : Location x = r2) :
    r1 = r2 := h1 ▸ h2

/- SFS.mm `df-lin`: injectivity of location. Now a real theorem (see `RegionModel`'s
own `lin` field far above) -- proven, not a genuine independent constraint, once
`Location`/`Region` are jointly constructed rather than each opaque on its own. -/

/-- SFS.mm `df-rov`. -/
def RegionOverlap (r1 r2 : Region) : Prop := ∃ p, InRegion p r1 ∧ InRegion p r2

/-- SFS.mm `df-rco`. -/
def RegionContainment (r1 r2 : Region) : Prop := ∀ p, InRegion p r2 → InRegion p r1

/-- SFS.mm `df-rat`. -/
def AtomicRegion (r0 : Region) : Prop :=
  ∀ (x : Occurrence) (r1 : Region), Location x = r1 ∧ RegionContainment r0 r1 → r0 = r1

/- SFS.mm `df-rdi`: atomic regions are disjoint or equal. Now a real theorem (see
`RegionModel`'s own `rdi` field far above). -/

/- SFS.mm `df-apar`: atomic parts have atomic regions. Now a real theorem (see
`RegionModel`'s own `apar` field far above). -/

/- SFS.mm `df-pec`: expansivity, tying `PartOf` to `RegionContainment` via
`Location`. Now a real theorem (see `RegionModel`'s own `expansivity` field far
above, including the argument-order fix documented there). -/

/- SFS.mm `df-rni`: no interpenetration. Now a real theorem (see `RegionModel`'s own
`no_interpenetration` field far above), folded into that class once it turned out to
follow from the same witness's `pch`/`ptr` reasoning `expansivity` already used. -/

/- SFS.mm `wrs`, function-valued (`Region → Surface`), not a relation -- 2026-08-21
change, at direct request, same reasoning as `Location` above:
`Regions.kerml`'s own real `RegionSurface`/`RegionInterior`/`RegionFilm` are all
declared as one-argument functions (`r~Region := result~Surface | ...`), and every
real formula calling them (`RegionInterior`'s/`RegionFilm`'s own bodies,
`ExternallyConnected`/`FilmConnected`) does so as a one-arg call, not a two-arg
predicate. **Unlike `Location`, this is genuinely new primitive content, not just a
tightened restatement of something already axiomatized**: the old `RegionSurface`
(a `def`, derived purely from `InRegion`/`OnSurface`) never asserted uniqueness --
`SFS.mm`/`df-rs` describes *a* satisfying surface, not *the* surface. Making
`RegionSurface` a function asserts, for the first time, that every region has
*exactly one* surface -- a real modeling decision, not a mechanical consequence of
anything already stated, done here because it matches `Regions.kerml`'s own
functional declaration and was explicitly requested, not derived. -/

/-- SFS.mm `df-rs`'s defining property, `RegionSurface`'s own. SFS.mm's own text has
a third conjunct `r_1 RegionSurface r_0` in the body, self-referentially -- but with
a *region* (`r_1`) plugged into `RegionSurface`'s old surface-typed argument slot,
which cannot be what was intended (and `r_0`/`r_1` are already swapped relative to
the rest of the clause). Rather than guess a specific fix, that conjunct is dropped
here (flagged, not silently "corrected" to some particular reading); this reflects
only the two conjuncts whose meaning is unambiguous, same as before the function
change (`SFS.mm`/`df-ri`'s own analogous property for `RegionInterior` below). -/
private def regionSurfacePropOf {Region Point Surface : Type} (InRegion : Point → Region → Prop)
    (OnSurface : Point → Surface → Prop) (RegionSurface : Region → Surface) (r0 : Region) : Prop :=
  ∃ r1 : Region, ∀ p, OnSurface p (RegionSurface r0) → InRegion p r0 ∧ ¬ InRegion p r1

private def regionInteriorPropOf {Region Point Surface : Type} (InRegion : Point → Region → Prop)
    (OnSurface : Point → Surface → Prop) (RegionSurface : Region → Surface)
    (RegionInterior : Region → Region) (r1 : Region) : Prop :=
  ∀ p, InRegion p r1 → InRegion p (RegionInterior r1) ∧ ¬ OnSurface p (RegionSurface (RegionInterior r1))

/-- **Class-based (2026-08-26, at direct request): `Surface`/`OnSurface`/
`RegionSurface`/`RegionInterior` bundled together with `regionSurfaceProp`/
`regionInteriorProp`**, same reasoning as `RegionModel`/`Mereology` above -- these
tie `Surface`/`OnSurface` to `RegionSurface`/`RegionInterior` (and to `Region`/
`InRegion`, already fixed by `RegionModel`), so eliminating them needs one jointly-
constructed model, not the independent trivial witnesses the earlier `SurfaceT`/
`OnSurfaceRel` conversions used (which carried no relationship to `RegionSurface`/
`RegionInterior` at all). -/
class SurfaceModel where
  Surface : Type
  OnSurface : Point → Surface → Prop
  RegionSurface : Region → Surface
  RegionInterior : Region → Region
  regionSurfaceProp : ∀ r0 : Region,
      regionSurfacePropOf InRegion OnSurface RegionSurface r0
  regionInteriorProp : ∀ r1 : Region,
      regionInteriorPropOf InRegion OnSurface RegionSurface RegionInterior r1

export SurfaceModel (Surface OnSurface RegionSurface RegionInterior regionSurfaceProp
  regionInteriorProp)

/-- The consistency certificate's existence half: `Surface := Region`,
`OnSurface := fun _ _ => False` (nothing is ever "on" any surface), `RegionSurface :=
id`, `RegionInterior := id`. Both properties collapse to trivialities under this
witness: `regionSurfaceProp`'s hypothesis (`OnSurface p (RegionSurface r0)`) is
vacuously `False`, so *any* `r1` works; `regionInteriorProp`'s first conjunct becomes
`InRegion p r1 → InRegion p r1` (reflexivity, since `RegionInterior = id`) and its
second is vacuous the same way `regionSurfaceProp`'s hypothesis is. This doesn't
commit `Surface`/`OnSurface`/`RegionSurface`/`RegionInterior` to this witness
(`surfaceModelInstance` below goes through `Classical.choose`, same as
`RegionModel`/`Mereology`/`Lifetimes`/`Now`, so the actual values stay opaque) -- it
only certifies *a* model exists. -/
theorem surface_exists :
    ∃ (Surface : Type) (OnSurface : Point → Surface → Prop) (RegionSurface : Region → Surface)
      (RegionInterior : Region → Region),
      (∀ r0 : Region, regionSurfacePropOf InRegion OnSurface RegionSurface r0) ∧
      (∀ r1 : Region, regionInteriorPropOf InRegion OnSurface RegionSurface RegionInterior r1) := by
  refine ⟨Region, fun _ _ => False, id, id, ?_, ?_⟩
  · intro r0
    exact ⟨r0, fun p hp => absurd hp (by simp)⟩
  · intro r1 p hp
    exact ⟨hp, by simp⟩

noncomputable instance surfaceModelInstance : SurfaceModel where
  Surface := Classical.choose surface_exists
  OnSurface := Classical.choose (Classical.choose_spec surface_exists)
  RegionSurface := Classical.choose (Classical.choose_spec (Classical.choose_spec surface_exists))
  RegionInterior := Classical.choose
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec surface_exists)))
  regionSurfaceProp := (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec surface_exists)))).1
  regionInteriorProp := (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec surface_exists)))).2

/-- SFS.mm `df-rf`. Unlike `RegionSurface`/`RegionInterior`, this one needs **no new
axiom at all** -- once both of those are functions, "the film of `r0`" (SFS.mm: "the
surface of the interior of `r0`") is already fully determined as `RegionSurface
(RegionInterior r0)`, a genuine `def`, not a fresh primitive. The old relational
`RegionFilm s r0 := ∃ r1, RegionInterior r0 r1 ∧ RegionSurface s r1` collapses to
exactly this once `RegionInterior`/`RegionSurface` are single-valued by construction
(the `∃ r1` no longer does any work -- `r1` is pinned to `RegionInterior r0`).
`noncomputable`: unlike `Get`/`GetP` above (whose bodies bottom out in `Set`/`Prop`,
erased at compile time), this returns a genuine `Surface` value built from opaque
axioms with no actual implementation to compile. -/
noncomputable def RegionFilm (r0 : Region) : Surface := RegionSurface (RegionInterior r0)

/-- SFS.mm `df-exc`. Simplified the same way `RegionFilm` was: the old relation's
`∃ s1 s2 : Surface, RegionSurface s1 r1 ∧ RegionSurface s2 r2 ∧ ...` collapses once
`RegionSurface` is a function -- `s1`/`s2` are pinned to `RegionSurface r1`/
`RegionSurface r2`, no longer independently existential. -/
def ExternallyConnected (r1 r2 : Region) : Prop :=
  ∃ p : Point, OnSurface p (RegionSurface r1) ∧ OnSurface p (RegionSurface r2)

/-- SFS.mm `df-flmc`. Same simplification as `ExternallyConnected`, via `RegionFilm`
instead of `RegionSurface`. -/
def FilmConnected (r1 r2 : Region) : Prop :=
  ∃ p : Point, OnSurface p (RegionFilm r1) ∧ OnSurface p (RegionFilm r2)

/-! ### Time -- Allen's Intervals (SFS.mm lines 2962-3117) -/

/-- SFS.mm `df-exists`. A genuine `def`, not an axiom: already fully determined by
`interpValAt`. -/
def existsAt (A : Occurrence) (t0 : Time) : Prop := interpValAt A t0 ≠ ∅

/-! `birth`/`death`, class-based (2026-08-26), porting `Repaired.lean`'s own recipe
(guard the characterizing law with its presupposition, keep the function total --
or here `Option`-valued -- with an unconstrained/undefined value when the
presupposition fails, then *prove* a model exists) from toy `ℕ` to the real
`Instant`/`Time`/`TIME`. The port is not mechanical: `ℕ` is well-ordered for free
(`Nat.strongRecOn`), so *any* nonempty subset has a least element with no extra
assumption. An arbitrary subset of the dense continuum `Time` need not (e.g.
`{t | t.val < 0.5}` has an infimum but no attained minimum), so `birth`'s guard
originally needed a further, separately-axiomatized structural fact
(`hasFirstInstant`, asserting -- falsely, in general, for a dense order -- that
*every* satisfiable `Time → Prop` predicate has an attained least witness) that the
`ℕ` case got for free from well-ordering. That axiom is retired (2026-08-26, same
day, once `finitePartition` below was broadened to cover every `TVal α`): `birth`'s
guard now goes through the real theorem `hasFirstTick`, which needs only
`finitePartition`'s *finite shared-tick* structure, not `Time`'s own order --
`#print axioms model` below shows `finitePartition` explicitly, alongside Lean's
standard classical axioms. `death`, by contrast, needs no such extra fact at all:
its guard is "self-certifying" (`death_exists`'s proof gets a witness handed to it
directly whenever the presupposition holds, and `none` is always available when it
doesn't), the same reasoning that already justified `endShot`'s `Option` redesign
in the first place. -/

class Lifetimes where
  /-- Primitive (no construction of "the first instant `A` exists" is given, only
  the guarded characterizing property `birthIff` below). Returns `Time`, not bare
  `Instant`: an occurrence's birth is itself one of the instants under discussion. -/
  birth : Occurrence → Time
  /-- `Occurrences.kerml`'s own `endShot: Instant[0..1]` (`//SFS`-marked: "The
  Occurrence may not have ended at time now"), unlike `startShot: Instant[1]`,
  which stays mandatory -- `birth` stays total, `death` doesn't. -/
  death : Occurrence → Option Time
  /-- SFS.mm `df-birth`, guarded on `A` existing somewhere (`Repaired.lean`'s own
  pattern): unconditional would force even a never-existing `A` to have *some*
  birth instant. SFS.mm's own text quantifies `A. t_1 e. (0[,)t_0) -. exists(A,t_0)`
  -- reusing the outer `t_0` inside the body instead of the bound `t_1` -- almost
  certainly a transcription slip; read here with `t_1`, matching `deathIff`'s own
  (correct) shape below. -/
  birthIff : ∀ {A : Occurrence} {t0 : Time}, (∃ s, existsAt A s) →
    (birth A = t0 ↔ existsAt A t0 ∧ ∀ t1 : Time, t1.val ∈ Set.Ico (0 : Instant) t0.val → ¬ existsAt A t1)
  /-- SFS.mm `df-death`, restated for `death`'s `Option` codomain: only
  characterizes `death A = some t0`, says nothing about when `death A = none`
  (ongoing) occurs -- `none` isn't itself characterized as "occurs exactly when no
  such `t0` exists"; it's simply the case this law doesn't constrain, which is what
  avoids the old total-`death`'s inconsistency (nothing forces `death A` to be
  `some` for an occurrence that never exists). Needs no extra guard, unlike
  `birthIff`: the `Option` codomain already *is* the guard. -/
  deathIff : ∀ {A : Occurrence} {t0 : Time},
    death A = some t0 ↔ existsAt A t0 ∧ ∀ t1 : Time, t1.val ∈ Set.Ioc t0.val now → ¬ existsAt A t1
  /-- SFS.mm `df-bl.timeof`: primitive, "the first instant `φ` holds" -- exactly
  `birth`'s own shape (`existsAt A` replaced by `interpAt φ`), bundled into this
  same class since it needs the same guard-and-prove treatment and the same
  `hasFirstTick` theorem (below, built on `finitePartition`). -/
  timeof : TProp → Time
  /-- SFS.mm `df-bl.timeof`'s characterizing property, guarded on `φ` holding
  somewhere -- same reasoning as `birthIff`: unconditional would force even a
  nowhere-true `φ` to have *some* first-true instant. -/
  timeofIff : ∀ {φ : TProp} {t1 : Time}, (∃ s, interpAt φ s) →
    (timeof φ = t1 ↔ interpAt φ t1 ∧ ∀ t : Time, t.val ∈ Set.Ico (0 : Instant) t1.val → ¬ interpAt φ t)

export Lifetimes (birth death birthIff deathIff timeof timeofIff)

/-- Every `TVal α`'s raw value only ever changes at finitely many *shared*
instants -- a single "event calendar," not a per-value one (2026-08-26, at direct
request; broadened the same day from an earlier `Occurrence`-only form once
`birth_exists`/`timeof_exists` below were rebuilt on top of it, retiring the
separate `hasFirstInstant` axiom they used to need). Stated without reference to
"pieces" to sidestep any `Ico`/`Icc` boundary bookkeeping: if there is no shared
tick strictly inside `(t1,t2]`, `d`'s value cannot have changed between `t1` and
`t2`. This is a genuine new modeling commitment, not derivable from anything else
in this file -- physically, it says the system has a shared discrete event
structure, matching how `Occurrence`'s `Set Item`-valued (not continuously
varying) values are already modeled; broadening it to arbitrary `TVal α` (rather
than leaving it `Occurrence`-specific) says the same thing about *every*
time-varying quantity, `TProp`-valued ones (`interpAt`/`timeof`) included, not
just `Set Item`-valued ones. It is what fixes `next`'s permanent vacuity and
`changed`'s own gap (see `changed`'s doc comment far below), and (since 2026-08-26)
what `birth`/`timeof` are built on too -- *not* hyperreals, which cannot help
here: two distinct `Time` values are both *standard* reals, so neither "nothing
between" nor "infinitesimally close" can ever hold for them, transfer principle or
not (a dead end reached and rejected before this axiom was proposed); and a
general `Time → Prop` predicate still has no well-ordering to exploit on its own
(`{t | 0 < t.val}` has an infimum but no attained minimum) -- it's specifically
the *finiteness* of the shared tick structure, not `Time`'s own order, that makes
`hasFirstTick` below a real theorem. -/
axiom finitePartition :
    ∃ (n : ℕ) (breaks : Fin (n + 1) → Time),
      breaks 0 = ⟨0, TIME_nonempty⟩ ∧ breaks (Fin.last n) = ⟨now, dl_nowt⟩ ∧
      (∀ i j : Fin (n + 1), i < j → (breaks i).val ≺ (breaks j).val) ∧
      ∀ {α : Type} (d : TVal α) (t1 t2 : Time), t1.val ≼ t2.val →
        (¬ ∃ i : Fin (n + 1), (breaks i).val ∈ Set.Ioc t1.val t2.val) →
        interpValAt d t1 = interpValAt d t2

/-- The chosen number of shared ticks, extracted from `finitePartition` once via
`Classical.choose` -- every downstream definition (`next`, `changed`) is stated
against this one fixed choice, not a fresh existential each time. -/
noncomputable def tickCount : ℕ := finitePartition.choose

/-- The chosen shared tick instants themselves. -/
noncomputable def ticks : Fin (tickCount + 1) → Time := finitePartition.choose_spec.choose

theorem ticks_zero : ticks 0 = ⟨0, TIME_nonempty⟩ := finitePartition.choose_spec.choose_spec.1
theorem ticks_last : ticks (Fin.last tickCount) = ⟨now, dl_nowt⟩ :=
  finitePartition.choose_spec.choose_spec.2.1
theorem ticks_mono : ∀ i j : Fin (tickCount + 1), i < j → (ticks i).val ≺ (ticks j).val :=
  finitePartition.choose_spec.choose_spec.2.2.1

theorem ticks_mono_le {i j : Fin (tickCount + 1)} (h : i ≤ j) : (ticks i).val ≼ (ticks j).val := by
  rcases h.lt_or_eq with hlt | heq
  · exact (ticks_mono i j hlt).le
  · exact heq ▸ le_refl _

/-- The real content of `finitePartition`, restated against `ticks`: no change in
`d`'s value between `t1` and `t2` unless a shared tick falls strictly inside
`(t1,t2]`. -/
theorem ticks_constant {α : Type} (d : TVal α) {t1 t2 : Time} (h : t1.val ≼ t2.val)
    (hno : ¬ ∃ i : Fin (tickCount + 1), (ticks i).val ∈ Set.Ioc t1.val t2.val) :
    interpValAt d t1 = interpValAt d t2 :=
  finitePartition.choose_spec.choose_spec.2.2.2 d t1 t2 h hno

/-- `t` is one of the finitely many shared ticks. -/
def isTick (t : Time) : Prop := ∃ i : Fin (tickCount + 1), ticks i = t

/-- Every instant `t`'s `d`-value matches the `d`-value at the *largest* shared
tick `≤ t` (`t`'s "bucket anchor") -- `ticks 0 = 0` guarantees the candidate set is
always nonempty, so `Finset.max'` gives a real witness, and `ticks_constant`
(no tick strictly between the anchor and `t`, since the anchor is the *largest*
one `≤ t`) gives the constancy. -/
theorem ticks_bucket {α : Type} (d : TVal α) (t : Time) :
    ∃ j : Fin (tickCount + 1), (ticks j).val ≼ t.val ∧ d t = d (ticks j) := by
  classical
  set S : Finset (Fin (tickCount + 1)) := Finset.univ.filter (fun i => (ticks i).val ≼ t.val)
    with hSdef
  have hSne : S.Nonempty :=
    ⟨0, by simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and, ticks_zero]
           exact t.2.1⟩
  refine ⟨S.max' hSne, (Finset.mem_filter.mp (S.max'_mem hSne)).2, ?_⟩
  symm
  apply ticks_constant d (Finset.mem_filter.mp (S.max'_mem hSne)).2
  rintro ⟨i, hi1, hi2⟩
  have hiS : i ∈ S := by simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi2
  exact absurd (ticks_mono_le (S.le_max' i hiS)) (not_le.mpr hi1)

/-- Any `TVal α`-anchored predicate that's satisfiable somewhere has a *first*
instant where it holds, and that instant is always one of the finitely many
shared ticks -- unlike the retired `hasFirstInstant`, this is a real theorem, not
an axiom: `Time`'s dense order gives no well-ordering on its own, but
`finitePartition` means `P (d ·)` can only ever change value at a tick
(`ticks_bucket`), so a finite search over `Fin (tickCount + 1)` (`Finset.min'`)
suffices. Stated generically (not fixed to `existsAt A`) so it serves both `birth`
(`d := A`, `P := (· ≠ ∅)`) and `timeof` below (`d := φ`, `P := id`) without a
near-duplicate theorem for each. -/
theorem hasFirstTick {α : Type} (d : TVal α) (P : α → Prop) (h : ∃ s : Time, P (d s)) :
    ∃ τ, IsLeast {t : Time | P (d t)} τ := by
  classical
  have htick : ∃ i : Fin (tickCount + 1), P (d (ticks i)) := by
    obtain ⟨s, hs⟩ := h
    obtain ⟨j, _, hj⟩ := ticks_bucket d s
    exact ⟨j, hj ▸ hs⟩
  set T : Finset (Fin (tickCount + 1)) := Finset.univ.filter (fun i => P (d (ticks i)))
    with hTdef
  have hTne : T.Nonempty := by
    obtain ⟨i, hi⟩ := htick
    exact ⟨i, by simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi⟩
  set i0 := T.min' hTne with hi0def
  have hi0P : P (d (ticks i0)) := (Finset.mem_filter.mp (T.min'_mem hTne)).2
  refine ⟨ticks i0, hi0P, ?_⟩
  rintro t (ht : P (d t))
  by_contra hlt
  have hlt' : t.val ≺ (ticks i0).val := not_le.mp hlt
  obtain ⟨j, hjle, hjeq⟩ := ticks_bucket d t
  have hjP : P (d (ticks j)) := hjeq ▸ ht
  have hjT : j ∈ T := by simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and]; exact hjP
  exact absurd (ticks_mono_le (T.min'_le j hjT) |>.trans hjle) (not_le.mpr hlt')

/-- A total selector satisfying `birthIff`'s guarded spec exists for every
occurrence: `hasFirstTick`'s witness when `A` exists somewhere, `Time`'s own
`⟨now, dl_nowt⟩` (unconstrained junk, matching this file's own precedent for an
arbitrary-but-valid `Time` witness) otherwise. -/
theorem birth_exists (A : Occurrence) :
    ∃ t0 : Time, (∃ s, existsAt A s) →
      (existsAt A t0 ∧ ∀ t1 : Time, t1.val ∈ Set.Ico (0 : Instant) t0.val → ¬ existsAt A t1) := by
  by_cases h : ∃ s, existsAt A s
  · obtain ⟨τ, hτmem, hτlb⟩ := hasFirstTick A (· ≠ ∅) h
    refine ⟨τ, fun _ => ⟨hτmem, fun t1 ht1 hex1 => ?_⟩⟩
    exact absurd (hτlb hex1) (not_le.mpr ht1.2)
  · exact ⟨⟨now, dl_nowt⟩, fun hex => absurd hex h⟩

/-- SFS.mm `df-bl.timeof`'s own guarded existence, exactly `birth_exists`'s
argument with `existsAt A` replaced by `interpAt φ` -- the same structural shape
(`timeofIff` is `birthIff` with `interpAt φ` in place of `existsAt A`), so the same
proof, via the same generic `hasFirstTick`, carries over unchanged. -/
theorem timeof_exists (φ : TProp) :
    ∃ t1 : Time, (∃ s, interpAt φ s) →
      (interpAt φ t1 ∧ ∀ t : Time, t.val ∈ Set.Ico (0 : Instant) t1.val → ¬ interpAt φ t) := by
  by_cases h : ∃ s, interpAt φ s
  · obtain ⟨τ, hτmem, hτlb⟩ := hasFirstTick φ id h
    refine ⟨τ, fun _ => ⟨hτmem, fun t ht hφt => ?_⟩⟩
    exact absurd (hτlb hφt) (not_le.mpr ht.2)
  · exact ⟨⟨now, dl_nowt⟩, fun hφ => absurd hφ h⟩

/-- Existence set membership `t0 ∈ {t | existsAt A t}` together with "nothing
exists strictly after `t0`" is exactly `IsGreatest {t | existsAt A t} t0` -- the
bridge `death_exists` below uses in both directions. -/
theorem death_isGreatest_iff (A : Occurrence) (t0 : Time) :
    (existsAt A t0 ∧ ∀ t1 : Time, t1.val ∈ Set.Ioc t0.val now → ¬ existsAt A t1) ↔
      IsGreatest {t : Time | existsAt A t} t0 := by
  constructor
  · rintro ⟨hex, hno⟩
    refine ⟨hex, fun t1 ht1mem => ?_⟩
    by_contra hlt
    exact hno t1 ⟨not_le.mp hlt, t1.2.2⟩ ht1mem
  · rintro ⟨hex, hub⟩
    refine ⟨hex, fun t1 ht1 hex1 => absurd (hub hex1) (not_le.mpr ht1.1)⟩

/-- A total selector satisfying `deathIff`'s guarded spec exists for every
occurrence, `none` when no greatest existence instant exists -- pure classical
logic, *no* extra axiom needed (unlike `birth_exists`): `death_isGreatest_iff`
already hands the `some`-branch a witness satisfying `IsGreatest` directly, so no
well-ordering-style assumption about `Occurrence` is ever needed; uniqueness of
`IsGreatest` (`IsGreatest.unique`) gives uniqueness of the selected value. -/
theorem death_exists (A : Occurrence) :
    ∃ d : Option Time, ∀ t0 : Time, d = some t0 ↔
      (existsAt A t0 ∧ ∀ t1 : Time, t1.val ∈ Set.Ioc t0.val now → ¬ existsAt A t1) := by
  by_cases h : ∃ τ, IsGreatest {t : Time | existsAt A t} τ
  · obtain ⟨τ, hτ⟩ := h
    refine ⟨some τ, fun t0 => ?_⟩
    rw [death_isGreatest_iff A t0]
    constructor
    · intro heq; rw [Option.some.injEq] at heq; exact heq ▸ hτ
    · intro hg; exact congrArg some (hτ.unique hg)
  · refine ⟨none, fun t0 => ?_⟩
    rw [death_isGreatest_iff A t0]
    constructor
    · intro heq; exact absurd heq (by simp)
    · intro hg; exact absurd ⟨t0, hg⟩ h

/-- The consistency certificate: a real model, named so it can be audited
(`#print axioms model`) below -- exactly the construction that would be impossible
without `birthIff`/`deathIff`'s guards. A plain (not locally-scoped) `instance`, so
every downstream use of `birth`/`death`/`birthIff`/`deathIff` elsewhere in this
project resolves to it automatically, unchanged. -/
noncomputable instance model : Lifetimes where
  birth A := Classical.choose (birth_exists A)
  death A := Classical.choose (death_exists A)
  birthIff {A} {t0} h := by
    have spec := Classical.choose_spec (birth_exists A) h
    constructor
    · rintro rfl; exact spec
    · rintro ⟨hex, hno⟩
      have h1 : ¬ t0.val < (Classical.choose (birth_exists A)).val := fun hlt =>
        spec.2 t0 ⟨t0.2.1, hlt⟩ hex
      have h2 : ¬ (Classical.choose (birth_exists A)).val < t0.val := fun hlt =>
        hno (Classical.choose (birth_exists A)) ⟨(Classical.choose (birth_exists A)).2.1, hlt⟩ spec.1
      exact Subtype.ext (le_antisymm (not_lt.mp h1) (not_lt.mp h2))
  deathIff {A} {t0} := by
    have spec := Classical.choose_spec (death_exists A)
    exact spec t0
  timeof φ := Classical.choose (timeof_exists φ)
  timeofIff {φ} {t1} h := by
    have spec := Classical.choose_spec (timeof_exists φ) h
    constructor
    · rintro rfl; exact spec
    · rintro ⟨hφ, hno⟩
      have h1 : ¬ t1.val < (Classical.choose (timeof_exists φ)).val := fun hlt =>
        spec.2 t1 ⟨t1.2.1, hlt⟩ hφ
      have h2 : ¬ (Classical.choose (timeof_exists φ)).val < t1.val := fun hlt =>
        hno (Classical.choose (timeof_exists φ)) ⟨(Classical.choose (timeof_exists φ)).2.1, hlt⟩ spec.1
      exact Subtype.ext (le_antisymm (not_lt.mp h1) (not_lt.mp h2))

/- The audit (`Repaired.lean`'s own convention): `model` depends on Lean's standard
classical axioms plus exactly one new ingredient, `finitePartition` -- not for the
well-ordering `Repaired.lean`'s toy `ℕ` case got for free (dense `Time` still has
none), but because `hasFirstTick` (reused for both `birth` and `timeof`) needs
*some* structural fact ruling out an unattained infimum, and `finitePartition`'s
finite shared-tick structure is what supplies it (2026-08-26, retiring the earlier,
separately-axiomatized `hasFirstInstant`). -/
#print axioms model

/-- Strong Kleene conjunction on `Option Prop`, the general form of the ad hoc
"`some tA, some tB => some (...) | _, _ => none`" pattern this file used to repeat
per-predicate: unlike that pattern, `kand` *short-circuits* to `some False` when the
known operand is already false, even if the other is `none` -- matching real
three-valued (Kleene) `∧`, not merely "both defined or nothing." Needs `Classical`
(same as `nonoverlaps`'s pre-existing hand-rolled version below did) only to decide
which branch a `some`-wrapped `Prop` operand is in. -/
noncomputable def kand (p q : Option Prop) : Option Prop :=
  open Classical in
  match p, q with
  | some P, some Q => some (P ∧ Q)
  | some P, none => if P then none else some False
  | none, some Q => if Q then none else some False
  | none, none => none

/-- Strong Kleene disjunction on `Option Prop`, dual to `kand`: short-circuits to
`some True` when the known operand is already true. -/
noncomputable def kor (p q : Option Prop) : Option Prop :=
  open Classical in
  match p, q with
  | some P, some Q => some (P ∨ Q)
  | some P, none => if P then some True else none
  | none, some Q => if Q then some True else none
  | none, none => none

/-- Comparisons lifted through `Option Time`: `none` unless both operands are known
(there is nothing to short-circuit on for a bare order/equality atom -- the
short-circuiting happens one level up, in `kand`/`kor`). -/
noncomputable def klt (a b : Option Time) : Option Prop :=
  match a, b with | some a', some b' => some (a'.val ≺ b'.val) | _, _ => none
noncomputable def kle (a b : Option Time) : Option Prop :=
  match a, b with | some a', some b' => some (a'.val ≼ b'.val) | _, _ => none
noncomputable def keq (a b : Option Time) : Option Prop :=
  match a, b with | some a', some b' => some (a' = b') | _, _ => none

/-- SFS.mm `df-lifetime`, `Option`-valued: undefined (`none`) exactly when `death A`
is, i.e. for an ongoing occurrence -- matching `Occurrences::HappensDuring`-style KerML
constructs already requiring a definite `endShot`. -/
noncomputable def life (A : Occurrence) : Option (Set Instant) := (death A).map fun tA => Set.Icc (birth A).val tA.val

/-- SFS.mm `df-precedes`, `Option`-valued: needs only `A`'s death (`B`'s `endShot`,
if any, is irrelevant to whether `A` precedes `B`) -- `none` iff `death A = none`. -/
noncomputable def precedes (A B : Occurrence) : Option Prop := (death A).map fun tA => tA.val ≺ (birth B).val
/-- SFS.mm `df-meets`: needs only `A`'s death, same reasoning as `precedes`. -/
noncomputable def meets (A B : Occurrence) : Option Prop := (death A).map fun tA => tA = birth B
/-- SFS.mm `df-overlaps`: needs only `A`'s death, same reasoning as `precedes`. -/
noncomputable def overlaps (A B : Occurrence) : Option Prop := (death A).map fun tA => (birth B).val ≺ tA.val
/-- `Interval`'s boundary-openness features (`Domain.kerml`'s `openLeft`/`openRight`),
reused on `Occurrence` here since `Allen.kerml`'s own `starts`/`finishes`/`coincident`/
`nearlyMeets` all call them on `x`/`y : Occurrence`. Fresh primitives: nothing here
represented interval boundary openness before `df-nearlymeets` was added to `SFS.mm`.
Declared here, ahead of `starts` below (rather than immediately before `nearlyMeets`,
where they first appeared 2026-08-25), so `starts`/`finishes`/`coincident` can
reference them too. Class-based (2026-08-26), same batch/treatment as `Item` above
-- no characterizing law (nothing else constrains what `openLeft`/`openRight` say
about a given `Occurrence`), bundled together (like `Now`'s `now`/`now_nonneg` or
`BoolItems`' `trueItem`/`falseItem`) since they're declared and used as a pair,
though each is chosen independently. -/
class OpenBoundary where
  openLeft : Occurrence → Prop
  openRight : Occurrence → Prop
export OpenBoundary (openLeft openRight)
noncomputable instance openBoundaryModel : OpenBoundary :=
  ⟨Classical.choose (⟨fun _ => False, trivial⟩ : ∃ _ : Occurrence → Prop, True),
    Classical.choose (⟨fun _ => False, trivial⟩ : ∃ _ : Occurrence → Prop, True)⟩

/-- SFS.mm `df-starts`: compares `A`'s and `B`'s deaths directly, so needs both --
via `kand`/`klt`, which (unlike the old hand-rolled match) short-circuits to a
definite answer as soon as any known conjunct settles it, even if a death is
unknown. `openLeft A = openLeft B` (2026-08-26) matches `Allen.kerml`'s real
formula, which this definition had been missing -- both boundaries must agree
open/closed the same way for `starts` to hold. Nested `kand`s deliberately mirror
`Allen.kerml`'s own right-associative `and`-chain (`Assert.lean`'s `dslWff` grammar
parses `A and B and C` as `A and (B and C)`) rather than grouping the two
non-partial conjuncts together, so this is *literally*, not just logically, what
the real `@Assert` formula elaborates to -- see `Assert.lean`/`Kernel.lean`'s own
`example ... := rfl` checks. -/
noncomputable def starts (A B : Occurrence) : Option Prop :=
  kand (some (birth A = birth B)) (kand (klt (death B) (death A)) (some (openLeft A = openLeft B)))
/-- SFS.mm `df-during`: needs both, same reasoning as `starts`. -/
noncomputable def during (A B : Occurrence) : Option Prop :=
  kand (some ((birth B).val ≼ (birth A).val)) (kle (death A) (death B))
/-- SFS.mm `df-finishes`: needs both, same reasoning as `starts` -- `openRight A =
openRight B` (2026-08-26) matches `Allen.kerml`'s real formula, same fix and same
right-associative nesting as `starts` above. -/
noncomputable def finishes (A B : Occurrence) : Option Prop :=
  kand (some ((birth B).val ≺ (birth A).val)) (kand (keq (death A) (death B)) (some (openRight A = openRight B)))
/-- SFS.mm `df-coincident`: needs both, same reasoning as `starts` -- both boundary
conjuncts (2026-08-26), matching `Allen.kerml`'s real formula, same fix and nesting
as `starts`/`finishes` above; the trailing pair (`openLeft`/`openRight`, both
non-partial) combine via plain `∧`, matching how the DSL's own right-associative
parse bottoms out. -/
noncomputable def coincident (A B : Occurrence) : Option Prop :=
  kand (some (birth B = birth A))
    (kand (keq (death A) (death B)) (some (openLeft A = openLeft B ∧ openRight A = openRight B)))
/-- SFS.mm `df-nonoverlaps`: `death(x) < birth(y) ∨ death(y) < birth(x)`, i.e.
exactly `precedes A B ∨ precedes B A` -- `kor` gives the correct strong-Kleene
disjunction for free (a known-true disjunct wins even if the other occurrence
hasn't ended), replacing what used to be a bespoke hand-rolled `if`/`match` block
here. -/
noncomputable def nonoverlaps (A B : Occurrence) : Option Prop := kor (precedes A B) (precedes B A)

/- `finitePartition`/`tickCount`/`ticks`/`ticks_zero`/`ticks_last`/`ticks_mono`/
`ticks_constant`/`isTick` moved earlier (2026-08-26, at direct request), right
after `Lifetimes`'s own `export`, and `finitePartition` itself broadened from
`Occurrence`-only to every `TVal α` -- `birth_exists`/`timeof_exists` now build
directly on the tick structure (via `hasFirstTick`) instead of the separate
`hasFirstInstant` axiom, which is retired entirely. See that section for the
full doc comment. -/

/-- SFS.mm `df-next`: `t_2` immediately follows `t_1`. Redefined 2026-08-26 (was
"`t_1 ≺ t_2` and no `Time` value strictly between them," provably vacuous on
dense `ℝ` regardless of `t_1`/`t_2` -- see the retired `next_dense`) as "`t_1`,
`t_2` are both shared ticks, `t_1 ≺ t_2`, and no *other tick* lies strictly
between them" -- genuine successor-in-a-finite-set, not "no real number between,"
so no longer forced to be `False` for every input. -/
noncomputable def next (t1 t2 : Time) : Prop :=
  isTick t1 ∧ isTick t2 ∧ t1.val ≺ t2.val ∧
    ¬ ∃ x : Time, isTick x ∧ t1.val ≺ x.val ∧ x.val ≺ t2.val

/-- SFS.mm `bl.nexttp`. Free, `rfl`-adjacent, not an axiom -- unaffected by
`next`'s redesign, still just the third conjunct. -/
theorem next_tprec {t1 t2 : Time} (h : next t1 t2) : t1.val ≺ t2.val := h.2.2.1

/-- SFS.mm `bl.nextuniq`, genuinely reinstated (was vacuously true via the old,
now-retired `next_dense` before this redesign): if `t2` and `t3` are each the
tick immediately following `t1`, they're the same tick -- via `ticks_mono` and
linear-order trichotomy on their indices, whichever tick has the smaller index
turns out to be strictly between `t1` and the other, contradicting that other's
own "nothing between" clause. -/
theorem next_uniq {t1 t2 t3 : Time} (h2 : next t1 t2) (h3 : next t1 t3) : t2 = t3 := by
  obtain ⟨_, ⟨i2, hi2⟩, h12, hno2⟩ := h2
  obtain ⟨_, ⟨i3, hi3⟩, h13, hno3⟩ := h3
  rcases lt_trichotomy i2 i3 with hlt | heq | hgt
  · exact absurd ⟨t2, ⟨i2, hi2⟩, h12, hi2 ▸ hi3 ▸ ticks_mono i2 i3 hlt⟩ hno3
  · rw [← hi2, ← hi3, heq]
  · exact absurd ⟨t3, ⟨i3, hi3⟩, h13, hi3 ▸ hi2 ▸ ticks_mono i3 i2 hgt⟩ hno2

/-- SFS.mm `df-nearlymeets`. The `next (death A) (birth B)` disjunct is, before
2026-08-26's redesign, provably always `False` (`next` was vacuous on dense `ℝ`);
now genuinely possible whenever `death A`/`birth B` are consecutive shared ticks. -/
noncomputable def nearlyMeets (A B : Occurrence) : Option Prop :=
  (death A).map fun tA => (birth B = tA ∧ (openRight A ∨ openLeft B)) ∨ next tA (birth B)

-- The old `nearlyMeets_iff` (an unconditional collapse to just the open-boundary
-- disjunct, via `next_dense`'s vacuity) is retired along with `next_dense` itself:
-- the `next` disjunct is no longer dead weight, so there is no longer a genuine
-- simplification to state here -- unfolding the `def` above is the whole story.

/-! ### KerML Element Representation and Type Definition (SFS.mm lines 3246-3324) -/

/-- SFS.mm `cci`/`cuid`: `CI`/`UI` (Class Identifiers / Unique Identifiers) are both
described only as strings (a name, or a `::`-separated qualified name, or a
fully-qualified name concatenated with a "wonce") -- `abbrev`s over `String`, not fresh
opaque types, matching that description exactly rather than adding an unstated
constraint. -/
abbrev CI := String
abbrev UI := String

/-- SFS.mm `ctagb`/`cwonce`: the tag-boundary separator string and an unspecified wonce.
Both are left as opaque `String`-valued primitives here, exactly mirroring SFS.mm's own
`df-wonce`: neither SFS.mm's axiomatization nor the book's prose actually enforce
"freshness" (a new, distinct wonce each time) as part of the definition itself -- that's
an informal side condition on how `mkUid` gets *used*, not a fact `mkUid` itself proves.
Class-based, same batch/treatment as `Item` above. -/
def tb : String := "\\#"
class Wonce where
  wonce : String
export Wonce (wonce)
noncomputable instance wonceModel : Wonce :=
  ⟨Classical.choose (⟨"", trivial⟩ : ∃ _ : String, True)⟩

/-- SFS.mm `df-wonce`: creation of a Unique Identifier from a Class Identifier by
appending the tag-boundary and a wonce. -/
noncomputable def mkUid (ci : CI) : UI := ci ++ tb ++ wonce

/- The former `KElement` -- an opaque stand-in for "the universe of KerML elements a
design can contain" -- has been **replaced** (2026-08-20, full-replacement redesign) by
the real `KerML.Root.Element` metaclass from `Root.lean`/`Core.lean` (a from-spec
formalization of the actual OMG KerML metamodel, see the `[[project_kerml_metamodel_lean]]`
memory). Only `Element` itself is brought into scope unqualified below -- *not* the rest
of `KerML.Root`'s names (in particular not `Membership`, which would silently collide
with Mathlib's own `Membership` typeclass powering `∈` notation). Reference other
`Root`/`Core` names (`KerML.Core.KType`, etc.) fully qualified. -/
open KerML.Root (Element)

/- `ElementKind`/`DesignKind`/`Design`/`VT`/`Specializes`/`df_specializes`/
`df_multspec` moved to `Core.lean` 2026-08-21: they describe the KerML *model
representation* itself (which real metaclasses exist in a design, tagged and typed
against `Element`), so they belong alongside `Element`/`KType`/`Specialization` there
rather than across the import boundary -- the reverse direction is impossible
(`Core.lean` cannot import `SFS.lean`: `Kernel.lean` imports `Assert.lean` which
imports `SFS.lean`, so `SFS → Core` and `Core → SFS` together would close a cycle).
`isTypeDeclOf`/`df_types` below still need `Design`/`DesignKind`/`VT`, so they're
brought back in here; `ElementKind` is needed too, for `ElementRep` further down.
`df_types` itself also moved to `Core.lean` (2026-08-26, folded into its own
`CoreDesignModel` class alongside `Design`/`VT` -- see that class's doc comment),
since it needs the exact same treatment as `Core.lean`'s own `df_feature`/
`df_classifier` and `Design`/`VT` are shared, load-bearing primitives for a much
larger cluster there, not private to `df_types`; brought in here too. -/
open KerML.Core (ElementKind DesignKind Design VT df_types)

/-- SFS.mm `cID`: the class of identifiers (strings naming KerML elements -- previously
declared but unused in `SFS.mm` until `df-type` reused it). Kept as a plain `String`
alias for continuity with `SFS.mm`'s own `cID`, even though `Design`/`VT` (now in
`Core.lean`) hold real `Element`s rather than bare `ID`s -- `Element.declaredName :
Option String` plays `ID`'s role directly. -/
abbrev ID := String

/-- The Lean-level reading of concrete KerML text `"type A"`: a `Design` element tagged
`.type` whose `declaredName` is literally `A` -- the genuine syntax-to-`Design`
association `df-type`'s redesigns were chasing, now expressible because `Element`
(unlike the old bare `ID`) actually carries a `declaredName` field populated by KerML's
own grammar. -/
def isTypeDeclOf (A : ID) (e : Element) : Prop :=
  e.declaredName = some A ∧ ∃ C : Set Element, (DesignKind.type, e, C) ∈ Design

/-- The connection `isTypeDeclOf` was introduced for but never actually drawn: concrete
KerML text `"type A"` (`isTypeDeclOf A e`) really does put `e` in `VT`, via `df_types`
applied directly to `isTypeDeclOf`'s own second conjunct. -/
theorem isTypeDeclOf_mem_VT {A : ID} {e : Element} (h : isTypeDeclOf A e) : e ∈ VT :=
  df_types e h.2

/- SFS.mm `df-types`: for every `Element` `e`, if `e` is declared with the bare `type`
keyword (i.e. tagged `.type` in `Design`, the same reading `df-type` gives that text),
then `e ∈ VT`. Now a real theorem, not an axiom -- see `Core.lean`'s own
`CoreDesignModel`/`df_types`, opened in above alongside `Design`/`VT`. -/

/-- `Chapter/CoreSemanticsChapter.tex` §2.1.3 `df-rep` ("Representation of Elements as
Triples") -- book-only, like `Model` below: `df-rep` has no SFS.mm formalization, only
`df-kind` (translated as `Core.lean`'s `ElementKind`, opened above) and `df-wonce`
(translated as `mkUid` above, covering `id`'s `CI`/`UI` domain) do. Ontologically a
KerML element is *defined*
as a ZFC-class, but is *represented* as the triple `⟨k,id,C⟩`: `k` its `ElementKind`;
`id` its unique/qualified-name identifier -- typed here as plain `String` rather than
`UI` specifically, since `df-rep` itself doesn't commit to `id` always being a
freshly-`mkUid`-minted value (a plain named identifier, per `df-rep`'s own prose, is
just as valid); `C` the class the element defines (its extension: the `Element`s it
classifies/contains, the same "collection defined by a rule" reading `Model.E`'s doc
comment below uses for a KerML element treated as a class). This describes the *shape*
every `Element` has under `df-rep`, not a new type distinct from `Element` -- `Element`
itself is `Root.lean`'s real metaclass, unchanged here. -/
structure ElementRep where
  k : ElementKind
  id : String
  C : Set Element

/-! ## The dynamic architecture model 𝔐 (`df-model`, `Supplemental-Semantics`
`Chapter/KernelSemanticsChapter.tex`, *not* SFS.mm)

`df-model` has no Metamath formalization anywhere in SFS.mm (confirmed absent -- LaTeX-only),
so unlike everything above, it isn't part of the "translate SFS.mm" scope this file otherwise
sticks to. Added anyway, on request. `T` and `≺` are not separate fields of `Model` below: the
book states them as the first two components of the tuple, but this whole file already treats
`TIME`/`≺` as global, ambient primitives rather than something that varies per model (matching
how SFS.mm's own `ctime`/`wtp` are likewise bare, file-level constants, not parameters to
anything) -- a `Model` field for them would just rename what's already here. -/

/-- `df-model`'s tuple, `𝔐 ≡ ⟨T,≺,D,E,P,I⟩`, bundled as a `structure`. `D`/`E`/`P`/`I`
now range over `Root.lean`'s real `Element` (2026-08-20 full-replacement redesign;
formerly the opaque `KElement`). -/
structure Model where
  /-- `D`: a design expressed in KerML. -/
  D : Set Element
  /-- `E`: the KerML element selected to be modeled. The book states `E ∈ D` on first
  introduction, then immediately reinterprets `E` itself as a *class* ("`E` will be treated
  as a set theory class: a collection defined by a rule" -- "`E` may have many possible
  elements at time `τ`; interpretation picks just one"). The second reading is the one
  formalized here (`E ⊆ D`, not `E ∈ D`), since it's the one under which "interpretation
  picks one member of `E`" is meaningful at all; the first-stated `E ∈ D` is not separately
  restated as an axiom. -/
  E : Set Element
  E_sub_D : E ⊆ D
  /-- `P(τ)`: the system boundary at `τ` -- sensor/actuator input/output, in the sense of the
  Parnas four-variable model (named in the book itself). Unrelated to the `PartOf` Mereology
  primitive above despite the letter `P` in both. -/
  P : Time → Set Element
  /-- `I⟦d,τ⟧`: the interpretation of design element `d` at `τ`. Given a `Set Element` value
  at each instant, matching this file's own `Occurrence := TVal (Set Item)` convention for
  "the extent of a thing at a given time" (see the Allen's-Intervals section above) rather
  than inventing a differently-shaped codomain. -/
  I : Element → TVal (Set Element)

/-! ## Feature access (`Lean4SFS/Assert.lean` elaboration support, not an SFS.mm
translation)

`d::f` (KerML feature navigation) and the `I[[d::f,tau]]`/`I[[d::f]]`
interpretation-bracket notation used throughout `Domain.kerml`'s `Get`/`GetNow`/
`SetNow`/`GetChange` `@Assert` formulas have no SFS.mm formalization (confirmed
absent -- see the [[project_lean4sfs]] memory). `featureAccess`/`Get`/`GetC` are new
primitives added specifically so `Assert.lean`'s elaborator has something to translate
`I[[·::·,·]]` into; they are not translations of any existing SFS.mm axiom, the same
way `Model` above isn't. -/

/-- `d::f`: the feature `f` of occurrence `d`, itself an occurrence (KerML features
are themselves typed elements, so themselves `Occurrence`-shaped here). Class-based,
same batch/treatment as `Item` above. -/
class FeatureAccessFn where
  featureAccess : Occurrence → Element → Occurrence
export FeatureAccessFn (featureAccess)
noncomputable instance featureAccessModel : FeatureAccessFn :=
  ⟨Classical.choose (⟨fun _ _ => fun _ => ∅, trivial⟩ : ∃ _ : Occurrence → Element → Occurrence, True)⟩

/-- `I[[d::f,tau]]`: the value of feature `f` of `d` at `tau`. -/
def Get (d : Occurrence) (f : Element) (tau : Time) : Set Item := interpValAt (featureAccess d f) tau

/-- `I[[d::f]]`: the (untimed/constant) value of feature `f` of `d`. -/
def GetC (d : Occurrence) (f : Element) : Set Item := interpVal (featureAccess d f)

/-- The predicate-reading counterpart to `featureAccess` above, for `d::f` when `f`
is itself Boolean-valued (KerML's `BooleanEvaluation`, `Domain.kerml`'s own real
`GetBooleanChange`/`GetChangeToTrue`/`GetChangeToFalse` -- `I[[d::e,tau]]` used bare,
not compared against anything). `Item` is a fully opaque axiom (no internal
true/false structure), so there is no sound way to *derive* "this `Occurrence`
denotes true" from `featureAccess`'s `Set Item` result -- this is a genuinely new,
independently-axiomatized accessor, mirroring `featureAccess` exactly except its
codomain is `TProp` (a time-varying `Prop`) instead of `Occurrence` (a time-varying
`Set Item`), matching KerML's own `\S`3.13.1 distinction between class-expressions
(`A`, evaluated via `I[[·,·]]`/`Get`) and Boolean expressions/predicates (`φ`,
evaluated via this and `GetP` below) -- the same "class vs. wff" split `Assert.lean`'s
own `dslTerm`/`dslWff` categories already make, now given a real target on this side
too. Class-based, same batch/treatment as `Item` above. -/
class FeatureAccessPropFn where
  featureAccessProp : Occurrence → Element → TProp
export FeatureAccessPropFn (featureAccessProp)
noncomputable instance featureAccessPropModel : FeatureAccessPropFn :=
  ⟨Classical.choose
    (⟨fun _ _ => fun _ => False, trivial⟩ : ∃ _ : Occurrence → Element → TProp, True)⟩

/-- `I[[d::e,tau]]`, predicate reading: whether Boolean feature `e` of `d` holds at
`tau` -- `interpAt` (already used for `\S`3.13.1's `φ @ τ`) applied to
`featureAccessProp` the same way `Get` applies `interpValAt` to `featureAccess`. -/
def GetP (d : Occurrence) (f : Element) (tau : Time) : Prop := interpAt (featureAccessProp d f) tau

/-- `Domain.kerml`'s own `SetNow` behavior, formalized 2026-08-21 at direct request
("SetNow is crucial to SFS modal world semantics... formalize the interpretation
I[[...]] so that SetNow has the desired result"). Not a separate operational
primitive -- `SetNow d f v` *is* `Domain.kerml`'s own `SetNow` assertion
(`I[[d::f,now]] = v`) by definition, so this `def` adds no new axiomatic content;
it names the exact proposition the KerML behavior already asserts, so `Assert.lean`
elaborating that formula produces this term up to `rfl` (see its own smoke test).

**Why this already gives "the desired result" (worlds don't retroactively change,
only the current one is being set), with no extra persistence axiom needed**:
`Occurrence := Time → Set Item` is a pure, total function -- `Get d f t0` for any
instant `t0` is just that function applied to `t0`, a fixed value with no dependence
on *when* it's evaluated (Lean has no mutable state to make it otherwise).
`SetNow d f v` only constrains `Get d f now`, i.e. `featureAccess d f` applied to
*one specific* argument (`now`); it says nothing about `featureAccess d f` applied to
any other instant `t0 ≠ now`. So once `now` has advanced past some earlier `t0`,
`Get d f t0` is unaffected by anything asserted about `now` today, in either
direction -- not because some new axiom protects it, but because it was never a
function *of* `now` to begin with. Formalizing `SetNow` this way is what makes that
guarantee explicit and connects it to `Get`, not what creates it. -/
def SetNow (d : Occurrence) (f : Element) (v : Set Item) : Prop := Get d f ⟨now, dl_nowt⟩ = v

/-- `Domain.kerml`'s own `GetChange` behavior, formalized 2026-08-21 at direct
request, same treatment as `SetNow` immediately above: not a new primitive, just the
exact proposition `Domain.kerml`'s own `GetChange` assertion names -- "if the value
of `d::f` was stable at `Get d f tau` throughout `[tau, now)`, and has changed as of
`now`, then `v` is that new (changed) value." `t="df-bl.changed"` (the `@Assert`'s
citation) was previously left unupdated because no `SFS.lean` declaration existed to
cite; now one does. -/
def GetChange (d : Occurrence) (f : Element) (tau : Time) (v : Set Item) : Prop :=
  (Get d f tau ≠ Get d f ⟨now, dl_nowt⟩ ∧ ∀ t ∈ Set.Ico tau (⟨now, dl_nowt⟩ : Time), Get d f t = Get d f tau)
    → v = Get d f ⟨now, dl_nowt⟩

/-- `Domain.kerml`'s own `GetBooleanChange` behavior, formalized 2026-08-21 at direct
request. `GetBooleanChange`'s real KerML declaration (`behavior GetBooleanChange :>
GetChange`) genuinely specializes `GetChange` -- its own `@Assert` formula is
`GetChange`'s, verbatim, with `e`/`b` in place of `f`/`v` (still via `Get`'s value
reading, not `GetP`, despite `e~BooleanEvaluation` -- `GetChangeToTrue`/
`GetChangeToFalse`, which do use the predicate reading, come later and aren't this
declaration). Defined directly in terms of `GetChange` rather than repeating its body,
mirroring that same specialization at the Lean level, not just the KerML one. -/
def GetBooleanChange (d : Occurrence) (e : Element) (tau : Time) (b : Set Item) : Prop :=
  GetChange d e tau b

/-- Opaque canonical `Set Item` values standing for the Boolean literals `true`/
`false`, needed once `GetChangeToTrue`/`GetChangeToFalse` compare `b` (inherited as
`Set Item` from `GetBooleanChange`) against a literal -- `Item` is fully opaque, with
no internal true/false structure to derive these from. Class-based, same batch/
treatment as `Item` above -- bundled together (like `Now`'s `now`/`now_nonneg`)
since they're declared and used as a pair, though each is chosen independently
(there was never a `trueItem ≠ falseItem` axiom to preserve; the two `axiom`s
never ruled out coincidence either). -/
class BoolItems where
  trueItem : Set Item
  falseItem : Set Item
export BoolItems (trueItem falseItem)
noncomputable instance boolItemsModel : BoolItems :=
  ⟨Classical.choose (⟨∅, trivial⟩ : ∃ _ : Set Item, True),
    Classical.choose (⟨∅, trivial⟩ : ∃ _ : Set Item, True)⟩

/-- `Domain.kerml`'s own `GetChangeToTrue` behavior (`:> GetBooleanChange`). Uses
`GetP` (the predicate reading), not `Get`, since its own `@Assert` formula uses
`I[[d::e,tau]]` bare, not compared against anything -- matching `GetP`'s own doc note
that `GetChangeToTrue`/`GetChangeToFalse` are exactly the declarations that need it.
Does not wait if `d::e` is already true: unlike `GetBooleanChange`, there is no
"was stable, has changed" antecedent, just "holds now and didn't hold throughout
`[tau,now)`". -/
def GetChangeToTrue (d : Occurrence) (e : Element) (tau : Time) (b : Set Item) : Prop :=
  (GetP d e ⟨now, dl_nowt⟩ ∧ ∀ t ∈ Set.Ico tau (⟨now, dl_nowt⟩ : Time), ¬ GetP d e t)
    → b = trueItem

/-- `Domain.kerml`'s own `GetChangeToFalse` behavior, mirror of `GetChangeToTrue`. -/
def GetChangeToFalse (d : Occurrence) (e : Element) (tau : Time) (b : Set Item) : Prop :=
  (¬ GetP d e ⟨now, dl_nowt⟩ ∧ ∀ t ∈ Set.Ico tau (⟨now, dl_nowt⟩ : Time), GetP d e t)
    → b = falseItem

/-- `Chapter/KernelSemanticsChapter.tex` §3.1.5 `df-bl.changed`: redefined
2026-08-26 via `finitePartition`'s shared ticks, replacing the old unconditional
`axiom changed` + `changedIff` pair (which -- see the retired doc comment history
-- was close to vacuous for ordinary step-function `Occurrence`s: no `t2` ever
satisfied its three conditions jointly except when `t1` itself was a fresh
transition instant). `changed d t1` is now: among the ticks strictly before `t1`
where `d`'s value differs from `d t1`, take the greatest one (`Finset.max'` over a
finite, decidable set -- no infimum/supremum-of-a-continuum issue, unlike the old
formula's open-interval search), then report the *next* tick after it (the start
of `t1`'s own current, matching-`d t1` run); `0` if no such differing tick exists
(matching `df-bl.changed`'s own `t2=0` "hasn't changed before `t1`" case,
recovered here as a real consequence of the search coming up empty rather than a
separate disjunct). Total, no guard needed -- finiteness does all the work. -/
noncomputable def changed (d : Occurrence) (t1 : Time) : Time :=
  open Classical in
  let differing : Finset (Fin (tickCount + 1)) :=
    Finset.univ.filter fun i => (ticks i).val ≺ t1.val ∧ interpValAt d (ticks i) ≠ interpValAt d t1
  if h : differing.Nonempty then
    let i := differing.max' h
    if hlt : (i : ℕ) + 1 < tickCount + 1 then ticks ⟨i + 1, hlt⟩ else ⟨now, dl_nowt⟩
  else ⟨0, TIME_nonempty⟩

/-- Sanity check, not a full re-derivation of the old `changedIff`: if `d` never
differs from its own value at `t1` among any tick strictly before `t1`, `changed`
reports `0` -- `df-bl.changed`'s own "hasn't changed before `t1`" case, now a real
theorem rather than an axiomatized disjunct. -/
theorem changed_zero_of_no_diff {d : Occurrence} {t1 : Time}
    (h : ∀ i : Fin (tickCount + 1), (ticks i).val ≺ t1.val → interpValAt d (ticks i) = interpValAt d t1) :
    changed d t1 = ⟨0, TIME_nonempty⟩ := by
  unfold changed
  rw [dite_eq_right]
  simp only [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff]
  exact fun i _ hcond => hcond.2 (h i hcond.1)

/-! ## `Lean4SFS/Assert.lean` name-compatibility aliases

Real `@Assert{n="..."}` names in `sysml.library/**/*.kerml` use the full KerML
predicate name; this file's Mereology section, closer to `SFS.mm`'s own more compact
naming, dropped the `Part`/`Atomic` prefix for three of them. Aliased here (not
renamed above) so `Assert.lean`'s elaborator can resolve formula bodies that cite the
KerML name directly, without disturbing this file's own established names or their
citations elsewhere. `Location`'s own `@Assert` formula uses infix `L` on an
`Occurrence` subject -- the *argument-type* half of the old mismatch (`Location` was
`Part → Region → Prop`) is gone as of the 2026-08-21 `Part`-retirement above
(`Location : Occurrence → Region → Prop`), confirmed via a real build, but the
formula still fails for two independent, unrelated reasons: no `abbrev L :=
Location` exists (the infix operator name `L` itself is unresolved), and `LFU`/
`LIN`/`EXPNS`/`APAR` call `Location(x)` as a *one-argument* function, but `Location`
is a genuine *two-argument* relation here (same one-arg-vs-two-arg mismatch already
documented for `RegionSurface`/`RegionFilm`/`RegionInterior`) -- see `Assert.lean`'s
own note. -/

/-- SFS.mm/KerML's `PartOverlap`. -/
abbrev PartOverlap := Overlap
/-- SFS.mm/KerML's `PartUnderlap`. -/
abbrev PartUnderlap := Underlap
/-- SFS.mm/KerML's `AtomicPart`. -/
abbrev AtomicPart := AtomPart
/-- `Regions.kerml`'s `PointInRegion` predicate, same KerML-vs-SFS.mm naming mismatch
as the three above -- `SFS.mm`'s own primitive is `win`/`InRegion`. -/
abbrev PointInRegion := InRegion
/-- `Regions.kerml`'s `PointOnSurface` predicate; `SFS.mm`'s own primitive is
`won`/`OnSurface`. -/
abbrev PointOnSurface := OnSurface

end SFS
