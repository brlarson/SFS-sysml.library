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

/-- SFS.mm `cnow`/`df-bl.nowrr`: a fixed nonnegative real, the end of recorded time. -/
axiom now : ℝ
axiom now_nonneg : 0 ≤ now

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

/-! ### Mereology (SFS.mm lines 2726-2816) -/

axiom Part : Type

/-- SFS.mm `wpartof`: primitive. -/
axiom PartOf : Part → Part → Prop

/-- SFS.mm `df-par`: antireflexivity, a genuine constraint on the primitive. -/
axiom par (x : Part) : ¬ PartOf x x

/-- SFS.mm `df-ptr`: transitivity, a genuine constraint on the primitive. -/
axiom ptr {x y z : Part} : PartOf x y → PartOf y z → PartOf x z

/-- SFS.mm `df-pov`. -/
def Overlap (x y : Part) : Prop := ∃ z, PartOf z x ∧ PartOf z y

/-- SFS.mm `df-pun`. -/
def Underlap (x y : Part) : Prop := ∃ z, PartOf x z ∧ PartOf y z

/-- SFS.mm `df-pim`. -/
def ImproperPart (x y : Part) : Prop := PartOf x y ∨ x = y

/-- SFS.mm `df-pdj`. SFS.mm's own text reads `p_x Disjoint p_y <-> -. p_y Overlap
p_y` (self-overlap of `y`, not overlap of `x` and `y`) -- almost certainly a
transcription slip for `-. p_x Overlap p_y`, which is what is used here; flagged,
not corrected in SFS.mm itself. -/
def PartDisjoint (x y : Part) : Prop := ¬ Overlap x y

/-- SFS.mm `df-pch`: despite the `df-` name this doesn't define a new symbol -- it's
purely a constraint (any two parts are comparable, equal, or disjoint, and not
mutually part of each other) that is not derivable from `df-par`/`df-ptr` alone,
so, like those two, it stays an `axiom` rather than becoming a `def`. -/
axiom pch (x y : Part) :
    ((PartOf x y ∨ PartOf y x) ∨ (x = y ∨ PartDisjoint x y)) ∧ ¬ (PartOf x y ∧ PartOf y x)

/-- SFS.mm `df-pat`. -/
def AtomPart (x : Part) : Prop := ¬ ∃ z, PartOf z x

/-- SFS.mm `df-pwh`. -/
def WholePart (x : Part) : Prop := ∀ z, PartOf z x ∨ x = z

-- SFS.mm's `povrfl`/`punrfl`/`pimrfl`/`pdjrfl` are unproven placeholders (`$= ?`)
-- there too (see `reference_metamath_sfs_toolchain.md`'s baseline-placeholder list).
-- Three are, in fact, real theorems here, needing no axiom:
theorem povrfl (x y : Part) : Overlap x y ↔ Overlap y x :=
  exists_congr fun _ => and_comm
theorem punrfl (x y : Part) : Underlap x y ↔ Underlap y x :=
  exists_congr fun _ => and_comm
theorem pdjrfl (x y : Part) : PartDisjoint x y ↔ PartDisjoint y x := by
  unfold PartDisjoint; rw [povrfl]
-- `pimrfl` (`ImproperPart x y ↔ ImproperPart y x`, i.e. `PartOf x y ∨ x=y ↔
-- PartOf y x ∨ y=x`) is deliberately *not* translated: given only `df-par`
-- (antireflexive) and `df-ptr` (transitive) for `PartOf`, it is not provable, and
-- for any concrete antisymmetric part-of relation (the ordinary reading of
-- mereological parthood) it is false whenever `x` is a proper part of `y`.
-- Asserting it as an axiom would make the axiom set inconsistent with such a
-- model; SFS.mm itself leaves it as an unproven `$= ?`, never cited elsewhere.

/-! ### Region and Location (SFS.mm lines 2816-2962) -/

axiom Region : Type
axiom Point : Type
axiom Surface : Type

/-- SFS.mm `wloc`: primitive (relates a *part*, not a point, to a region). -/
axiom Location : Part → Region → Prop
/-- SFS.mm `win`: primitive. -/
axiom InRegion : Point → Region → Prop
/-- SFS.mm `won`: primitive. -/
axiom OnSurface : Point → Surface → Prop

/-- SFS.mm `df-lfu`: locational functionality, a genuine constraint on `Location`. -/
axiom lfu {x : Part} {r1 r2 : Region} : Location x r1 → Location x r2 → r1 = r2

/-- SFS.mm `df-lin`: injectivity of location, a genuine constraint on `Location`. -/
axiom lin {x y : Part} {r : Region} : Location x r → Location y r → x = y

/-- SFS.mm `df-rov`. -/
def RegionOverlap (r1 r2 : Region) : Prop := ∃ p, InRegion p r1 ∧ InRegion p r2

/-- SFS.mm `df-rco`. -/
def RegionContainment (r1 r2 : Region) : Prop := ∀ p, InRegion p r2 → InRegion p r1

/-- SFS.mm `df-rat`. -/
def AtomicRegion (r0 : Region) : Prop :=
  ∀ (x : Part) (r1 : Region), Location x r1 ∧ RegionContainment r0 r1 → r0 = r1

/-- SFS.mm `df-rdi`: a genuine constraint (atomic regions are disjoint or equal). -/
axiom rdi {r1 r2 : Region} : AtomicRegion r1 → AtomicRegion r2 → ¬ RegionOverlap r1 r2 ∨ r1 = r2

/-- SFS.mm `df-apar`: a genuine constraint (atomic parts have atomic regions). -/
axiom apar {x : Part} {r0 : Region} : Location x r0 → AtomPart x → AtomicRegion r0

/-- SFS.mm `df-pec`: expansivity, a genuine constraint tying `PartOf` to
`RegionContainment` via `Location`. -/
axiom expansivity {x y : Part} {r1 r2 : Region} :
    Location x r1 → Location y r2 → PartOf x y → RegionContainment r1 r2

/-- SFS.mm `df-rni`: no interpenetration, a genuine constraint. -/
axiom no_interpenetration {r1 r2 : Region} : RegionOverlap r1 r2 → RegionContainment r1 r2 ∨ RegionContainment r2 r1

/-- SFS.mm `df-rs`. SFS.mm's own text has a third conjunct `r_1 RegionSurface r_0`
in the body, self-referentially -- but with a *region* (`r_1`) plugged into
`RegionSurface`'s first (surface-typed) argument slot, which cannot be what was
intended (and `r_0`/`r_1` are already swapped relative to the rest of the clause).
Rather than guess a specific fix, that conjunct is dropped here (flagged, not
silently "corrected" to some particular reading); the definition below reflects
only the two conjuncts whose meaning is unambiguous. Defined before
`RegionInterior` so the latter can cite it directly, unlike SFS.mm's own order. -/
def RegionSurface (s : Surface) (r0 : Region) : Prop :=
  ∃ r1 : Region, ∀ p, OnSurface p s → InRegion p r0 ∧ ¬ InRegion p r1

/-- SFS.mm `df-ri`. -/
def RegionInterior (r1 r2 : Region) : Prop :=
  ∃ s : Surface, ∀ p, InRegion p r1 → InRegion p r2 ∧ ¬ OnSurface p s ∧ RegionSurface s r2

/-- SFS.mm `df-rf`. -/
def RegionFilm (s : Surface) (r0 : Region) : Prop := ∃ r1, RegionInterior r0 r1 ∧ RegionSurface s r1

/-- SFS.mm `df-exc`. -/
def ExternallyConnected (r1 r2 : Region) : Prop :=
  ∃ (s1 s2 : Surface) (p : Point), (RegionSurface s1 r1 ∧ RegionSurface s2 r2) ∧ OnSurface p s1 ∧ OnSurface p s2

/-- SFS.mm `df-flmc`. -/
def FilmConnected (r1 r2 : Region) : Prop :=
  ∃ (s1 s2 : Surface) (p : Point), (RegionFilm s1 r1 ∧ RegionFilm s2 r2) ∧ OnSurface p s1 ∧ OnSurface p s2

/-! ### Time -- Allen's Intervals (SFS.mm lines 2962-3117) -/

/-- Carrier for what an occurrence's temporal extent is a set *of*; SFS.mm leaves
this fully generic (its `A` is an unconstrained class). -/
axiom Item : Type

/-- SFS.mm's implicit type for `A` in `exists`/`birth`/`death`/Allen's-relations: a
temporal value whose extent, at each instant, is a set of `Item`s (empty = doesn't
exist then). Reuses the real `TVal`/`interpValAt` machinery from the BLESS-logic
section above rather than re-axiomatizing evaluation-at-an-instant. -/
abbrev Occurrence := TVal (Set Item)

/-- SFS.mm `df-exists`. A genuine `def`, not an axiom: already fully determined by
`interpValAt`. -/
def existsAt (A : Occurrence) (t0 : Time) : Prop := interpValAt A t0 ≠ ∅

/-- SFS.mm `birth`: primitive (no construction of "the first instant `A` exists" is
given, only the characterizing property `df-birth` below). Returns `Time`, not bare
`Instant`: an occurrence's birth is itself one of the instants under discussion. -/
axiom birth : Occurrence → Time
/-- SFS.mm `death`: primitive. -/
axiom death : Occurrence → Time

/-- SFS.mm `df-birth`. SFS.mm's own text quantifies `A. t_1 e. (0[,)t_0) -.
exists(A,t_0)` -- reusing the outer `t_0` inside the body instead of the bound
`t_1` -- almost certainly a transcription slip; read here with `t_1`, matching
`df-death`'s own (correct) shape immediately below. -/
axiom birthIff {A : Occurrence} {t0 : Time} :
    birth A = t0 ↔ existsAt A t0 ∧ ∀ t1 : Time, t1.val ∈ Set.Ico (0 : Instant) t0.val → ¬ existsAt A t1

/-- SFS.mm `df-death`. -/
axiom deathIff {A : Occurrence} {t0 : Time} :
    death A = t0 ↔ existsAt A t0 ∧ ∀ t1 : Time, t1.val ∈ Set.Ioc t0.val now → ¬ existsAt A t1

/-- SFS.mm `df-lifetime`. -/
def life (A : Occurrence) : Set Instant := Set.Icc (birth A).val (death A).val

/-- SFS.mm `df-precedes`. -/
def precedes (A B : Occurrence) : Prop := (death A).val ≺ (birth B).val
/-- SFS.mm `df-meets`. -/
def meets (A B : Occurrence) : Prop := death A = birth B
/-- SFS.mm `df-overlaps`. -/
def overlaps (A B : Occurrence) : Prop := (birth B).val ≺ (death A).val
/-- SFS.mm `df-starts`. -/
def starts (A B : Occurrence) : Prop := birth A = birth B ∧ (death B).val ≺ (death A).val
/-- SFS.mm `df-during`. -/
def during (A B : Occurrence) : Prop := (birth B).val ≼ (birth A).val ∧ (death A).val ≼ (death B).val
/-- SFS.mm `df-finishes`. -/
def finishes (A B : Occurrence) : Prop := (birth B).val ≺ (birth A).val ∧ death A = death B
/-- SFS.mm `df-coincident`. -/
def coincident (A B : Occurrence) : Prop := birth A = birth B ∧ death A = death B
/-- SFS.mm `df-nonoverlaps`. -/
def nonoverlaps (A B : Occurrence) : Prop := (death A).val ≺ (birth B).val ∨ (death B).val ≺ (birth A).val

/-- SFS.mm `df-next`: `t_2` immediately follows `t_1`, no instant strictly between.
A genuine `def` over the real `≺` (SFS.mm needed `bl.tpeq1`/`bl.tpeq2` as extra
axioms to make this usable in a real Metamath proof, since its `wtp` is a bare
primitive there -- moot here, `tprec_congr1`/`tprec_congr2` above are free). -/
def next (t1 t2 : Time) : Prop := t1.val ≺ t2.val ∧ ¬ ∃ x : Time, t1.val ≺ x.val ∧ x.val ≺ t2.val

/-- SFS.mm `bl.nexttp`. Free, `rfl`-adjacent, not an axiom. -/
theorem next_tprec {t1 t2 : Time} (h : next t1 t2) : t1.val ≺ t2.val := h.1

/-- SFS.mm `bl.nextdense`, and simultaneously the direct resolution -- via ordinary
real-number density -- of the exact `bl.nlt1`-`bl.nlt7`/`ASSIGN`-unification
blocker documented in `reference_metamath_sfs_toolchain.md`: `next` is *vacuous* on
`ℝ`, full stop. The midpoint of `t1.val` and `t2.val` is the witness; it's a genuine
`Time` (not just an `Instant`) because `TIME` is convex -- `t1.val ≥ 0` and
`t2.val ≤ now` bound it into `[0,now]` too. -/
theorem next_dense (t1 t2 : Time) : ¬ next t1 t2 := by
  rintro ⟨h12, hno⟩
  replace h12 : t1.val < t2.val := h12
  have hm1 : t1.val < (t1.val + t2.val) / 2 := by linarith
  have hm2 : (t1.val + t2.val) / 2 < t2.val := by linarith
  have hmT : (t1.val + t2.val) / 2 ∈ TIME := ⟨by linarith [t1.2.1], by linarith [t2.2.2]⟩
  exact hno ⟨⟨(t1.val + t2.val) / 2, hmT⟩, hm1, hm2⟩

/-- SFS.mm `bl.nextuniq`. Vacuously true, via `next_dense`, in one line -- the
uniqueness question dissolves once existence is known to fail on unrestricted
dense time (matching the book's own remark that `next` "only does real work when
applied to instant pairs known not to be dense with each other"). -/
theorem next_uniq {t1 t2 t3 : Time} (h : next t1 t2) : t2 = t3 := absurd h (next_dense t1 t2)

-- SFS.mm `bl.nextev`/`bl.nextwit` (helper lemmas witnessing the "no instant between"
-- clause of `df-next`, needed in the Metamath development to route around `wtp` not
-- being `wbr`-based) are subsumed by `next_dense`: since `next` is uniformly false
-- here, nothing downstream ever needs their witnessing content.

/-! ### KerML Element Representation and Type Definition (SFS.mm lines 3246-3324) -/

/-- SFS.mm `df-kind`: a set of 14 pairwise-distinct constants. The natural Lean
counterpart of "these are new, pairwise-distinct atomic constants" is an
`inductive` enum (constructor-distinctness is free), not an `axiom`. -/
inductive ElementKind
  | Element | Relationship | Dependency | Feature | Classifier | DataType | Class
  | Structure | Association | Connector | Behavior | Function | Expression | Interaction
  deriving DecidableEq, Repr

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
an informal side condition on how `mkUid` gets *used*, not a fact `mkUid` itself proves. -/
def tb : String := "\\#"
axiom wonce : String

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

/-- SFS.mm `cID`: the class of identifiers (strings naming KerML elements -- previously
declared but unused in `SFS.mm` until `df-type` reused it). Kept as a plain `String`
alias for continuity with `SFS.mm`'s own `cID`, even though `Design`/`VT` below now hold
real `Element`s rather than bare `ID`s -- `Element.declaredName : Option String` plays
`ID`'s role directly. -/
abbrev ID := String

/-- SFS.mm `cType`/`cDesign`, `df-type`. `df-type` went through three designs in one
session (see `[[reference_supplemental_semantics_book]]`'s and
`[[project_kerml_metamodel_lean]]`'s memory for the full history): an opaque `Denote`
function (rejected, still just a stand-in); a `Design : Set (DesignKind × ID × Set
KElement)` triple tying KerML text to `df-rep`'s own shape (an improvement, but `ID`
was still a bare, structurally-arbitrary string, not connected to anything KerML's own
grammar actually populates); and now, with `Root.lean`/`Core.lean` available, this
**full replacement**: `Design` holds real `KerML.Root.Element` values, whose
`declaredName` field is populated directly by KerML's own `Identification` concrete-
syntax rule (`TypeDeclaration → declaredName = NAME`) -- so "type A" can now be read as
`isTypeDeclOf A e` below for a real `e : Element`, not an arbitrary tag. `DesignKind` is
a fresh sum type (not `ElementKind`) because a `Design` triple's kind slot must hold
*either* one of `ElementKind`'s 14 tags *or* `Type`, and `Type` is deliberately excluded
from `ElementKind` itself (matching the book's own KerML §8.4.3.2 distinction, see
`ElementKind`'s doc comment).

Unlike SFS.mm's own `df-type`, which has to separately assert `C e. _V` (a genuine set,
not an undefined/proper-class value -- not automatic in ZFC) given the triple-membership
premise, **no such assertion is needed or possible here**: `Set Element` already
guarantees `C` is a real value for every triple in `Design`, the same reason `dl_al`
above needed no `ralv`-style bridging step -- there is no "proper class" for `Design`'s
membership type to accidentally admit. -/
inductive DesignKind
  | ofElementKind (k : ElementKind)
  | type

axiom Design : Set (DesignKind × Element × Set Element)

/-- The Lean-level reading of concrete KerML text `"type A"`: a `Design` element tagged
`.type` whose `declaredName` is literally `A` -- the genuine syntax-to-`Design`
association `df-type`'s redesigns were chasing, now expressible because `Element`
(unlike the old bare `ID`) actually carries a `declaredName` field populated by KerML's
own grammar. -/
def isTypeDeclOf (A : ID) (e : Element) : Prop :=
  e.declaredName = some A ∧ ∃ C : Set Element, (DesignKind.type, e, C) ∈ Design

/-- SFS.mm `cVT`: `V_T`, the set of all Types in the design (KerML Core Semantics
§2.1.1's vocabulary triple `⟨V_T,V_C,V_F⟩`) -- a primitive `df-types` *constrains*
rather than fully defines, matching `SFS.mm`'s own implication (not equation) form, so
this stays an `axiom` rather than a derived `def`, unlike `Denote`/`mkUid` above. Now
`Set Element` (holding the actual design elements), not `Set ID`, matching `Design`'s
own full-replacement redesign above. -/
axiom VT : Set Element

/-- SFS.mm `df-types`: for every `Element` `e`, if `e` is declared with the bare `type`
keyword (i.e. tagged `.type` in `Design`, the same reading `df-type` gives that text),
then `e ∈ VT`. This genuinely needs to stay an axiom here too -- `VT` is independently
primitive on both sides, so there's no automatic Lean-typing shortcut this time. -/
axiom df_types : ∀ e : Element, (∃ C : Set Element, (DesignKind.type, e, C) ∈ Design) → e ∈ VT

/-- `Chapter/CoreSemanticsChapter.tex` §2.1.3 `df-rep` ("Representation of Elements as
Triples") -- book-only, like `Model` below: `df-rep` has no SFS.mm formalization, only
`df-kind` (translated as `ElementKind` above) and `df-wonce` (translated as `mkUid`
above, covering `id`'s `CI`/`UI` domain) do. Ontologically a KerML element is *defined*
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
are themselves typed elements, so themselves `Occurrence`-shaped here). -/
axiom featureAccess : Occurrence → Element → Occurrence

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
too. -/
axiom featureAccessProp : Occurrence → Element → TProp

/-- `I[[d::e,tau]]`, predicate reading: whether Boolean feature `e` of `d` holds at
`tau` -- `interpAt` (already used for `\S`3.13.1's `φ @ τ`) applied to
`featureAccessProp` the same way `Get` applies `interpValAt` to `featureAccess`. -/
def GetP (d : Occurrence) (f : Element) (tau : Time) : Prop := interpAt (featureAccessProp d f) tau

/-! ## `Lean4SFS/Assert.lean` name-compatibility aliases

Real `@Assert{n="..."}` names in `sysml.library/**/*.kerml` use the full KerML
predicate name; this file's Mereology section, closer to `SFS.mm`'s own more compact
naming, dropped the `Part`/`Atomic` prefix for three of them. Aliased here (not
renamed above) so `Assert.lean`'s elaborator can resolve formula bodies that cite the
KerML name directly, without disturbing this file's own established names or their
citations elsewhere. Not every such mismatch gets an alias -- `Location`'s own
`@Assert` formula uses infix `L` on an `Occurrence` subject, but `SFS.lean`'s
`Location : Part → Region → Prop` takes a different argument type entirely, so no
alias would make it type-check; see `Assert.lean`'s own note on that one. -/

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
