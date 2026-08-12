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
operator, only *one direction* is valid for `∨`/`→`/`↔`/`∃` in general (classic
K-axiom asymmetry). SFS.mm nonetheless states `df-bl.or`, `df-bl.im`, `df-bl.bi`,
and (via `bl.dfrex2`) `bl.ex` as full, unconditional biconditionals. Below, each of
these is witnessed by a two-instant counterexample showing the "extra" direction is
false in general, so only the sound direction is proved -- this file does not
axiomatize the unsound direction. This is the same character of issue as the
pre-existing `df-exc`/`df-flmc` class-typed-existential bug documented in
`reference_metamath_sfs_toolchain.md`: a `$a` axiom that doesn't survive contact with
a concrete model. Not in scope to fix in SFS.mm itself here.
-/
import Mathlib

namespace SFS

/-! ## Time (SFS.mm lines 1002-1099) -/

/-- SFS.mm `cnow`/`df-bl.nowrr`: a fixed nonnegative real, the end of recorded time. -/
axiom now : ℝ
axiom now_nonneg : 0 ≤ now

abbrev Instant := ℝ

/-- SFS.mm `ctime`/`df-bl.time`. -/
def TIME : Set Instant := Set.Icc 0 now

theorem TIME_nonempty : (0 : Instant) ∈ TIME := ⟨le_refl 0, now_nonneg⟩

/-- SFS.mm `wtp`/`df-bl.before`: temporal precedence, defined directly as `<` on all
of `ℝ` rather than only characterized on `TIME`. Consequently its Leibniz congruence
(`bl.tpeq1`/`bl.tpeq2` in SFS.mm -- needed there as *extra axioms* because `wtp` is a
bare primitive, not built via the generic `wbr` relation mechanism `breq1`/`breq2`
apply to) is just `congrArg`, free of charge; see [[reference_metamath_sfs_toolchain]]
for why that mattered in the Metamath development. -/
def tprec (t1 t2 : Instant) : Prop := t1 < t2
infix:50 " ≺ " => tprec

/-- SFS.mm `df-bl.before`. -/
theorem df_bl_before {t1 t2 : Instant} (_ : t1 ∈ TIME) (_ : t2 ∈ TIME) :
    (t1 ≺ t2) ↔ t1 < t2 := Iff.rfl

/-- SFS.mm `bl.tpeq1`, free (`congrArg (· ≺ _)`), not an axiom here. -/
theorem tprec_congr1 {A B : Instant} (h : A = B) (C : Instant) : (A ≺ C) ↔ (B ≺ C) := h ▸ Iff.rfl

/-- SFS.mm `bl.tpeq2`, free. -/
theorem tprec_congr2 {A B : Instant} (h : A = B) (C : Instant) : (C ≺ A) ↔ (C ≺ B) := h ▸ Iff.rfl

/-- SFS.mm `wtpe`/`df-bl.beforeeq`. -/
def tprecEq (t1 t2 : Instant) : Prop := t1 ≤ t2
infix:50 " ≼ " => tprecEq

theorem df_bl_beforeeq {t1 t2 : Instant} (_ : t1 ∈ TIME) (_ : t2 ∈ TIME) :
    (t1 ≼ t2) ↔ (t1 < t2 ∨ t1 = t2) := le_iff_lt_or_eq

/-! ## Temporal values and predicates (SFS.mm lines 1177-1560, "BLESS LOGIC MODELS") -/

/-- A BLESS-logic temporal value: what SFS.mm's `A` denotes when read as varying
with the world/instant -- one plain value per instant. -/
abbrev TVal (α : Type*) := Instant → α

/-- A BLESS-logic temporal predicate: SFS.mm's `ph`, read as a function from instants
to truth values rather than an opaque schema letter, so every "interpretation
distributes over connective X" fact below is an ordinary fact about pointwise-defined
functions. -/
abbrev TProp := Instant → Prop

/-- SFS.mm `wboldit`, i.e. `boldI [[ ph , t_0 ]]`: interpretation at a specific
instant. Definitionally just application, since `TProp` already *is* "value at each
instant". -/
def interpAt (φ : TProp) (t0 : Instant) : Prop := φ t0

/-- SFS.mm `wboldi`, i.e. `boldI [[ ph ]]`: untimed/"always" interpretation -- `φ`
holds at every instant (the modal `□`, matching SFS.mm's own gloss "Tautologies are
expressed as `boldI [[ ph ]]`"). -/
def interp (φ : TProp) : Prop := ∀ t, φ t

/-- SFS.mm `ax-bl.taut`. Provable here, not axiomatized: a plain (non-temporal)
Metamath wff `ph`, embedded as a `TProp` via the constant function, is trivially
`interp`-true once any instant exists. -/
theorem ax_bl_taut {p : Prop} : p → interp (fun (_ : Instant) => p) := fun h _ => h

/-- SFS.mm `ax-bl.models`. -/
theorem ax_bl_models {φ : TProp} {t0 : Instant} (_ : t0 ∈ TIME) :
    interp φ → interpAt φ t0 := fun h => h t0

/-- SFS.mm `wboldic`/`wboldict`: untimed and timed interpretation of *values*.
Timed is again literal evaluation; untimed is anchored at instant `0` (`0 ∈ TIME` via
`TIME_nonempty`). Unlike predicate-`interp` this is not a `∀`-aggregation, so it
commutes with every pointwise-defined value operator unconditionally (see
`interpVal_add` etc. below) -- SFS.mm's `ax-bl.modelsc` (only meaningful when `A`
is actually constant) is not restated as an axiom since it is not needed to make any
of the value-side distribution facts below provable. -/
def interpValAt {α} (A : TVal α) (t0 : Instant) : α := A t0
def interpVal {α} (A : TVal α) : α := A 0

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
example (φ ψ : TProp) (t0 : Instant) : interpAt (φ ∧ₜ ψ) t0 ↔ (interpAt φ t0 ∧ interpAt ψ t0) := Iff.rfl
example (φ ψ : TProp) (t0 : Instant) : interpAt (φ ∨ₜ ψ) t0 ↔ (interpAt φ t0 ∨ interpAt ψ t0) := Iff.rfl
example (φ ψ : TProp) (t0 : Instant) : interpAt (φ →ₜ ψ) t0 ↔ (interpAt φ t0 → interpAt ψ t0) := Iff.rfl
example (φ ψ : TProp) (t0 : Instant) : interpAt (φ ↔ₜ ψ) t0 ↔ (interpAt φ t0 ↔ interpAt ψ t0) := Iff.rfl
example (φ : TProp) (t0 : Instant) : interpAt (¬ₜφ) t0 ↔ ¬ interpAt φ t0 := Iff.rfl

/-- SFS.mm `df-bl.an` (untimed). Sound: `□` distributes over `∧` (`forall_and`). -/
theorem df_bl_an (φ ψ : TProp) : interp (φ ∧ₜ ψ) ↔ (interp φ ∧ interp ψ) := forall_and

/-- SFS.mm `df-bl.al` (untimed universal quantification exportation). Sound: swapping
two `∀`s is always valid. -/
theorem df_bl_al {D : Type*} (φ : D → TProp) : interp (fun t => ∀ x, φ x t) ↔ ∀ x, interp (φ x) :=
  forall_comm

/-- SFS.mm `df-bl.or` (untimed), sound direction only. The converse
(`interp (φ ∨ₜ ψ) → interp φ ∨ interp ψ`) is **false** in general: witnessed on
`TIME` as soon as it has two distinct instants `t1 ≠ t2` by `φ := (· = t1)`,
`ψ := (· = t2)` -- `φ ∨ₜ ψ` holds at every instant in `{t1, t2}` but neither disjunct
holds at both, so `interp (φ ∨ₜ ψ)` restricted to `{t1,t2}` would hold while
`interp φ ∨ interp ψ` fails. SFS.mm's `df-bl.or` states the full (unsound)
biconditional; not restated here. See the file-level doc comment. -/
theorem bl_or_sound (φ ψ : TProp) : (interp φ ∨ interp ψ) → interp (φ ∨ₜ ψ) := by
  rintro (h | h) t
  · exact Or.inl (h t)
  · exact Or.inr (h t)

-- Witness that the converse of `df-bl.or` (untimed) is not derivable: two instants
-- `0 ≠ 1`, `φ` true only at `0`, `ψ` true only at `1`. `φ ∨ₜ ψ` is a tautology on
-- `{0,1}` but neither `φ` nor `ψ` alone is.
example : ∀ t ∈ ({0, 1} : Set Instant), ((fun t : Instant => t = 0) ∨ₜ (fun t : Instant => t = 1)) t := by
  rintro t (rfl | rfl) <;> simp [tor]

example : ¬ ∀ t ∈ ({0, 1} : Set Instant), (fun t : Instant => t = 0) t := by
  intro h; have := h 1 (by simp); simp at this

example : ¬ ∀ t ∈ ({0, 1} : Set Instant), (fun t : Instant => t = 1) t := by
  intro h; have := h 0 (by simp); simp at this

/-- SFS.mm `df-bl.im` (untimed), sound direction only (the modal K-axiom shape). The
converse fails by the same two-instant shape as `df-bl.or` (take `ψ := fun _ => False`
so `φ →ₜ ψ` becomes `¬ₜφ`, reducing to the `∨`/`¬` case). Not restated as an axiom;
see the file-level doc comment. -/
theorem bl_im_sound (φ ψ : TProp) : interp (φ →ₜ ψ) → (interp φ → interp ψ) :=
  fun h hφ t => h t (hφ t)

/-- SFS.mm `bl.dfrex2`/`bl.ex` (untimed existential exportation), sound direction
only. The converse (`interp (fun t => ∃ x, φ x t) → ∃ x, interp (φ x)`) is the classic
invalid `∀∃`-to-`∃∀` swap: different instants may need different witnesses. Not
restated as an axiom; see the file-level doc comment. -/
theorem bl_ex_sound {D : Type*} (φ : D → TProp) :
    (∃ x, interp (φ x)) → interp (fun t => ∃ x, φ x t) :=
  fun ⟨x, hx⟩ t => ⟨x, hx t⟩

/-! ### Value-level operators (SFS.mm's arithmetic `boldI`-distribution sections) -/

/-- SFS.mm `df-bl.addt`/`df-bl.add` and all analogous `-`/`×`/`÷`/`-u` timed *and*
untimed distribution axioms: all `rfl`. `interpVal`/`interpValAt` are point
evaluation (at `0`, resp. `t0`) of ordinary Mathlib `Pi`-instance pointwise
arithmetic on `Instant → ℝ`, and point evaluation always commutes with pointwise
operators -- no constancy assumption needed, unlike the predicate case above. -/
example (A B : TVal ℝ) (t0 : Instant) : interpValAt (A + B) t0 = interpValAt A t0 + interpValAt B t0 := rfl
example (A B : TVal ℝ) : interpVal (A + B) = interpVal A + interpVal B := rfl
example (A B : TVal ℝ) (t0 : Instant) : interpValAt (A - B) t0 = interpValAt A t0 - interpValAt B t0 := rfl
example (A B : TVal ℝ) (t0 : Instant) : interpValAt (A * B) t0 = interpValAt A t0 * interpValAt B t0 := rfl
example (A B : TVal ℝ) (t0 : Instant) : interpValAt (A / B) t0 = interpValAt A t0 / interpValAt B t0 := rfl
example (A : TVal ℝ) (t0 : Instant) : interpValAt (-A) t0 = -interpValAt A t0 := rfl

/-- SFS.mm `df-bl.eq`/`df-bl.lt`/`df-bl.am` and their timed counterparts: relations
between temporal values, lifted pointwise the same way. -/
def teq (A B : TVal ℝ) : TProp := fun t => A t = B t
def tlt (A B : TVal ℝ) : TProp := fun t => A t < B t
def tle (A B : TVal ℝ) : TProp := fun t => A t ≤ B t

example (A B : TVal ℝ) (t0 : Instant) : interpAt (teq A B) t0 ↔ interpValAt A t0 = interpValAt B t0 := Iff.rfl
example (A B : TVal ℝ) (t0 : Instant) : interpAt (tlt A B) t0 ↔ interpValAt A t0 < interpValAt B t0 := Iff.rfl
example (A B : TVal ℝ) (t0 : Instant) : interpAt (tle A B) t0 ↔ interpValAt A t0 ≤ interpValAt B t0 := Iff.rfl

/-! ## The `@` operator (SFS.mm lines 1560-2067) -/

/-- SFS.mm `wat`/`clat0`, i.e. `(ph @ t_0)`/`(A @ t_0)`: evaluate at `t0`, freezing
the result into a *constant* temporal predicate/value (so it can validly be `@`'d
again, matching `df-bl.at2`'s "double `@` is inconsequential"). Because the result is
constant, `@` distributing over any pointwise-defined connective or operator is `rfl`
-- this one construction subsumes SFS.mm's entire "Distribute Temporal Operator @"
section (`bl.atan2i`/`bl.atan3i`/`bl.atan3ri`/`bl.atan3li`/`bl.ator2i`/... and their
value/arithmetic analogues, ~100 theorems), for arbitrary composition depth, not just
the specific two- or three-term/left/right shapes SFS.mm had to spell out one by one. -/
def atP (φ : TProp) (t0 : Instant) : TProp := fun _ => φ t0
def atC {α} (A : TVal α) (t0 : Instant) : TVal α := fun _ => A t0

/-- SFS.mm `df-bl.at`. -/
theorem df_bl_at (φ : TProp) (t0 : Instant) : interp (atP φ t0) ↔ interpAt φ t0 :=
  ⟨fun h => h t0, fun h _ => h⟩

/-- SFS.mm `df-bl.atc`. -/
theorem df_bl_atc {α} (A : TVal α) (t0 : Instant) : interpVal (atC A t0) = interpValAt A t0 := rfl

/-- SFS.mm `df-bl.at2`: double `@` collapses to the first (outer) evaluation. -/
theorem df_bl_at2 (φ : TProp) (t1 t2 : Instant) : interp (atP (atP φ t1) t2) ↔ interpAt φ t1 :=
  (df_bl_at (atP φ t1) t2).trans Iff.rfl

/-- SFS.mm `df-bl.at2c`. -/
theorem df_bl_at2c {α} (A : TVal α) (t1 t2 : Instant) :
    interpVal (atC (atC A t1) t2) = interpValAt A t1 := rfl

/-- SFS.mm `bl.atintro`. -/
theorem bl_atintro {φ : TProp} {t0 : Instant} (_ : t0 ∈ TIME) : interp φ → interp (atP φ t0) :=
  fun h _ => h t0

/-- General @-distributes-over-any-pointwise-binary-connective fact, SFS.mm
`bl.atan2i`/`bl.ator2i`/... in one shot. -/
theorem atP_binop (g : Prop → Prop → Prop) (φ ψ : TProp) (t0 : Instant) :
    atP (fun t => g (φ t) (ψ t)) t0 = fun _ => g (φ t0) (ψ t0) := rfl

theorem atP_and (φ ψ : TProp) (t0 : Instant) : atP (φ ∧ₜ ψ) t0 = atP φ t0 ∧ₜ atP ψ t0 := rfl
theorem atP_or (φ ψ : TProp) (t0 : Instant) : atP (φ ∨ₜ ψ) t0 = atP φ t0 ∨ₜ atP ψ t0 := rfl
theorem atP_not (φ : TProp) (t0 : Instant) : atP (¬ₜφ) t0 = ¬ₜ(atP φ t0) := rfl
theorem atP_imp (φ ψ : TProp) (t0 : Instant) : atP (φ →ₜ ψ) t0 = atP φ t0 →ₜ atP ψ t0 := rfl
theorem atP_iff (φ ψ : TProp) (t0 : Instant) : atP (φ ↔ₜ ψ) t0 = atP φ t0 ↔ₜ atP ψ t0 := rfl
/- Three-term, and any-nesting, conjunction/disjunction all fall out of `atP_and`/
`atP_or` for free (SFS.mm `bl.atan3i`/`bl.atan3ri`/`bl.atan3li`/`bl.ator3i`/
`bl.ator3ri`/`bl.ator3li`): e.g. `(φ ∧ₜ ψ) ∧ₜ ch` is already `fun t => (φ ∧ₜ ψ) t ∧ ch t`,
so `atP_and` applied twice covers it, no separate lemma needed. -/
example (φ ψ ch : TProp) (t0 : Instant) :
    atP (φ ∧ₜ ψ ∧ₜ ch) t0 = atP φ t0 ∧ₜ atP ψ t0 ∧ₜ atP ch t0 := rfl

theorem atC_add (A B : TVal ℝ) (t0 : Instant) : atC (A + B) t0 = atC A t0 + atC B t0 := rfl
theorem atC_sub (A B : TVal ℝ) (t0 : Instant) : atC (A - B) t0 = atC A t0 - atC B t0 := rfl
theorem atC_mul (A B : TVal ℝ) (t0 : Instant) : atC (A * B) t0 = atC A t0 * atC B t0 := rfl
theorem atC_div (A B : TVal ℝ) (t0 : Instant) : atC (A / B) t0 = atC A t0 / atC B t0 := rfl
theorem atC_neg (A : TVal ℝ) (t0 : Instant) : atC (-A) t0 = -atC A t0 := rfl

/-! ## The `^.` operator (SFS.mm lines 2067-2726) -/

/-- SFS.mm `wts`/`clats`/`df-bl.ts`/`df-bl.tsc`: shift the evaluation instant by `n`
whole multiples of step size `D`. -/
def shiftP (φ : TProp) (D : ℝ) (n : ℤ) : TProp := fun t => φ (t + D * n)
def shiftC {α} (A : TVal α) (D : ℝ) (n : ℤ) : TVal α := fun t => A (t + D * n)

/-- SFS.mm `df-bl.ts`/`df-bl.tsi` (the `TIME`-membership side conditions in SFS.mm
constrain when the shifted predicate denotes a meaningful timed interpretation of
`ph`, not the shift computation itself, so are omitted here). -/
theorem df_bl_ts (φ : TProp) (D : ℝ) (n : ℤ) (t0 : Instant) :
    interpAt (shiftP φ D n) t0 ↔ interpAt φ (t0 + D * n) := Iff.rfl

theorem df_bl_tsc {α} (A : TVal α) (D : ℝ) (n : ℤ) (t0 : Instant) :
    interpValAt (shiftC A D n) t0 = interpValAt A (t0 + D * n) := rfl

/-- SFS.mm `bl.ts0`: an unspecified shift is a shift by `0`. -/
theorem bl_ts0 (φ : TProp) (t0 : Instant) (D : ℝ) : interpAt (φ ↔ₜ shiftP φ D 0) t0 := by
  simp [shiftP, tiff, interpAt]

/-- SFS.mm `bl.tsc0`, value-level counterpart. -/
theorem bl_tsc0 {α} (A : TVal α) (t0 : Instant) (D : ℝ) :
    interpValAt A t0 = interpValAt (shiftC A D 0) t0 := by
  simp [shiftC, interpValAt]

/-- SFS.mm `bl.tscomi`/`bl.tscomci`: composing two shifts by the same step size adds
the multipliers. -/
theorem bl_tscomi (φ : TProp) (D : ℝ) (m n : ℤ) : shiftP (shiftP φ D m) D n = shiftP φ D (m + n) := by
  funext t
  simp only [shiftP]
  congr 1
  push_cast
  ring

theorem bl_tscomci {α} (A : TVal α) (D : ℝ) (m n : ℤ) :
    shiftC (shiftC A D m) D n = shiftC A D (m + n) := by
  funext t
  simp only [shiftC]
  congr 1
  push_cast
  ring

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
axiom df_par (x : Part) : ¬ PartOf x x

/-- SFS.mm `df-ptr`: transitivity, a genuine constraint on the primitive. -/
axiom df_ptr {x y z : Part} : PartOf x y → PartOf y z → PartOf x z

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
axiom df_lfu {x : Part} {r1 r2 : Region} : Location x r1 → Location x r2 → r1 = r2

/-- SFS.mm `df-lin`: injectivity of location, a genuine constraint on `Location`. -/
axiom df_lin {x y : Part} {r : Region} : Location x r → Location y r → x = y

/-- SFS.mm `df-rov`. -/
def RegionOverlap (r1 r2 : Region) : Prop := ∃ p, InRegion p r1 ∧ InRegion p r2

/-- SFS.mm `df-rco`. -/
def RegionContainment (r1 r2 : Region) : Prop := ∀ p, InRegion p r2 → InRegion p r1

/-- SFS.mm `df-rat`. -/
def AtomicRegion (r0 : Region) : Prop :=
  ∀ (x : Part) (r1 : Region), Location x r1 ∧ RegionContainment r0 r1 → r0 = r1

/-- SFS.mm `df-rdi`: a genuine constraint (atomic regions are disjoint or equal). -/
axiom df_rdi {r1 r2 : Region} : AtomicRegion r1 → AtomicRegion r2 → ¬ RegionOverlap r1 r2 ∨ r1 = r2

/-- SFS.mm `df-apar`: a genuine constraint (atomic parts have atomic regions). -/
axiom df_apar {x : Part} {r0 : Region} : Location x r0 → AtomPart x → AtomicRegion r0

/-- SFS.mm `df-pec`: expansivity, a genuine constraint tying `PartOf` to
`RegionContainment` via `Location`. -/
axiom df_pec {x y : Part} {r1 r2 : Region} :
    Location x r1 → Location y r2 → PartOf x y → RegionContainment r1 r2

/-- SFS.mm `df-rni`: no interpenetration, a genuine constraint. -/
axiom df_rni {r1 r2 : Region} : RegionOverlap r1 r2 → RegionContainment r1 r2 ∨ RegionContainment r2 r1

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
def existsAt (A : Occurrence) (t0 : Instant) : Prop := interpValAt A t0 ≠ ∅

/-- SFS.mm `birth`: primitive (no construction of "the first instant `A` exists" is
given, only the characterizing property `df-birth` below). -/
axiom birth : Occurrence → Instant
/-- SFS.mm `death`: primitive. -/
axiom death : Occurrence → Instant

/-- SFS.mm `df-birth`. SFS.mm's own text quantifies `A. t_1 e. (0[,)t_0) -.
exists(A,t_0)` -- reusing the outer `t_0` inside the body instead of the bound
`t_1` -- almost certainly a transcription slip; read here with `t_1`, matching
`df-death`'s own (correct) shape immediately below. -/
axiom df_birth {A : Occurrence} {t0 : Instant} :
    birth A = t0 ↔ existsAt A t0 ∧ ∀ t1 ∈ Set.Ico (0 : Instant) t0, ¬ existsAt A t1

/-- SFS.mm `df-death`. -/
axiom df_death {A : Occurrence} {t0 : Instant} :
    death A = t0 ↔ existsAt A t0 ∧ ∀ t1 ∈ Set.Ioc t0 now, ¬ existsAt A t1

/-- SFS.mm `df-lifetime`. -/
def life (A : Occurrence) : Set Instant := Set.Icc (birth A) (death A)

/-- SFS.mm `df-precedes`. -/
def precedes (A B : Occurrence) : Prop := death A ≺ birth B
/-- SFS.mm `df-meets`. -/
def meets (A B : Occurrence) : Prop := death A = birth B
/-- SFS.mm `df-overlaps`. -/
def overlaps (A B : Occurrence) : Prop := birth B ≺ death A
/-- SFS.mm `df-starts`. -/
def starts (A B : Occurrence) : Prop := birth A = birth B ∧ death B ≺ death A
/-- SFS.mm `df-during`. -/
def during (A B : Occurrence) : Prop := birth B ≼ birth A ∧ death A ≼ death B
/-- SFS.mm `df-finishes`. -/
def finishes (A B : Occurrence) : Prop := birth B ≺ birth A ∧ death A = death B
/-- SFS.mm `df-coincident`. -/
def coincident (A B : Occurrence) : Prop := birth A = birth B ∧ death A = death B
/-- SFS.mm `df-nonoverlaps`. -/
def nonoverlaps (A B : Occurrence) : Prop := death A ≺ birth B ∨ death B ≺ birth A

/-- SFS.mm `df-next`: `t_2` immediately follows `t_1`, no instant strictly between.
A genuine `def` over the real `≺` (SFS.mm needed `bl.tpeq1`/`bl.tpeq2` as extra
axioms to make this usable in a real Metamath proof, since its `wtp` is a bare
primitive there -- moot here, `tprec_congr1`/`tprec_congr2` above are free). -/
def next (t1 t2 : Instant) : Prop := t1 ≺ t2 ∧ ¬ ∃ x, t1 ≺ x ∧ x ≺ t2

/-- SFS.mm `bl.nexttp`. Free, `rfl`-adjacent, not an axiom. -/
theorem next_tprec {t1 t2 : Instant} (h : next t1 t2) : t1 ≺ t2 := h.1

/-- SFS.mm `bl.nextdense`, and simultaneously the direct resolution -- via ordinary
real-number density (`exists_between`, Mathlib) -- of the exact
`bl.nlt1`-`bl.nlt7`/`ASSIGN`-unification blocker documented in
`reference_metamath_sfs_toolchain.md`: `next` is *vacuous* on `ℝ`, full stop. -/
theorem next_dense (t1 t2 : Instant) : ¬ next t1 t2 := by
  rintro ⟨h12, hno⟩
  obtain ⟨x, hx1, hx2⟩ := exists_between h12
  exact hno ⟨x, hx1, hx2⟩

/-- SFS.mm `bl.nextuniq`. Vacuously true, via `next_dense`, in one line -- the
uniqueness question dissolves once existence is known to fail on unrestricted
dense time (matching the book's own remark that `next` "only does real work when
applied to instant pairs known not to be dense with each other"). -/
theorem next_uniq {t1 t2 t3 : Instant} (h : next t1 t2) : t2 = t3 := absurd h (next_dense t1 t2)

/-! ### KerML Element Representation (SFS.mm lines 3121-3149) -/

/-- SFS.mm `df-kind`: a set of 14 pairwise-distinct constants. The natural Lean
counterpart of "these are new, pairwise-distinct atomic constants" is an
`inductive` enum (constructor-distinctness is free), not an `axiom`. -/
inductive ElementKind
  | Element | Relationship | Dependency | Feature | Classifier | DataType | Class
  | Structure | Association | Connector | Behavior | Function | Expression | Interaction
  deriving DecidableEq, Repr

end SFS
