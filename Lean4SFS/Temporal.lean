/-
# `Temporal.lean` -- the Lean half of the temporal-succession change

Companion to the three revised `.kerml` files, which widen `HappensBefore`'s ends
from `Occurrence` to a new marker classifier `Domain::Temporal`, so that
`first start then putIt` type-checks with `Action::start : Instant`.

## Why two halves

The library and the model check different things, and neither subsumes the other.

* KerML can state the constraint only as *specialization from a common supertype*.
  `Domain::Temporal` is that supertype.  The library says WHICH values are
  admissible at a succession end, and nothing more.

* Syside does not type-check the contents of `@Assert` formulas -- `f=` is an
  opaque string to the tool.  So `precedes(earlierOccurrence, laterOccurrence)`
  is *not* checked against `Allen::precedes`'s `in x : Occurrence` by anything.
  That mismatch is real but latent; it bites here, in Lean, where
  `precedes (A B : Occurrence)` rejects an `Instant` argument outright.

This file supplies the missing half: HOW the predicate reads its arguments,
stated so that it reads them out of anything with a temporal extent.

## What `precedes` actually needs

From `SFS.lean` as it stands:

    noncomputable def effectiveEnd (A : Occurrence) : Time := (death A).getD ⟨now, dl_nowt⟩
    noncomputable def precedes (A B : Occurrence) : Prop := (effectiveEnd A).val ≺ (birth B).val

Two observations drive everything below.

1. `precedes` is ASYMMETRIC.  It projects only the *end* of its left argument and
   only the *start* of its right.  Nothing else about `Occurrence` is touched.
   Hence two one-field classes rather than one two-field class -- each argument
   is constrained by exactly what is read from it.

2. It needs only a STRICT ORDER on the instant carrier.  Not totality.  Nothing
   in the present Allen layer proves anything requiring trichotomy (the single
   `lt_trichotomy` in `SFS.lean` is in the tick-index machinery), so `[LT ι]` is
   the honest constraint.  See the note on `nonoverlaps` at the bottom for the
   one thing linearity would buy.

## Status

This file is self-contained and compiles on its own (`lake env lean Temporal.lean`)
against a `variable`-bound carrier.  It is an illustration of the shape, not a
change to `SFS.lean`; the "Grafting into SFS.lean" section at the bottom gives the
concrete instances, which cannot be written here without importing SFS.
-/

namespace Temporal

universe u v w

/-! ## The two classes

`ι` is the instant carrier, an `outParam` so that `precedes` can infer it from
either argument rather than requiring it to be written at each call site.  Both
classes are one field: the single projection that `precedes` performs. -/

/-- The left-hand requirement of `precedes`: this value has an end instant.

For an `Occurrence` this is `SFS.effectiveEnd` -- the real end if the occurrence
has one, else `now`.  Total, following `c42d6ae` ("Re-formulate Allen's intervals
via effectiveEnd, retiring the Kleene layer"). -/
class HasEnd (ι : outParam (Type u)) (α : Type v) where
  «end» : α → ι

/-- The right-hand requirement of `precedes`: this value has a start instant.

For an `Occurrence` this is `SFS.Lifetimes.birth`, which is total already. -/
class HasStart (ι : outParam (Type u)) (α : Type v) where
  start : α → ι

/-! ## The generalized predicate

Two carriers, `α` and `β`, not one.  This is what admits a mixed succession --
an `Instant` on one end and an `Occurrence` on the other. -/

variable {ι : Type u} {α : Type v} {β : Type w}

/-- `SFS.mm` `df-precedes`, generalized.  Definitionally the present
`SFS.precedes` when `α = β = Occurrence`. -/
def precedes [LT ι] [HasEnd ι α] [HasStart ι β] (a : α) (b : β) : Prop :=
  HasEnd.«end» a < HasStart.start b

/-- `df-overlaps`, generalized: the right argument starts before the left ends.
Mirror image of `precedes` in which class each argument needs. -/
def overlaps [LT ι] [HasEnd ι α] [HasStart ι β] (a : α) (b : β) : Prop :=
  HasStart.start b < HasEnd.«end» a

/-- `df-during`, generalized.  Needs both projections from both arguments, so
both class constraints appear twice. -/
def during [LE ι] [HasStart ι α] [HasEnd ι α] [HasStart ι β] [HasEnd ι β]
    (a : α) (b : β) : Prop :=
  HasStart.start b ≤ HasStart.start a ∧ HasEnd.«end» a ≤ HasEnd.«end» b

/-! ## Boundary flags

`meets`, `starts`, `finishes`, `coincident` and `nearlyMeets` additionally compare
open/closed boundaries, which are NOT recoverable from the endpoints.  They need a
third class -- which would also retire the two bare axioms

    axiom openLeft  : Occurrence → Prop        -- SFS.lean:1190
    axiom openRight : Occurrence → Prop        -- SFS.lean:1191

in the same spirit as `d56f99c` ("Replace openLeft/openRight axioms with a bundled
OpenBoundary class"): as class fields they become carried structure rather than
trusted ingredients. -/

/-- `Domain.kerml`'s `Interval::openLeft` / `openRight`, as carried structure. -/
class HasBoundary (α : Type v) where
  openLeft  : α → Prop
  openRight : α → Prop

/-- `df-meets`, generalized.  The two boundary conjuncts are `Allen.kerml`'s own
(`x.endShot == y.startShot and not x.openRight and not y.openLeft`). -/
def meets [DecidableEq ι] [HasEnd ι α] [HasBoundary α] [HasStart ι β] [HasBoundary β]
    (a : α) (b : β) : Prop :=
  HasEnd.«end» a = HasStart.start b ∧ ¬ HasBoundary.openRight a ∧ ¬ HasBoundary.openLeft b

/-! ## The degenerate instance

An instant starts and ends at itself and is closed on both sides.  This is the
Lean counterpart of `type Instant specializes TimeValue, Temporal` in `Domain.kerml`,
and it is what lets `Action::start` sit at a succession end.

Both instances are needed, not one, because a model may use either orientation:

    first start then putIt;   -- Instant on the LEFT  -> HasEnd
    first putIt then done;    -- Instant on the RIGHT -> HasStart

Note this is an *instance*, not a subtyping claim.  On the Lean side `Instant`
need not become interval-shaped, so none of the scalar machinery it carries in
the library (`0.0 [s]`, `o.endShot - o.startShot` in `Clocks.kerml`) is disturbed. -/

instance instHasEndSelf   : HasEnd ι ι   := ⟨id⟩
instance instHasStartSelf : HasStart ι ι := ⟨id⟩
instance instHasBoundarySelf : HasBoundary ι := ⟨fun _ => False, fun _ => False⟩

/-! ## A third inhabitant, neither Instant nor Occurrence

The constraint the classes express is structural: *this value has endpoints*.
Nothing about it is particular to instants or to occurrences, and it is worth
having one witness on record that is neither.

A set of instants with an attained first and last member is such a witness.  It
inhabits `HasStart` and `HasEnd`, so `precedes` accepts it at either end of a
succession, yet it is neither an `Instant` (it is a collection, and may hold many)
nor an `Occurrence` (it has no identity, no life, no frame of reference).

`lo` and `hi` are ATTAINED (`lo_mem` / `hi_mem`), not merely bounding.  That is
`SFS.lean`'s own choice, where `hasFirstInstant` yields `IsLeast` for exactly this
reason.  Because attainment is carried as a field rather than derived, the
structure needs only `[LE ι]` -- no linearity, and no completeness.  Where a
`Spanned` can be built at all, its endpoints come with it. -/

/-- A set of instants carrying an attained least and greatest member. -/
structure Spanned (ι : Type u) [LE ι] where
  mem : ι → Prop  -- This is essentially `Set ι`
  lo : ι
  hi : ι
  lo_mem : mem lo
  hi_mem : mem hi
  lo_least : ∀ t, mem t → lo ≤ t
  hi_greatest : ∀ t, mem t → t ≤ hi

instance instHasStartSpanned [LE ι] : HasStart ι (Spanned ι) := ⟨Spanned.lo⟩
instance instHasEndSpanned   [LE ι] : HasEnd   ι (Spanned ι) := ⟨Spanned.hi⟩

/-! ## Worked check

With the degenerate instance in scope, both succession orientations elaborate.
`Occ` here stands in for `Occurrence`; in `SFS.lean` these are the real instances
given in the grafting section below. -/

section Demo

variable {ι : Type u} (Occ : Type v) [HasStart ι Occ] [HasEnd ι Occ] [LT ι]

/-- `first start then putIt` -- Instant on the left, Occurrence on the right. -/
example (tau : ι) (putIt : Occ) : Prop := precedes tau putIt

/-- `first putIt then done` -- Occurrence on the left, Instant on the right. -/
example (putIt : Occ) (tau : ι) : Prop := precedes putIt tau

/-- The unchanged case: both ends Occurrences, exactly as before. -/
example (p q : Occ) : Prop := precedes p q

/-- A set of instants against an Occurrence: neither argument type is built in. -/
example [LE ι] (s : Spanned ι) (putIt : Occ) : Prop := precedes s putIt

end Demo

/-! ## Grafting into SFS.lean

Add, after `Lifetimes` and `effectiveEnd`:

    instance : Temporal.HasStart Time Occurrence := ⟨Lifetimes.birth⟩
    instance : Temporal.HasEnd   Time Occurrence := ⟨effectiveEnd⟩
    instance : Temporal.HasBoundary  Occurrence  := ⟨openLeft, openRight⟩

then replace the bodies of `precedes` / `overlaps` / `during` / `meets` with the
generalized versions.  Each is definitionally equal to the present one at
`α = β = Occurrence`, so existing proofs about them do not change shape.

`Time`'s own instances come free from `instHasEndSelf` / `instHasStartSelf` above.

### One consequence to decide deliberately

`SFS.lean` currently has

    noncomputable def nonoverlaps (A B : Occurrence) : Prop := precedes A B ∨ precedes B A

which remains well-formed over a strict partial order but stops being equivalent
to `¬ overlaps A B`.  Equivalently: Allen's thirteen relations stop being jointly
exhaustive.  That property is a consequence of LINEARITY, not of any definition
here, so it is available on demand by strengthening `[LT ι]` to a linear order --
which the `time-as-typeclass` branch's `TimeFrame` already carries.  Left as
`[LT ι]` here because nothing presently proven needs more, and because causal /
relativistic time and concurrent execution are both genuinely partial; the
per-occurrence `FrameOfReference` in `Regions.kerml` points the same way.

Should that be wanted, Mathlib already has the class, in two strengths.

The lighter one is `IsStrictTotalOrder ι (· < ·)`: a `Prop` class,
`extends Std.Trichotomous lt, IsStrictOrder α lt`, where `IsStrictOrder` is in
turn `Std.Irrefl` + `IsTrans`.  Those three properties are exactly what the Allen
layer would need, and nothing else comes with them.  It is the better fit here,
since every predicate above touches only `LT`:

    def precedes [LT ι] [IsStrictTotalOrder ι (· < ·)]
        [HasEnd ι α] [HasStart ι β] (a : α) (b : β) : Prop := ...

The heavier one is `LinearOrder`, which additionally carries `PartialOrder`,
`Min`, `Max`, `Ord` and three decidability fields.  That is what the
`time-as-typeclass` branch's `TimeFrame` already holds, as
`[instantLinearOrder : LinearOrder Instant]` with `attribute [instance]`, so
matching it costs nothing there and the choice may be settled by consistency
rather than by weight.

Three things to know before reaching for either (all verified against the pinned
Mathlib, and all easy to trip over):

* `[LinearOrder α]` does supply `IsStrictTotalOrder α (· < ·)`, but the instance
  lives in `Mathlib.Order.RelClasses`.  With only `Mathlib.Order.Defs.*` imported,
  `inferInstance` fails.
* Trichotomy is spelled `Std.Trichotomous` in this version, not `IsTrichotomous`.
* `Std.Trichotomous.trichotomous` is stated in CONNECTEDNESS form,
  `¬ r a b → ¬ r b a → a = b` -- not the three-way disjunction.  For the
  disjunction use `lt_trichotomy a b` (with `LinearOrder`) or
  `trichotomous_of lt a b` (with the unbundled class).

Either route also means this file stops being import-free; see Status above.
-/

end Temporal
