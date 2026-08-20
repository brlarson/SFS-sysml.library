/-
Lean 4 formalization of the KerML (Kernel Modeling Language, OMG SysML v2 Release,
"Kernel Modeling Language v1.0 Beta 3") **Core** package's metamodel: KerML §8.2.4
"Core Concrete Syntax" and §8.3.3 "Core Abstract Syntax". Builds on `Root.lean`
(KerML §8.2.3/§8.3.2) the same way KerML's own Core package imports Root (Figure 1,
"KerML Syntax Layers").

Same scope discipline as `Root.lean` -- see that file's header for the full rationale:
`extends` mirrors the generalization hierarchy; only non-derived (stored) attributes
become fields; the containment/graph-structural attributes (`feature`,
`ownedFeatureMembership`, `inheritedMembership`, ...) are omitted; OCL constraints are
noted in prose, not encoded or proved.

**Naming note**: KerML's `Type` metaclass is renamed `KType` here -- `Type` is Lean's
own universe/keyword, and even inside a namespace a `structure Type` would shadow it
for every subsequent use of bare `Type` in this file (e.g. `axiom foo : Type`), which
is exactly the kind of silent, hard-to-diagnose collision worth avoiding outright
rather than working around locally. `FeatureDirectionKind`'s literals are similarly
renamed (`in`/`out` are Lean keywords) to `inDir`/`outDir`/`inoutDir`.
-/

import Root

namespace KerML.Core

open KerML.Root

/-- KerML §8.3.3.1.8 `KType` (KerML's `Type`; see file header for the rename).
"The basic structural framework for the KerML model, in terms of Namespaces of
Features whose values may be classified by Types." `isAbstract`: instances must also
instantiate a specialized `KType`. `isSufficient`: whether meeting this `KType`'s
classification conditions is *sufficient* for classification (not just necessary).
Constraint (not encoded): every `KType` must (directly or indirectly) specialize
`Base::Anything`. Derived attributes omitted per the file header: `feature`,
`featureMembership`, `inheritedMembership`, `multiplicity`, `isConjugated`,
`ownedSpecialization`, `ownedConjugator`, `unioningType`/`intersectingType`/
`differencingType`, `endFeature`, `input`/`output`, ... -/
structure KType extends Namespace where
  isAbstract : Bool := false
  isSufficient : Bool := false
  deriving Repr

/-- KerML §8.3.3.2.2 `Classifier`. "A `KType` whose instances are classified by how
they relate to instances of other `Classifiers`, via their `Features`, along with
whichever additional instances the `Classifier` may directly specify." A `Classifier`
that specializes a `Feature` cannot classify anything (constraint, not encoded).
`ownedSubclassification` is derived, so no extra fields beyond `KType`'s. -/
structure Classifier extends KType where
  deriving Repr

/-- KerML §8.3.3.1.5 `FeatureDirectionKind`: whether a `Feature` used as a parameter
is an input (`inDir`), output (`outDir`), or both (`inoutDir`). See file header for
the `in`/`out`/`inout` → `inDir`/`outDir`/`inoutDir` keyword-avoiding rename. -/
inductive FeatureDirectionKind
  | inDir | outDir | inoutDir
  deriving DecidableEq, Repr

/-- KerML §8.3.3.3.3 `Feature`. "A kind of `KType` whose instances are values that
are assigned to it in the context of instances of its `featuringType`(s)." Non-derived
attributes only (see file header) -- `type`, `chainingFeature`, `featuringType`,
`owningType`, `ownedTyping`/`ownedSubsetting`/`ownedRedefinition`/
`ownedReferenceSubsetting`/`ownedCrossSubsetting`/`ownedFeatureChaining`/
`ownedFeatureInverting`/`ownedTypeFeaturing`, `crossFeature`, `featureTarget`,
`endOwningType`, `owningFeatureMembership` are all derived/graph-structural, omitted.
Many further constraints (e.g. every `Feature` must specialize `Base::things`; an
`isEnd` `Feature` must have multiplicity exactly 1..1 and no `direction`/`isDerived`/
`isAbstract`/`isComposite`/`isPortion`; `isVariable` requires `owningType` to
specialize `Occurrences::Occurrence`) tie into the Kernel Semantic Library and are not
encoded here. -/
structure Feature extends KType where
  direction : Option FeatureDirectionKind := none
  isComposite : Bool := false
  isConstant : Bool := false
  isDerived : Bool := false
  isEnd : Bool := false
  isOrdered : Bool := false
  isPortion : Bool := false
  isUnique : Bool := false
  /-- Whether this Feature's value can vary across snapshots of an `Occurrence`
  `owningType` (only meaningful together with `owningType` specializing
  `Occurrences::Occurrence`; see KerML §8.3.3.3.3 constraints, not encoded). -/
  isVariable : Bool := false
  deriving Repr

/-- KerML §8.3.3.1.11 `Multiplicity`: a `Feature` "whose values are the natural
number cardinalities that bound the number of values of a `Feature` typed by a
`Type` with this `Multiplicity`." Constraint (not encoded): must specialize
`Base::naturals`. No extra stored attributes beyond `Feature`'s. -/
structure Multiplicity extends Feature where
  deriving Repr

/-- KerML §8.3.3.1.7 `Specialization`. A `Relationship` asserting `specific`
(redefines `source`) is a specialization of `general` (redefines `target`) -- every
instance of `specific` is also an instance of `general`. `owningType` (derived =
`specific`, when owned) omitted. Constraint (not encoded): the `specific` `KType` of a
`Specialization` cannot be conjugated. -/
structure Specialization extends Relationship where
  specific : KType
  general : KType
  deriving Repr

/-- KerML §8.3.3.2.3 `Subclassification`, a `Specialization` between two
`Classifier`s: `subclassifier` (redefines `specific`) is a subclassifier of
`superclassifier` (redefines `general`). -/
structure Subclassification extends Specialization where
  subclassifier : Classifier
  superclassifier : Classifier
  deriving Repr

/-- KerML §8.3.3.3.7 `FeatureTyping`, a `Specialization` asserting `typedFeature`
(redefines `specific`) is typed by `type` (redefines `general`) -- i.e. `type` is one
of `typedFeature`'s types. -/
structure FeatureTyping extends Specialization where
  typedFeature : Feature
  type : KType
  deriving Repr

/-- KerML §8.3.3.3.9 `Subsetting`, a `Specialization` between two `Feature`s: every
value of `subsettingFeature` (redefines `specific`), on its domain, is a value of
`subsettedFeature` (redefines `general`). -/
structure Subsetting extends Specialization where
  subsettingFeature : Feature
  subsettedFeature : Feature
  deriving Repr

/-- KerML §8.3.3.3.6 `Redefinition`, a `Subsetting` where corresponding values must
additionally be *equal* (not just related by subsetting), enabling the redefining
`Feature` to reuse the redefined `Feature`'s name. -/
structure Redefinition extends Subsetting where
  redefiningFeature : Feature
  redefinedFeature : Feature
  deriving Repr

/-- KerML §8.3.3.3.8 `ReferenceSubsetting`: a syntactically-distinguished
`Subsetting` (same semantics as `Subsetting` generally), always owned by
`referencingFeature` (derived = `subsettingFeature`); a `Feature` has at most one
(constraint, not encoded). Used e.g. for a Connector's `relatedFeature`s. -/
structure ReferenceSubsetting extends Subsetting where
  referencedFeature : Feature
  deriving Repr

/-- KerML §8.3.3.3.2 `CrossSubsetting`: subsets an `isEnd` `Feature` to a chained
`Feature` "crossing" to another end `Feature`'s type on the same `owningType`
(requires the owning `KType` to have at least two end `Feature`s). -/
structure CrossSubsetting extends Subsetting where
  crossedFeature : Feature
  deriving Repr

/-- KerML §8.3.3.1.4 `FeatureMembership`, an `OwningMembership` whose member is a
`Feature`. If the owned `Feature` is not `isVariable`, `owningType` becomes one of its
`featuringType`s directly; if `isVariable`, it's featured by `owningType`'s
*snapshots* instead (`owningType` must specialize `Occurrences::Occurrence`,
constraint not encoded). `ownedMemberFeature`/`owningType` are derived, omitted. -/
structure FeatureMembership extends OwningMembership where
  deriving Repr

/-- KerML §8.3.3.3.4 `EndFeatureMembership`, a `FeatureMembership` whose member
`Feature` must be owned and have `isEnd = true` (constraint, not encoded; no extra
stored attributes beyond `FeatureMembership`'s). -/
structure EndFeatureMembership extends FeatureMembership where
  deriving Repr

/-- KerML §8.3.3.1.3 `Conjugation`. `conjugatedType` (redefines `source`) inherits
`originalType` (redefines `target`)'s `Feature`s with `in`/`out` directions reversed.
Constraints (not encoded): a `KType` is `conjugatedType` in at most one `Conjugation`;
a conjugated `KType` can't also be a `specific` `KType` in a `Specialization`. -/
structure Conjugation extends Relationship where
  conjugatedType : KType
  originalType : KType
  deriving Repr

/-- KerML §8.3.3.1.6 `Disjoining`: asserts `typeDisjoined` (redefines `source`) and
`disjoiningType` (redefines `target`) have disjoint (non-overlapping) instance sets. -/
structure Disjoining extends Relationship where
  typeDisjoined : KType
  disjoiningType : KType
  deriving Repr

/-- KerML §8.3.3.1.10 `Unioning`: makes `unioningType` (redefines `target`) one of
`typeUnioned` (derived = `source`, owned union member)'s `unioningType`s (a `KType`'s
instances are the union of its `unioningType`s', if any). -/
structure Unioning extends Relationship where
  unioningType : KType
  deriving Repr

/-- KerML §8.3.3.1 `Intersecting`: analogous to `Unioning`, but for set intersection
(`intersectingType` redefines `target`). -/
structure Intersecting extends Relationship where
  intersectingType : KType
  deriving Repr

/-- KerML §8.3.3.1 `Differencing`: analogous to `Unioning`, but for set difference
(`differencingType` redefines `target`; the owning `KType`'s instances are its first
`differencingType`'s instances minus the rest). -/
structure Differencing extends Relationship where
  differencingType : KType
  deriving Repr

/-- KerML §8.3.3.3.5 `FeatureChaining`: relates a `Feature` (`featureChained`, derived
= `source`, owned) to one link (`chainingFeature`, redefines `target`) of the chain of
`Feature`s that determine its value. -/
structure FeatureChaining extends Relationship where
  chainingFeature : Feature
  deriving Repr

/-- KerML §8.3.3.3.10 `FeatureInverting`: asserts `invertingFeature` (redefines
`target`) is the inverse of `featureInverted` (redefines `source`). -/
structure FeatureInverting extends Relationship where
  featureInverted : Feature
  invertingFeature : Feature
  deriving Repr

/-- KerML §8.3.3.3.11 `TypeFeaturing`: asserts `featureOfType` (redefines `source`)
is featured (usable) by instances of `featuringType` (redefines `target`). Distinct
from `FeatureTyping` above (a kind of `Specialization`) despite the similar name --
they're unrelated in the generalization hierarchy. -/
structure TypeFeaturing extends Relationship where
  featureOfType : Feature
  featuringType : KType
  deriving Repr

end KerML.Core
