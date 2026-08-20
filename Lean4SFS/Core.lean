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

Below the abstract-syntax structures, this file also declares real `syntax`/`elab`
productions for KerML §8.2.4 "Core Concrete Syntax" -- a working parser and elaborator
for a keyword-only subset of the textual notation itself (`type A specializes B ;`,
`feature f typed by T ;`, ...), in the same house style `DSL.lean` established for the
`@Assert` formula language (`declare_syntax_cat`/`syntax ... : category` productions,
pure `MacroM (TSyntax `term)` elaborator functions, one top-level triggering `elab`).
See that section's own header comment for its scope (relationship-bearing productions
only; boolean prefix flags and name resolution are out of scope).
-/

import Root
import Lean

namespace KerML.Core

open KerML.Root
open Lean

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

/-! ## Concrete syntax (KerML §8.2.4 "Core Concrete Syntax")

A real, working parser and elaborator for a subset of KerML's textual notation, in
`DSL.lean`'s house style (`declare_syntax_cat`, `syntax ... : category` productions,
pure `MacroM (TSyntax `term)` elaborators, one top-level triggering `elab`).

**Scope, deliberately narrower than the full grammar (documented, not accidental)**:

- Only the *relationship-forming* productions are covered: `Type`, `Classifier`,
  `Feature` (as declaration headers) and the nine standalone relationship
  declarations (`Specialization`/`Conjugation`/`Disjoining`/`Subclassification`/
  `FeatureTyping`/`Subsetting`/`Redefinition`/`FeatureInverting`/`TypeFeaturing`),
  plus `Feature`'s inline `references`/`crosses`/`chains` parts. These are what
  actually *create* additional `Element`s, which is the interesting elaboration
  target. Boolean/enum prefix flags (`abstract`, `all`, `derived`, `composite`,
  `portion`, `var`, `const`, direction `in`/`out`/`inout`) are **not** parsed here --
  those fields already exist on `KType`/`Feature` above; this layer just doesn't yet
  read them from text. Symbolic operator alternates (`:>`, `~`, `::>`, `=>`, `:>>`)
  are also omitted -- keyword spellings only (`specializes`, `conjugates`, `subsets`,
  ...).
- `TypeBody` is always `;` (no owned-member bodies) -- consistent with this file's own
  "structural only" scope, which already dropped the containment graph a `{ ... }`
  body would populate.
- Qualified names are simplified to bare `ident` (no dotted/`::`-paths, no name
  resolution): a referenced name like the `B` in `type A specializes B ;` is
  genuinely a *reference* to something else -- an existing declaration, visible in
  whatever scope this text occurs in (per the repo's `CLAUDE.md`: identifiers "may
  include names or identifiers visible in the scope where they occur," not always
  re-declared where used) -- not a fresh declaration of its own. This project has no
  symbol table (see file header) to actually look `B` up, though, so it's represented
  here by a minimal stub value (`mkKTypeStub`/`mkClassifierStub`/`mkFeatureStub`)
  carrying just the referenced name -- a placeholder standing in for "whatever `B`
  resolves to," not a claim that `B` is newly declared right here. Building a real
  symbol table would be a substantially bigger project than this addition.
- Every `kermlDecl` elaborates to a single `List Element` term: the primary
  `KType`/`Classifier`/`Feature`/relationship, followed by one further `Element` per
  relationship its text implies. This is *not* a simplification of the metamodel --
  KerML's own abstract syntax doesn't store `Specialization`/`Conjugation`/... as
  fields *on* the `Type` they relate either; they're sibling owned `Relationship`
  elements. A flat list of "the `Element`s this declaration text brings into being" is
  the faithful shape, not a shortcut. -/

/-- Minimal stub values standing in for a bare identifier *reference* in the concrete
syntax below (see the scope note above: these represent something already visible in
scope, not a fresh declaration -- this project just has no symbol table to actually
resolve the reference, so the stub carries only the referenced name). -/
def mkKTypeStub (name : String) : KType := { elementId := name, declaredName := some name }
def mkClassifierStub (name : String) : Classifier := { elementId := name, declaredName := some name }
def mkFeatureStub (name : String) : Feature := { elementId := name, declaredName := some name }

/-- `.toElement` composed through each structure's `extends` chain, so every metaclass
constructed below can be placed in a single flat `List Element` result. -/
def KType.elt (t : KType) : Element := t.toNamespace.toElement
def Classifier.elt (c : Classifier) : Element := c.toKType.elt
def Feature.elt (f : Feature) : Element := f.toKType.elt
def Specialization.elt (s : Specialization) : Element := s.toRelationship.toElement
def Subclassification.elt (s : Subclassification) : Element := s.toSpecialization.elt
def FeatureTyping.elt (t : FeatureTyping) : Element := t.toSpecialization.elt
def Subsetting.elt (s : Subsetting) : Element := s.toSpecialization.elt
def Redefinition.elt (r : Redefinition) : Element := r.toSubsetting.elt
def ReferenceSubsetting.elt (r : ReferenceSubsetting) : Element := r.toSubsetting.elt
def CrossSubsetting.elt (r : CrossSubsetting) : Element := r.toSubsetting.elt
def Conjugation.elt (c : Conjugation) : Element := c.toRelationship.toElement
def Disjoining.elt (d : Disjoining) : Element := d.toRelationship.toElement
def Unioning.elt (u : Unioning) : Element := u.toRelationship.toElement
def Intersecting.elt (i : Intersecting) : Element := i.toRelationship.toElement
def Differencing.elt (d : Differencing) : Element := d.toRelationship.toElement
def FeatureChaining.elt (f : FeatureChaining) : Element := f.toRelationship.toElement
def FeatureInverting.elt (f : FeatureInverting) : Element := f.toRelationship.toElement
def TypeFeaturing.elt (t : TypeFeaturing) : Element := t.toRelationship.toElement

/-- A synthesized `elementId` for a relationship object built below, since
`elementId : String` has no default and this layer has no real ID-generation
tooling -- just a readable `A-kind-B` tag, uniqueness not enforced (matching this
file's "structural only" scope generally). -/
def relElementId (a b kind : String) : String := a ++ "-" ++ kind ++ "-" ++ b

def kTypeStubTerm (i : TSyntax `ident) : MacroM (TSyntax `term) :=
  `(mkKTypeStub $(quote i.getId.toString))
def classifierStubTerm (i : TSyntax `ident) : MacroM (TSyntax `term) :=
  `(mkClassifierStub $(quote i.getId.toString))
def featureStubTerm (i : TSyntax `ident) : MacroM (TSyntax `term) :=
  `(mkFeatureStub $(quote i.getId.toString))

def mkSpecializationTerm (aT bT : TSyntax `term) (an bn : String) : MacroM (TSyntax `term) :=
  `(({ elementId := $(quote (relElementId an bn "specializes")),
       specific := $aT, general := $bT } : Specialization))
def mkSubclassificationTerm (aT bT : TSyntax `term) (an bn : String) : MacroM (TSyntax `term) :=
  `(({ elementId := $(quote (relElementId an bn "subclassifies")),
       subclassifier := $aT, superclassifier := $bT,
       specific := ($aT).toKType, general := ($bT).toKType } : Subclassification))
def mkFeatureTypingTerm (fT tT : TSyntax `term) (fn tn : String) : MacroM (TSyntax `term) :=
  `(({ elementId := $(quote (relElementId fn tn "typedby")),
       typedFeature := $fT, type := $tT,
       specific := ($fT).toKType, general := $tT } : FeatureTyping))
def mkSubsettingTerm (fT gT : TSyntax `term) (fn gn : String) : MacroM (TSyntax `term) :=
  `(({ elementId := $(quote (relElementId fn gn "subsets")),
       subsettingFeature := $fT, subsettedFeature := $gT,
       specific := ($fT).toKType, general := ($gT).toKType } : Subsetting))
def mkRedefinitionTerm (fT gT : TSyntax `term) (fn gn : String) : MacroM (TSyntax `term) :=
  `(({ elementId := $(quote (relElementId fn gn "redefines")),
       redefiningFeature := $fT, redefinedFeature := $gT,
       subsettingFeature := $fT, subsettedFeature := $gT,
       specific := ($fT).toKType, general := ($gT).toKType } : Redefinition))
def mkReferenceSubsettingTerm (fT gT : TSyntax `term) (fn gn : String) : MacroM (TSyntax `term) :=
  `(({ elementId := $(quote (relElementId fn gn "references")),
       referencedFeature := $gT,
       subsettingFeature := $fT, subsettedFeature := $gT,
       specific := ($fT).toKType, general := ($gT).toKType } : ReferenceSubsetting))
def mkCrossSubsettingTerm (fT gT : TSyntax `term) (fn gn : String) : MacroM (TSyntax `term) :=
  `(({ elementId := $(quote (relElementId fn gn "crosses")),
       crossedFeature := $gT,
       subsettingFeature := $fT, subsettedFeature := $gT,
       specific := ($fT).toKType, general := ($gT).toKType } : CrossSubsetting))
def mkConjugationTerm (aT bT : TSyntax `term) (an bn : String) : MacroM (TSyntax `term) :=
  `(({ elementId := $(quote (relElementId an bn "conjugates")),
       conjugatedType := $aT, originalType := $bT } : Conjugation))
def mkDisjoiningTerm (aT bT : TSyntax `term) (an bn : String) : MacroM (TSyntax `term) :=
  `(({ elementId := $(quote (relElementId an bn "disjoint")),
       typeDisjoined := $aT, disjoiningType := $bT } : Disjoining))
def mkUnioningTerm (bT : TSyntax `term) (bn : String) : MacroM (TSyntax `term) :=
  `(({ elementId := $(quote (bn ++ "-unioning")), unioningType := $bT } : Unioning))
def mkIntersectingTerm (bT : TSyntax `term) (bn : String) : MacroM (TSyntax `term) :=
  `(({ elementId := $(quote (bn ++ "-intersecting")), intersectingType := $bT } : Intersecting))
def mkDifferencingTerm (bT : TSyntax `term) (bn : String) : MacroM (TSyntax `term) :=
  `(({ elementId := $(quote (bn ++ "-differencing")), differencingType := $bT } : Differencing))
def mkFeatureChainingTerm (_fT gT : TSyntax `term) (fn gn : String) : MacroM (TSyntax `term) :=
  `(({ elementId := $(quote (relElementId fn gn "chains")),
       chainingFeature := $gT } : FeatureChaining))
def mkFeatureInvertingTerm (fT gT : TSyntax `term) (fn gn : String) : MacroM (TSyntax `term) :=
  `(({ elementId := $(quote (relElementId fn gn "inverseof")),
       featureInverted := $fT, invertingFeature := $gT } : FeatureInverting))
def mkTypeFeaturingTerm (fT tT : TSyntax `term) (fn tn : String) : MacroM (TSyntax `term) :=
  `(({ elementId := $(quote (relElementId fn tn "featuredby")),
       featureOfType := $fT, featuringType := $tT } : TypeFeaturing))

/-- `[t1, t2, ...] : List Element`, built as nested `::`, matching `DSL.lean`'s own
`foldrM`-over-a-collection idiom for assembling syntax incrementally. -/
partial def mkListTerm : List (TSyntax `term) → MacroM (TSyntax `term)
  | [] => `([])
  | t :: ts => do `($t :: $(← mkListTerm ts))

/-- A bare `abstract` prefix flag, wrapped in its own trivial category (rather than
used as a bare optional keyword directly) so it can be captured via `$[$abs:...]?`
the same proven way `dslRange`'s own optional clauses are captured in `DSL.lean` --
presence tested via `.isSome`, not stored (matches `KType`/`Classifier`/etc.'s own
`isAbstract` field existing, just not yet threaded from parsed text into a value,
same "not yet read from text" status as the other omitted prefix flags noted below).
Shared here (not duplicated in `Kernel.lean`) since both `Core.lean`'s own
`type`/`classifier`/`feature` and `Kernel.lean`'s nine classifier-like keywords need
it to parse real KerML text like `Base.kerml`'s `abstract classifier Anything`. -/
declare_syntax_cat kermlAbstractFlag
syntax "abstract " : kermlAbstractFlag

/-- A multiplicity bound: a bare integer or `*` (unbounded). -/
declare_syntax_cat kermlMultBound
syntax num : kermlMultBound
syntax "*" : kermlMultBound

/-- KerML §8.2.5.11 `MultiplicityBounds`, simplified: `[N]` (single bound) or
`[N..M]` (range). Real `[...]` brackets from `Base.kerml` (`Anything[1]`,
`[1..*]`, `[0..1]`, ...) now parse; the bound *values* aren't stored anywhere,
though -- `MultiplicityRange`'s own Lean structure (`Kernel.lean`) has zero stored
fields, `lowerBound`/`upperBound`/`bound` all being derived Expression-valued
attributes this project's "structural only" scope already omits (see `Root.lean`'s
header). Parsing the bracket just lets real text containing one be consumed;
`kernelDecl`'s standalone `multiplicity` keyword (`Kernel.lean`) is what actually
produces a `MultiplicityRange` element. -/
declare_syntax_cat kermlMult
syntax "[" kermlMultBound "]" : kermlMult
syntax "[" kermlMultBound ".." kermlMultBound "]" : kermlMult

/-- KerML `QualifiedName`: `A` or `A::B::C`. Used at every *reference* position below
(a `specializes`/`typed by`/`subsets`/... target, or either operand of a standalone
relationship declaration) -- never for a *primary* declared name, which stays plain
`ident` (KerML's own `Identification`, not `QualifiedName`). Elaborates to a `String`
(`qualNameStr`, "::"-joined) used the same way a bare reference `ident`'s
`.getId.toString` always was -- still no symbol table, so `Anything::self` becomes a
stub carrying the string `"Anything::self"`, not an actual lookup of `Anything`'s
real `self` member; this is a strictly more faithful *label* for the reference than
dropping the qualifier ever was, not a resolution mechanism. -/
declare_syntax_cat kermlQualName
syntax ident ("::" ident)* : kermlQualName

def qualNameStr : TSyntax `kermlQualName → String
  | `(kermlQualName| $x:ident $[:: $xs:ident]*) =>
    String.intercalate "::" ((#[x] ++ xs).toList.map (·.getId.toString))
  | _ => "?"

/-- `kermlQualName`-taking counterparts of `kTypeStubTerm`/`classifierStubTerm`/
`featureStubTerm` above, for reference positions (everywhere those three were
previously called with a bare `ident` *target*, as opposed to a primary declared
name, which stays `ident`-based). -/
def kTypeStubTermQ (q : TSyntax `kermlQualName) : MacroM (TSyntax `term) :=
  `(mkKTypeStub $(quote (qualNameStr q)))
def classifierStubTermQ (q : TSyntax `kermlQualName) : MacroM (TSyntax `term) :=
  `(mkClassifierStub $(quote (qualNameStr q)))
def featureStubTermQ (q : TSyntax `kermlQualName) : MacroM (TSyntax `term) :=
  `(mkFeatureStub $(quote (qualNameStr q)))

/-- `doc "..."` stub -- see that production's own doc comment for the `/* ... */`
simplification. `elementId` is a fixed placeholder (uniqueness not enforced anywhere
else in this grammar either). -/
def mkDocumentationStub (body : String) : Documentation := { elementId := "doc", body := body }
/-- Fully-qualified name required here (unlike `KType.elt`/`Classifier.elt`/etc.
above, which live in *this* file's own `KerML.Core` namespace): `Documentation` is
declared in `Root.lean`'s `KerML.Root` namespace, and dot notation (`d.elt`) resolves
against a type's own declaring namespace, not wherever an extension `def` happens to
be written -- `def Documentation.elt` here would silently become
`KerML.Core.Documentation.elt`, invisible to `d.elt` for a real
`KerML.Root.Documentation`. `_root_.` is required too: merely writing
`KerML.Root.Documentation.elt` while *inside* `namespace KerML.Core` still nests
under the current namespace (`KerML.Core.KerML.Root.Documentation.elt`) rather than
replacing it -- `_root_.` anchors the name at the true top level. -/
def _root_.KerML.Root.Documentation.elt (d : Documentation) : Element := d.toComment.toAnnotatingElement.toElement

declare_syntax_cat kermlDecl

/-- KerML `TypeBody`/`FeatureBody`-style bodies: `;` (no owned members) or `{
kermlDecl* }` -- real nested member declarations, e.g. `Base.kerml`'s `classifier
Anything { feature self ... }`. `kermlDecl*` (not a dedicated "feature member only"
subgrammar) is deliberately over-permissive -- real KerML restricts body content to
`NonFeatureMember | FeatureMember | AliasMember | Import`, but reusing the full
`kermlDecl` category directly keeps this addition small, and every real nested
declaration this project's `#check`s exercise (`Base.kerml`'s nested `feature`s) is a
valid `kermlDecl` anyway. **Nested content contributes flat, sibling `Element`s to
the same list the outer declaration's own elaboration builds** -- consistent with
`kermlDecl`'s pre-existing "flat list of implied elements, not a nested graph"
principle (see that note above): a nested `feature self ...` becomes additional
entries alongside `Anything`'s own `Element` and its relationship `Element`s, not a
child linked to `Anything` via an owned-membership edge (that edge is exactly the
containment-graph machinery this whole project drops). Doc comments (`doc /* ... */`)
inside real bodies are **not** parsed here -- left for a future addition; smoke tests
below omit them, using genuinely empty or doc-free bodies instead of `Base.kerml`'s
literal text. -/
declare_syntax_cat kermlBody
syntax " ;" : kermlBody
syntax " {" kermlDecl* "}" : kermlBody

/-- KerML §8.2.4.1.1 `Type`, relationship-part subset (see scope note above): `[abstract]
type A [specializes B,+] [conjugates C] [disjoint from D,+] [unions U,+] [intersects
I,+] [differences Df,+] ;`. `abstract` is parsed (see `kermlAbstractFlag` above) but
not yet threaded into `KType.isAbstract` -- still not a *stored* field from this
concrete-syntax layer's own text, same status as before, just no longer a token that
blocks parsing real `abstract`-prefixed declarations like `Base.kerml`'s. -/
syntax (name := kermlType) (kermlAbstractFlag)? "type " ident
  (" specializes " kermlQualName,+)?
  (" conjugates " kermlQualName)?
  (" disjoint" " from " kermlQualName,+)?
  (" unions " kermlQualName,+)?
  (" intersects " kermlQualName,+)?
  (" differences " kermlQualName,+)?
  kermlBody : kermlDecl

/-- KerML §8.2.4.2.1 `Classifier`, same shape as `Type` above except `specializes`
produces `Subclassification` (not generic `Specialization`), per
`SuperclassingPart : OwnedSubclassification`. -/
syntax (name := kermlClassifier) (kermlAbstractFlag)? "classifier " ident
  (" specializes " kermlQualName,+)?
  (" conjugates " kermlQualName)?
  (" disjoint" " from " kermlQualName,+)?
  (" unions " kermlQualName,+)?
  (" intersects " kermlQualName,+)?
  (" differences " kermlQualName,+)?
  kermlBody : kermlDecl

/-- KerML §8.2.4.3.1 `Feature`, relationship-part subset: `[abstract] feature f
([typed by T,+] | [: T,+]) [mult] [subsets S,+] [references R] [crosses X] [redefines
D,+] [chains C] [inverse of V] [featured by F,+] ;`. Bare `: T,+` is an alternate
spelling of `typed by T,+` (KerML's `TYPED_BY = ':' | 'typed' 'by'`, only the
keyword form was covered before) -- both feed the same `FeatureTyping` elaboration.
`[mult]` (`kermlMult` above) is parsed but not stored, matching that category's own
note. -/
syntax (name := kermlFeature) (kermlAbstractFlag)? "feature " ident
  (" typed" " by " kermlQualName,+)?
  (" : " kermlQualName,+)?
  (kermlMult)?
  (" subsets " kermlQualName,+)?
  (" references " kermlQualName)?
  (" crosses " kermlQualName)?
  (" redefines " kermlQualName,+)?
  (" chains " kermlQualName)?
  (" inverse" " of " kermlQualName)?
  (" featured" " by " kermlQualName,+)?
  kermlBody : kermlDecl

/-- KerML §8.2.4.1.2 `Specialization`, standalone form: `subtype A specializes B ;`.
Both `A`/`B` are `QualifiedName` references (`SpecificType`/`GeneralType`), not
declarations -- unlike `type`/`classifier`/`feature`'s own primary name, neither
operand here is ever a fresh declaration. -/
syntax "subtype " kermlQualName " specializes " kermlQualName " ;" : kermlDecl
/-- KerML §8.2.4.1.3 `Conjugation`, standalone form: `conjugate A conjugates B ;`. -/
syntax "conjugate " kermlQualName " conjugates " kermlQualName " ;" : kermlDecl
/-- KerML §8.2.4.1.4 `Disjoining`, standalone form: `disjoint A from B ;`. -/
syntax "disjoint " kermlQualName " from " kermlQualName " ;" : kermlDecl
/-- KerML §8.2.4.2.2 `Subclassification`, standalone form: `subclassifier A specializes
B ;`. -/
syntax "subclassifier " kermlQualName " specializes " kermlQualName " ;" : kermlDecl
/-- KerML §8.2.4.3.2 `FeatureTyping`, standalone form: `typing F typed by T ;`. -/
syntax "typing " kermlQualName " typed" " by " kermlQualName " ;" : kermlDecl
/-- KerML §8.2.4.3.3 `Subsetting`, standalone form: `subset A subsets B ;`. -/
syntax "subset " kermlQualName " subsets " kermlQualName " ;" : kermlDecl
/-- KerML §8.2.4.3.4 `Redefinition`, standalone form: `redefinition A redefines B ;`. -/
syntax "redefinition " kermlQualName " redefines " kermlQualName " ;" : kermlDecl
/-- KerML §8.2.4.3.6 `FeatureInverting`, standalone form: `inverse A of B ;`. -/
syntax "inverse " kermlQualName " of " kermlQualName " ;" : kermlDecl
/-- KerML §8.2.4.3.7 `TypeFeaturing`, standalone form: `featuring A by B ;` (distinct
keyword from `Feature`'s inline `featured by` part above, per the spec). -/
syntax "featuring " kermlQualName " by " kermlQualName " ;" : kermlDecl

/-- KerML `Documentation` (`Root.lean`): real KerML writes `doc /* ... */`, a
C-style block comment whose contents *are* the documentation text -- lexing that
needs a custom low-level parser this project doesn't attempt (every other production
here is built from existing token categories -- `ident`/`num`/`str`/literal keyword
atoms -- never a raw custom one). `doc "..."` (a plain quoted string, Lean's own
`str` token) stands in for it: same simplified-surface/faithful-structure trade this
grammar already makes throughout (`;` for `{ ... }`, bare `ident` for
`QualifiedName`, before those were separately closed) -- `Base.kerml`'s literal
`doc /* This package defines... */` becomes `doc "This package defines..."` in the
smoke tests below, not its exact text. Valid as a nested `kermlDecl` (so it appears
inside a `kermlBody` alongside sibling declarations, matching `Base.kerml`'s own
`classifier Anything { doc ... feature self ... }` shape) or standalone. Produces a
`Documentation` element -- per this grammar's established "no containment graph"
principle, its *ownership* (which element it documents) isn't modeled, only its
existence as a sibling `Element`, same as every other nested declaration. -/
syntax "doc " str : kermlDecl

mutual

/-- `kermlDecl` → `Array (TSyntax term)`, one entry per implied `Element` (see the
scope note above for why a flat array, rather than a single value, is the faithful
elaboration target). Callers concatenate freely; only the top-level `kerml%` trigger
wraps the final result into a `List Element` term via `mkListTerm` -- matching
`kermlExpr`'s own convention (`Kernel.lean`), adopted here too once nested `kermlBody`
content needed the same composability. -/
partial def elabKermlDecl : TSyntax `kermlDecl → MacroM (Array (TSyntax `term))
  | `(kermlDecl| $[$_abs:kermlAbstractFlag]? type $a:ident
        $[specializes $specs,*]?
        $[conjugates $conj:kermlQualName]?
        $[disjoint from $disj,*]?
        $[unions $uni,*]?
        $[intersects $inter,*]?
        $[differences $diff,*]?
        $body:kermlBody) => do
    let an := a.getId.toString
    let aT ← kTypeStubTerm a
    let specElems ← match specs with
      | some ss => ss.getElems.mapM (fun g => do
          let gT ← kTypeStubTermQ g
          let rel ← mkSpecializationTerm aT gT an (qualNameStr g)
          `(($rel).elt))
      | none => pure #[]
    let conjElems ← match conj with
      | some c => do
          let cT ← kTypeStubTermQ c
          let rel ← mkConjugationTerm aT cT an (qualNameStr c)
          pure #[← `(($rel).elt)]
      | none => pure #[]
    let disjElems ← match disj with
      | some ds => ds.getElems.mapM (fun g => do
          let gT ← kTypeStubTermQ g
          let rel ← mkDisjoiningTerm aT gT an (qualNameStr g)
          `(($rel).elt))
      | none => pure #[]
    let uniElems ← match uni with
      | some us => us.getElems.mapM (fun g => do
          let gT ← kTypeStubTermQ g
          let rel ← mkUnioningTerm gT (qualNameStr g)
          `(($rel).elt))
      | none => pure #[]
    let interElems ← match inter with
      | some is' => is'.getElems.mapM (fun g => do
          let gT ← kTypeStubTermQ g
          let rel ← mkIntersectingTerm gT (qualNameStr g)
          `(($rel).elt))
      | none => pure #[]
    let diffElems ← match diff with
      | some ds => ds.getElems.mapM (fun g => do
          let gT ← kTypeStubTermQ g
          let rel ← mkDifferencingTerm gT (qualNameStr g)
          `(($rel).elt))
      | none => pure #[]
    let bodyElems ← elabKermlBody body
    pure (#[← `(($aT).elt)] ++ specElems ++ conjElems ++ disjElems ++ uniElems ++ interElems ++ diffElems ++ bodyElems)
  | `(kermlDecl| $[$_abs:kermlAbstractFlag]? classifier $a:ident
        $[specializes $specs,*]?
        $[conjugates $conj:kermlQualName]?
        $[disjoint from $disj,*]?
        $[unions $uni,*]?
        $[intersects $inter,*]?
        $[differences $diff,*]?
        $body:kermlBody) => do
    let an := a.getId.toString
    let aT ← classifierStubTerm a
    let specElems ← match specs with
      | some ss => ss.getElems.mapM (fun g => do
          let gT ← classifierStubTermQ g
          let rel ← mkSubclassificationTerm aT gT an (qualNameStr g)
          `(($rel).elt))
      | none => pure #[]
    let conjElems ← match conj with
      | some c => do
          let cT ← kTypeStubTermQ c
          let rel ← mkConjugationTerm (← `(($aT).toKType)) cT an (qualNameStr c)
          pure #[← `(($rel).elt)]
      | none => pure #[]
    let disjElems ← match disj with
      | some ds => ds.getElems.mapM (fun g => do
          let gT ← kTypeStubTermQ g
          let rel ← mkDisjoiningTerm (← `(($aT).toKType)) gT an (qualNameStr g)
          `(($rel).elt))
      | none => pure #[]
    let uniElems ← match uni with
      | some us => us.getElems.mapM (fun g => do
          let gT ← kTypeStubTermQ g
          let rel ← mkUnioningTerm gT (qualNameStr g)
          `(($rel).elt))
      | none => pure #[]
    let interElems ← match inter with
      | some is' => is'.getElems.mapM (fun g => do
          let gT ← kTypeStubTermQ g
          let rel ← mkIntersectingTerm gT (qualNameStr g)
          `(($rel).elt))
      | none => pure #[]
    let diffElems ← match diff with
      | some ds => ds.getElems.mapM (fun g => do
          let gT ← kTypeStubTermQ g
          let rel ← mkDifferencingTerm gT (qualNameStr g)
          `(($rel).elt))
      | none => pure #[]
    let bodyElems ← elabKermlBody body
    pure (#[← `(($aT).elt)] ++ specElems ++ conjElems ++ disjElems ++ uniElems ++ interElems ++ diffElems ++ bodyElems)
  | `(kermlDecl| $[$_abs:kermlAbstractFlag]? feature $a:ident
        $[typed by $tys,*]?
        $[: $tys2,*]?
        $[$_mult:kermlMult]?
        $[subsets $subs,*]?
        $[references $refF:kermlQualName]?
        $[crosses $crossF:kermlQualName]?
        $[redefines $redefs,*]?
        $[chains $chainF:kermlQualName]?
        $[inverse of $invF:kermlQualName]?
        $[featured by $feats,*]?
        $body:kermlBody) => do
    let an := a.getId.toString
    let aT ← featureStubTerm a
    let tyTargets := (tys.map (·.getElems) |>.getD #[]) ++ (tys2.map (·.getElems) |>.getD #[])
    let tyElems ← tyTargets.mapM (fun g => do
        let gT ← kTypeStubTermQ g
        let rel ← mkFeatureTypingTerm aT gT an (qualNameStr g)
        `(($rel).elt))
    let subElems ← match subs with
      | some ss => ss.getElems.mapM (fun g => do
          let gT ← featureStubTermQ g
          let rel ← mkSubsettingTerm aT gT an (qualNameStr g)
          `(($rel).elt))
      | none => pure #[]
    let refElems ← match refF with
      | some g => do
          let gT ← featureStubTermQ g
          let rel ← mkReferenceSubsettingTerm aT gT an (qualNameStr g)
          pure #[← `(($rel).elt)]
      | none => pure #[]
    let crossElems ← match crossF with
      | some g => do
          let gT ← featureStubTermQ g
          let rel ← mkCrossSubsettingTerm aT gT an (qualNameStr g)
          pure #[← `(($rel).elt)]
      | none => pure #[]
    let redefElems ← match redefs with
      | some rs => rs.getElems.mapM (fun g => do
          let gT ← featureStubTermQ g
          let rel ← mkRedefinitionTerm aT gT an (qualNameStr g)
          `(($rel).elt))
      | none => pure #[]
    let chainElems ← match chainF with
      | some g => do
          let gT ← featureStubTermQ g
          let rel ← mkFeatureChainingTerm aT gT an (qualNameStr g)
          pure #[← `(($rel).elt)]
      | none => pure #[]
    let invElems ← match invF with
      | some g => do
          let gT ← featureStubTermQ g
          let rel ← mkFeatureInvertingTerm aT gT an (qualNameStr g)
          pure #[← `(($rel).elt)]
      | none => pure #[]
    let featElems ← match feats with
      | some ts => ts.getElems.mapM (fun g => do
          let gT ← kTypeStubTermQ g
          let rel ← mkTypeFeaturingTerm aT gT an (qualNameStr g)
          `(($rel).elt))
      | none => pure #[]
    let bodyElems ← elabKermlBody body
    pure (#[← `(($aT).elt)] ++ tyElems ++ subElems ++ refElems ++ crossElems ++ redefElems ++
      chainElems ++ invElems ++ featElems ++ bodyElems)
  | `(kermlDecl| subtype $a:kermlQualName specializes $b:kermlQualName ;) => do
    let aT ← kTypeStubTermQ a; let bT ← kTypeStubTermQ b
    let rel ← mkSpecializationTerm aT bT (qualNameStr a) (qualNameStr b)
    pure #[← `(($rel).elt)]
  | `(kermlDecl| conjugate $a:kermlQualName conjugates $b:kermlQualName ;) => do
    let aT ← kTypeStubTermQ a; let bT ← kTypeStubTermQ b
    let rel ← mkConjugationTerm aT bT (qualNameStr a) (qualNameStr b)
    pure #[← `(($rel).elt)]
  | `(kermlDecl| disjoint $a:kermlQualName from $b:kermlQualName ;) => do
    let aT ← kTypeStubTermQ a; let bT ← kTypeStubTermQ b
    let rel ← mkDisjoiningTerm aT bT (qualNameStr a) (qualNameStr b)
    pure #[← `(($rel).elt)]
  | `(kermlDecl| subclassifier $a:kermlQualName specializes $b:kermlQualName ;) => do
    let aT ← classifierStubTermQ a; let bT ← classifierStubTermQ b
    let rel ← mkSubclassificationTerm aT bT (qualNameStr a) (qualNameStr b)
    pure #[← `(($rel).elt)]
  | `(kermlDecl| typing $a:kermlQualName typed by $b:kermlQualName ;) => do
    let aT ← featureStubTermQ a; let bT ← kTypeStubTermQ b
    let rel ← mkFeatureTypingTerm aT bT (qualNameStr a) (qualNameStr b)
    pure #[← `(($rel).elt)]
  | `(kermlDecl| subset $a:kermlQualName subsets $b:kermlQualName ;) => do
    let aT ← featureStubTermQ a; let bT ← featureStubTermQ b
    let rel ← mkSubsettingTerm aT bT (qualNameStr a) (qualNameStr b)
    pure #[← `(($rel).elt)]
  | `(kermlDecl| redefinition $a:kermlQualName redefines $b:kermlQualName ;) => do
    let aT ← featureStubTermQ a; let bT ← featureStubTermQ b
    let rel ← mkRedefinitionTerm aT bT (qualNameStr a) (qualNameStr b)
    pure #[← `(($rel).elt)]
  | `(kermlDecl| inverse $a:kermlQualName of $b:kermlQualName ;) => do
    let aT ← featureStubTermQ a; let bT ← featureStubTermQ b
    let rel ← mkFeatureInvertingTerm aT bT (qualNameStr a) (qualNameStr b)
    pure #[← `(($rel).elt)]
  | `(kermlDecl| featuring $a:kermlQualName by $b:kermlQualName ;) => do
    let aT ← featureStubTermQ a; let bT ← kTypeStubTermQ b
    let rel ← mkTypeFeaturingTerm aT bT (qualNameStr a) (qualNameStr b)
    pure #[← `(($rel).elt)]
  | `(kermlDecl| doc $s:str) => do pure #[← `((mkDocumentationStub $s).elt)]
  | _ => Macro.throwUnsupported

/-- `kermlBody` → the flat `Array` of `Element` terms its nested `kermlDecl*` content
implies (`;`/empty `{}` contributes nothing) -- see `kermlBody`'s own declaration
above for why this stays flat rather than building any ownership linkage. -/
partial def elabKermlBody : TSyntax `kermlBody → MacroM (Array (TSyntax `term))
  | `(kermlBody| ;) => pure #[]
  | `(kermlBody| { $decls:kermlDecl* }) => do
    let subs ← decls.mapM elabKermlDecl
    pure (subs.foldl (· ++ ·) #[])
  | _ => pure #[]

end

/-- `kerml% <decl>` elaborates a `kermlDecl` into a `List Element` term, matching
`DSL.lean`'s own `domain%` trigger convention. -/
elab "kerml% " d:kermlDecl : term => do
  let elems ← Elab.liftMacroM (elabKermlDecl d)
  let stx ← Elab.liftMacroM (mkListTerm elems.toList)
  Elab.Term.elabTerm stx none

-- Smoke tests: real elaborations, type-checked by Lean, not parse-only stubs.
#check kerml% type Widget ;
#check kerml% type Occurrence specializes Anything ;
#check kerml% type Vehicle specializes Car, Truck conjugates VehicleMirror
  disjoint from Boat unions LandVehicle intersects PoweredThing differences Toy ;
#check kerml% classifier Car specializes Vehicle ;
#check kerml% feature mass typed by Real ;
#check kerml% feature wheelCount subsets partCount references sharedWheel
  crosses axleEnd redefines legacyWheelCount chains hub inverse of spoke
  featured by Car, Truck ;
#check kerml% subtype Occurrence specializes Anything ;
#check kerml% conjugate VehicleMirror conjugates Mirror ;
#check kerml% disjoint Boat from Car ;
#check kerml% subclassifier Car specializes Vehicle ;
#check kerml% typing mass typed by Real ;
#check kerml% subset wheelCount subsets partCount ;
#check kerml% redefinition wheelCount redefines legacyWheelCount ;
#check kerml% inverse spoke of hub ;
#check kerml% featuring mass by Car ;

-- Base.kerml's own real declarations (`Classifiers`/`Features` half -- see
-- Kernel.lean's own matching block for `DataValue`/the four `multiplicity`
-- ranges), now as close to the real file's literal text as this grammar gets:
-- real nesting, real clause order (`: T [mult] subsets ... chains ...`), real
-- `doc` placement, `things.that` as a real (Lean-tokenizer-compound) chain
-- target. Two things still don't match verbatim, both explicitly out of scope
-- (not requested, not reopened here): `doc /* ... */`'s literal block-comment
-- text (`"..."` stands in, see `doc`'s own production note) and the `nonunique`
-- flag (omitted from every feature below that has it in the real file).
#check kerml% abstract classifier Anything {
  doc "Anything is the top level generalized type in the language."
  feature self : Anything [1] subsets things chains things.that {
    doc "The source of a SelfLink of this thing to itself. self is thus a feature that relates everything to itself."
  }
}
#check kerml% abstract feature things : Anything [1..*] {
  doc "things is the top-level feature in the language."
  feature that : Anything [1] {
    doc "For each value of things, the featuring instance of that value."
  }
}
#check kerml% abstract feature dataValues : DataValue [0..*] subsets things {
  doc "dataValues is a specialization of things restricted to type DataValue."
}
#check kerml% abstract feature naturals : ScalarValues::Natural [0..*] subsets dataValues {
  doc "naturals is a specialization of dataValues restricted to type Natural."
}

end KerML.Core
