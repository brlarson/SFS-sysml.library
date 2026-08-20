/-
Lean 4 formalization of the KerML (Kernel Modeling Language, OMG SysML v2 Release,
"Kernel Modeling Language v1.0 Beta 3") **Kernel** package's metamodel: KerML §8.3.4
"Kernel Abstract Syntax" (§8.2.5 "Kernel Concrete Syntax" is cited for context only,
not implemented -- see the note at the end of this header). Builds on `Core.lean`
(itself building on `Root.lean`) the same way KerML's own Kernel package imports Core,
which imports Root (Figure 1, "KerML Syntax Layers") -- this completes the three-layer
KerML metamodel.

**Authoritative source note**: the generalization hierarchy here follows this repo's
own `sysml.library/Kernel Libraries/Kernel Semantic Library/KerML.kerml` (a
reflective KerML model of the abstract syntax, maintained in this fork) rather than
the generic OMG spec PDF wherever the two disagree -- `KerML.kerml` takes precedence
for an "SFS-sysml.library"-specific formalization like this one. Two places they
disagree, both marked `//SFS:` in `KerML.kerml` itself: `Expression` specializes
`Feature` directly (not `Step`), and `Function` (`KFunction`) specializes `Classifier`
directly (not `Behavior`) -- see those two structures' own doc comments below for the
detail. `Root.lean`/`Core.lean` were checked against `KerML.kerml` too and already
matched it exactly; only this file needed correcting (verified 2026-08-20, after
initially being written from the PDF's §8.3.4 alone).

Same scope discipline as `Root.lean`/`Core.lean` -- see `Root.lean`'s header for the
full rationale: `extends` mirrors the generalization hierarchy; only non-derived
(stored) attributes become fields; containment/graph-structural attributes are
omitted; OCL constraints are noted in prose, not encoded or proved. **Additionally
omitted here** (new relative to Root/Core, called out because Kernel's spec actually
has some): spec-defined **operations** (`evaluate`, `modelLevelEvaluable`,
`instantiatedType()`, ...) -- these are behavioral/computed, not stored data, so like
derived attributes they're noted in doc comments where load-bearing, never encoded as
Lean functions.

**Naming note** (see `Core.lean`'s own note on `Type`→`KType` for the precedent):
three Kernel metaclass names collide with Lean 4 keywords/core-library names and are
renamed the same way:
- `Class` → `KClass` (`class` is a Lean keyword).
- `Structure` → `KStructure` (`structure` is a Lean keyword).
- `Function` → `KFunction` (`Function` is a Lean 4 core namespace -- `Function.comp`,
  `Function.const`, etc. -- a bare `structure Function` would shadow it for the rest
  of this file).

**Scalar literal value types**: KerML's own numeric/string data types (`Boolean`,
`Integer`, `Rational`/`Real`, `String`) are Kernel Semantic Library types, not Lean
types. Consistent with "structural only" (no attempt to formalize the Kernel Semantic
Library's own type tower here), literal-valued attributes use the nearest plain Lean
type: `Bool`, `Int`, `String`, and `Float` standing in for KerML's `Real` (no
precision/rounding claim intended -- just a stored-value placeholder).

**Multiple inheritance**: several Kernel metaclasses specialize two KerML supertypes
at once (`Association : Classifier, Relationship`; `Connector : Relationship,
Feature`; ...), which Lean 4's `structure ... extends A, B` supports directly
(including through the diamond shared ancestry every case here has, since `Classifier`
and `Relationship`/`Feature` all eventually reach `Element`) -- built and verified via
`lake build`, not assumed.

**KerML §8.2.5 Kernel Concrete Syntax**: below the abstract-syntax structures, this
file also adds real `syntax`/`elab` productions for a subset of Kernel's textual
notation, in the same house style `Assert.lean` and `Core.lean`'s own concrete-syntax
section established. Two independent pieces: `kernelDecl` (declaration keywords --
`datatype`/`class`/`struct`/`assoc`/`behavior`/`function`/`predicate`/`interaction`/
`package`, reusing `Core.lean`'s relationship-builder helpers directly since `open
KerML.Core` brings them into scope) and `kermlExpr` (a real operator-precedence
expression grammar -- literals, arithmetic/comparison/logical operators, feature
chaining, indexing, invocation, `new`-construction). See that section's own header
comment for its scope and the (substantial) list of KerML §8.2.5.8 operators
deliberately left out.
-/

import Root
import Core
import Assert
import Lean

namespace KerML.Kernel

open KerML.Root
open KerML.Core
open Lean

/-! ## 8.3.4.1 Data Types -/

/-- KerML §8.3.4.1 `DataType`. A `Classifier` of things distinguishable only by how
they relate to other things via `Feature`s (value/structural-equality semantics, not
identity). Constraint (not encoded): must (in/directly) specialize `Base::DataValue`;
must not specialize a `KClass` or `Association`. -/
structure DataType extends Classifier where
  deriving Repr

/-! ## 8.3.4.2 Classes -/

/-- KerML §8.3.4.2 `Class` (renamed `KClass`, see file header). A `Classifier` of
things distinguishable by identity regardless of how they relate to other things
(contrasts with `DataType`). Constraint (not encoded): must specialize
`Occurrences::Occurrence`; must not specialize a `DataType`. -/
structure KClass extends Classifier where
  deriving Repr

/-! ## 8.3.4.3 Structures -/

/-- KerML §8.3.4.3 `Structure` (renamed `KStructure`, see file header). A `KClass` of
objects that are primarily structural rather than behavioral -- not themselves
`Behavior`s, but may be involved in or act as performer of one. Constraint (not
encoded): must specialize `Objects::Object`; must not specialize a `Behavior`. -/
structure KStructure extends KClass where
  deriving Repr

/-! ## 8.3.4.4 Associations -/

/-- KerML §8.3.4.4 `Association`. A `Relationship`-and-`Classifier` that classifies
links between things; its end `Feature`s' co-domains are the related types.
Constraint (not encoded): binary form must specialize `Links::binaryLink`; a
concrete (non-abstract) `Association` must have ≥2 related types. -/
structure Association extends Classifier, Relationship where
  deriving Repr

/-- KerML §8.3.4.4 `AssociationStructure`. An `Association` that is also a
`KStructure`, classifying link objects that are both links and objects -- non-end
features may vary over the object's lifetime, but end-feature values are fixed.
Constraint (not encoded): binary form must specialize `Objects::BinaryLinkObject`. -/
structure AssociationStructure extends Association, KStructure where
  deriving Repr

/-! ## 8.3.4.5 Connectors -/

/-- KerML §8.3.4.5 `Connector`. A usage of `Association`s whose links are restricted
to instances of the `Connector`'s featuring `Type`(s), further restricted to links
between values of `Feature`s on instances of its domain. Constraint (not encoded):
binary form must specialize `Links::binaryLinks`; a concrete `Connector` must have
≥2 related features. -/
structure Connector extends Feature, Relationship where
  deriving Repr

/-- KerML §8.3.4.5 `BindingConnector`. A binary `Connector` requiring its two related
features to identify the same thing (equal values). Constraint (not encoded): must
have exactly 2 related features; must specialize `Links::selfLinks`. -/
structure BindingConnector extends Connector where
  deriving Repr

/-- KerML §8.3.4.5 `Succession`. A binary `Connector` requiring its related features
to happen separately in time (temporal ordering, not concurrency). Constraint (not
encoded): must specialize the `Feature` `Occurrences::happensBeforeLinks`. -/
structure Succession extends Connector where
  deriving Repr

/-! ## 8.3.4.6 Behaviors -/

/-- KerML §8.3.4.6 `Behavior`. Coordinates occurrences of other `Behavior`s and
changes in objects; can be decomposed into `Step`s and characterized by parameters.
Constraint (not encoded): must specialize `Performances::Performance`; must not
specialize a `KStructure`. -/
structure Behavior extends KClass where
  deriving Repr

/-- KerML §8.3.4.6 `Step`. A `Feature` typed by one or more `Behavior`s; coordinates
performance of other `Behavior`s within a `Behavior`, supports temporal ordering, and
can be connected via `Flow`s. -/
structure Step extends Feature where
  deriving Repr

/-- KerML §8.3.4.6 `ParameterMembership`. A `FeatureMembership` identifying its
member `Feature` as a parameter, always owned, always with a direction. Constraint
(not encoded): owning type must be a `Behavior`, a `Step`, or the result parameter of
a `ConstructorExpression`; the member feature's direction must match the (spec
operation, not encoded here) `parameterDirection()` -- `'in'` by default, overridden
to `'out'` by `ReturnParameterMembership` below. -/
structure ParameterMembership extends FeatureMembership where
  deriving Repr

/-! ## 8.3.4.7 Functions -/

/-- KerML §8.3.4.7 `Expression`. **Deviates from the OMG spec here**: the spec has
`Expression specializes Step`, but this repo's own `KerML.kerml` (the maintained
reflective abstract-syntax model, authoritative over the generic OMG PDF for this
fork) has `Expression specializes Feature` directly instead, marked
`//SFS: Expression specializes Feature, added 'parameter'` -- part of a pair of
changes (with `KFunction` below) making `Expression`/`Function` evaluation
"immediate" rather than routed through `Step`/`Behavior`'s general
Step-of-a-Behavior machinery. `KerML.kerml`'s own top-of-file comment warns this
isn't reflected in the *abstract syntax* metaclass tree there either, so unexpected
errors are possible from metaclass reflection -- noted for parity, not applicable
here since this file doesn't model reflection. Always has a single result parameter
(redefining its function's result), enabling tree-structured interconnection of
`Expression`s. Constraint (not encoded): must specialize `Performances::evaluations`;
must have exactly one result parameter. -/
structure Expression extends Feature where
  deriving Repr

/-- KerML §8.3.4.7 `BooleanExpression`. A Boolean-valued `Expression` whose type is a
`Predicate`; represents the logical condition resulting from evaluating that
`Predicate`. Constraint (not encoded): must specialize
`Performances::booleanEvaluations`. -/
structure BooleanExpression extends Expression where
  deriving Repr

/-- KerML §8.3.4.7 `Function` (renamed `KFunction`, see file header). **Deviates from
the OMG spec here**: the spec has `Function specializes Behavior`, but this repo's own
`KerML.kerml` has `Function specializes Classifier` directly instead (with `Behavior`
commented out in the source), marked `//SFS: Function specializes Classifier to be
immediate` -- see `Expression`'s own doc comment above for the paired rationale
(immediate-evaluation semantics, not routed through `Behavior`/`Step`). Represents
performance of a calculation with an `out` parameter identified as its result,
possibly decomposed into `Expression`s. Constraint (not encoded): must specialize
`Performances::Evaluation`; must have exactly one `ReturnParameterMembership`. -/
structure KFunction extends Classifier where
  deriving Repr

/-- KerML §8.3.4.7 `Invariant`. A `BooleanExpression` asserted to have a specific
Boolean result: true if `isNegated = false`, false if `isNegated = true`. Constraint
(not encoded): must specialize `Performances::falseEvaluations` (if negated) or
`Performances::trueEvaluations` (otherwise). -/
structure Invariant extends BooleanExpression where
  isNegated : Bool := false
  deriving Repr

/-- KerML §8.3.4.7 `Predicate`. A `KFunction` whose result parameter has type
`Boolean` and multiplicity exactly `1..1`. Constraint (not encoded): must specialize
`Performances::BooleanEvaluation`. -/
structure Predicate extends KFunction where
  deriving Repr

/-- KerML §8.3.4.7 `ResultExpressionMembership`. A `FeatureMembership` indicating
that the owned result `Expression` provides the result values for the owning
`KFunction`/`Expression`, which must contain a matching `BindingConnector`.
Constraint (not encoded): owning type must be a `KFunction` or `Expression`. -/
structure ResultExpressionMembership extends FeatureMembership where
  deriving Repr

/-- KerML §8.3.4.7 `ReturnParameterMembership`. A `ParameterMembership` marking its
member `Feature` as the result parameter of a `KFunction` or `Expression`; direction
is always `out` (spec operation `parameterDirection()`, not encoded, leaf-redefined
to always return `'out'`). Constraint (not encoded): owning type must be a
`KFunction` or `Expression`. -/
structure ReturnParameterMembership extends ParameterMembership where
  deriving Repr

/-! ## 8.3.4.8 Expressions -/

/-- KerML §8.3.4.8 `InstantiationExpression`. **Abstract in the spec** ("is abstract,
with concrete subclasses `InvocationExpression` and `ConstructorExpression`" --
never directly instantiated, Lean doesn't enforce this). An `Expression` that
instantiates its instantiated type, binding some or all features of that type to
results of its arguments. Constraint (not encoded): must own its result parameter. -/
structure InstantiationExpression extends Expression where
  deriving Repr

/-- KerML §8.3.4.8 `InvocationExpression`. An `InstantiationExpression` whose
instantiated type must be a `Behavior` or a `Feature` typed by a single `Behavior`
(e.g. a `Step`); input parameters are bound to argument-`Expression` results. If the
instantiated type is/typed-by a `KFunction`, the result is that function's result;
otherwise the result is an instance of the instantiated type (like a behavioral
`ConstructorExpression`). Constraint (not encoded): must specialize its instantiated
type; all owned features other than result must have direction `in`. -/
structure InvocationExpression extends InstantiationExpression where
  deriving Repr

/-- KerML §8.3.4.8 `OperatorExpression`. An `InvocationExpression` whose `function`
is determined by resolving `operator` against the standard Kernel Function Library
packages (`BaseFunctions`/`DataFunctions`/`ControlFunctions`) -- common supertype for
`CollectExpression`/`FeatureChainExpression`/`IndexExpression`/`SelectExpression`
below, each of which value-constrains (not type-redefines; Lean has no refinement
types here) the inherited `operator` field to a fixed symbol, noted per-structure. -/
structure OperatorExpression extends InvocationExpression where
  operator : String
  deriving Repr

/-- KerML §8.3.4.8 `CollectExpression`. An `OperatorExpression` whose `operator` is
constrained (OCL, not encoded) to `"collect"`, resolving to
`ControlFunctions::collect`. -/
structure CollectExpression extends OperatorExpression where
  deriving Repr

/-- KerML §8.3.4.8 `ConstructorExpression`. An `InstantiationExpression` whose result
specializes its instantiated type, binding some/all features of that type to results
of its argument `Expression`s (i.e. "new"-style object construction). Constraint (not
encoded): must have no owned features other than result; each owned feature of
result must redefine exactly one public feature of the instantiated type. -/
structure ConstructorExpression extends InstantiationExpression where
  deriving Repr

/-- KerML §8.3.4.8 `FeatureChainExpression`. An `OperatorExpression` whose `operator`
is constrained (OCL, not encoded) to `"."`, resolving to `ControlFunctions::'.'`;
evaluates to the result of chaining the `result` `Feature` of its single argument
`Expression` with its target feature. -/
structure FeatureChainExpression extends OperatorExpression where
  deriving Repr

/-- KerML §8.3.4.8 `FeatureReferenceExpression`. An `Expression` whose result is
bound to a referent `Feature` -- i.e. references that feature's value. Constraint
(not encoded): must own a `BindingConnector` between referent and result. -/
structure FeatureReferenceExpression extends Expression where
  deriving Repr

/-- KerML §8.3.4.8 `IndexExpression`. An `OperatorExpression` whose `operator` is
constrained (OCL, not encoded) to `"#"`, resolving to `BasicFunctions::'#'`
(array/sequence indexing). -/
structure IndexExpression extends OperatorExpression where
  deriving Repr

/-- KerML §8.3.4.8 `LiteralExpression`. An `Expression` that provides a basic
`DataValue` as its result -- base type for the five literal-value expressions below.
Constraint (not encoded): must specialize `Performances::literalEvaluations`. -/
structure LiteralExpression extends Expression where
  deriving Repr

/-- KerML §8.3.4.8 `LiteralBoolean`. A `LiteralExpression` providing a Boolean
`value` as result. -/
structure LiteralBoolean extends LiteralExpression where
  value : Bool
  deriving Repr

/-- KerML §8.3.4.8 `LiteralInfinity`. A `LiteralExpression` providing the
positive-infinity value (`*`); result must have type `Positive` (constraint, not
encoded). -/
structure LiteralInfinity extends LiteralExpression where
  deriving Repr

/-- KerML §8.3.4.8 `LiteralInteger`. A `LiteralExpression` providing an Integer
`value` (`Int`) as result. -/
structure LiteralInteger extends LiteralExpression where
  value : Int
  deriving Repr

/-- KerML §8.3.4.8 `LiteralRational`. A `LiteralExpression` whose `value` is the
result -- `KerML.kerml` types this `Rational` (not `Real`, despite the OMG spec text
elsewhere calling it real-valued); `Float` stands in here regardless (see file
header), the same placeholder either way. -/
structure LiteralRational extends LiteralExpression where
  value : Float
  deriving Repr

/-- KerML §8.3.4.8 `LiteralString`. A `LiteralExpression` providing a String `value`
as result. -/
structure LiteralString extends LiteralExpression where
  value : String
  deriving Repr

/-- KerML §8.3.4.8 `MetadataAccessExpression`. An `Expression` whose result is a
sequence of `Metaclass` instances representing all `MetadataFeature` annotations of
the referenced element, plus a reflective `Metaclass` instance for that element's own
metaclass. Constraint (not encoded): must have ≥1 owned member that is not a
`FeatureMembership`. -/
structure MetadataAccessExpression extends Expression where
  deriving Repr

/-- KerML §8.3.4.8 `NullExpression`. An `Expression` that results in a null value.
Constraint (not encoded): must specialize `Performances::nullEvaluations`. -/
structure NullExpression extends Expression where
  deriving Repr

/-- KerML §8.3.4.8 `SelectExpression`. An `OperatorExpression` whose `operator` is
constrained (OCL, not encoded) to `"select"`, resolving to
`ControlFunctions::select`. -/
structure SelectExpression extends OperatorExpression where
  deriving Repr

/-! ## 8.3.4.9 Interactions -/

/-- KerML §8.3.4.9 `Flow`. A `Step` representing transfer of values from one
`Feature` to another; `Flow`s can take non-zero time to complete. Constraint (not
encoded): must specialize the `Step` `Transfers::transfers`; must have at most one
owned `PayloadFeature`. -/
structure Flow extends Connector, Step where
  deriving Repr

/-- KerML §8.3.4.9 `FlowEnd`. A `Feature` that is one of the connector ends giving
the source or target of a `Flow`. Constraint (not encoded): must be an end feature
(`isEnd = true`); owning type must be a `Flow`; must have exactly one owned
feature. -/
structure FlowEnd extends Feature where
  deriving Repr

/-- KerML §8.3.4.9 `Interaction`. A `Behavior` that is also an `Association`,
providing a context for multiple objects whose behaviors impact one another. -/
structure Interaction extends Association, Behavior where
  deriving Repr

/-- KerML §8.3.4.9 `PayloadFeature`. The owned feature of a `Flow` that identifies
the things carried by the kinds of transfers that are instances of the `Flow`.
Constraint (not encoded): must redefine `Transfers::Transfer::payload`. -/
structure PayloadFeature extends Feature where
  deriving Repr

/-- KerML §8.3.4.9 `SuccessionFlow`. A `Flow` that also provides temporal ordering --
classifies transfers that cannot start until the source occurrence completes, and
must complete before the target occurrence can start. Constraint (not encoded): must
specialize the `Step` `Transfers::flowTransfersBefore`. -/
structure SuccessionFlow extends Succession, Flow where
  deriving Repr

/-! ## 8.3.4.10 Feature Values -/

/-- KerML §8.3.4.10 `FeatureValue`. An `OwningMembership` identifying a member
`Expression` that provides the value of the `Feature` that owns it. The value can be
a bound value or initial value, and can be a concrete value or a default
(overridable) value; a `Feature` can have at most one `FeatureValue` (constraint, not
encoded). -/
structure FeatureValue extends OwningMembership where
  isDefault : Bool := false
  isInitial : Bool := false
  deriving Repr

/-! ## 8.3.4.11 Multiplicities -/

/-- KerML §8.3.4.11 `MultiplicityRange`. A `Multiplicity` whose value is the
inclusive range of natural numbers given by a lower-bound `Expression` result and an
upper-bound `Expression` result (`*` meaning unbounded above). All of `bound`/
`lowerBound`/`upperBound` are derived (omitted, per file header); the bound
`Expression`s themselves live in the owned-member graph this project doesn't model,
so this structure has no stored fields beyond `Multiplicity`'s. -/
structure MultiplicityRange extends Multiplicity where
  deriving Repr

/-! ## 8.3.4.12 Metadata -/

/-- KerML §8.3.4.12 `Metaclass`. A `KStructure` used to type `MetadataFeature`s --
the reflective classifier for metadata annotation instances. Constraint (not
encoded): must specialize `Metaobjects::Metaobject`. -/
structure Metaclass extends KStructure where
  deriving Repr

/-- KerML §8.3.4.12 `MetadataFeature`. A `Feature` that is also an
`AnnotatingElement`, used to annotate another element with metadata; typed by a
`Metaclass`. Constraint (not encoded): must have exactly one type, which must be a
non-abstract `Metaclass`; every (transitively) owned feature must have no declared
name and must redefine exactly one feature of that metaclass. -/
structure MetadataFeature extends AnnotatingElement, Feature where
  deriving Repr

/-! ## 8.3.4.13 Packages -/

/-- KerML §8.3.4.13 `ElementFilterMembership`. An `OwningMembership` between a
`Namespace` and a model-level-evaluable Boolean `Expression` (`condition`, derived,
omitted), asserting that imported members of the `Namespace` should be filtered
using it. Behavior is defined for specialized `Namespace` kinds (e.g. `Package`
below), not generically here. -/
structure ElementFilterMembership extends OwningMembership where
  deriving Repr

/-- KerML §8.3.4.13 `Package`. A `Namespace` used to group elements without
instance-level semantics; may have one or more model-level-evaluable filter-condition
`Expression`s (owned via `ElementFilterMembership`s, derived into `filterCondition`,
omitted) used to filter its imported memberships. -/
structure Package extends Namespace where
  deriving Repr

/-- KerML §8.3.4.13 `LibraryPackage`. A `Package` that is the container for a model
library; it and everything it (directly/indirectly) contains are library elements.
`isStandard` should only be true for `LibraryPackage`s in the standard Kernel Model
Libraries, or in normative model libraries for a language built on KerML. -/
structure LibraryPackage extends Package where
  isStandard : Bool := false
  deriving Repr

/-! ## Concrete syntax (KerML §8.2.5 "Kernel Concrete Syntax")

Two independent syntax/elaboration pieces, in `Assert.lean`/`Core.lean`'s house style.

### `kernelDecl` -- declaration keywords

Mirrors `Core.lean`'s `kermlDecl` `Type`/`Classifier` productions exactly (same
optional relationship parts, same "referenced names are scope-visible, stood in for
by a stub rather than resolved via a symbol table this project doesn't have"
treatment, same `;`-only body), just for nine more KerML §8.2.5 declaration keywords:
`datatype`/`class`/`struct`/`assoc`/`behavior`/`function`/`predicate`/`interaction`
(all "classifier-like" -- their `specializes` clause produces a `Subclassification`,
reusing `Core.lean`'s own `mkSubclassificationTerm`/`mkConjugationTerm`/
`mkDisjoiningTerm`/`mkUnioningTerm`/`mkIntersectingTerm`/`mkDifferencingTerm`/
`classifierStubTerm`/`kTypeStubTerm` directly, since `open KerML.Core` brings them
into scope) plus `package` (structurally different -- no relationship parts at all in
the real grammar, just a bare name). A genuinely separate category name from
`Core.lean`'s `kermlDecl` (not an extension of it) to avoid any risk of collision if
both files are ever imported together. **Not covered** (documented, matching
`Core.lean`'s own scope note): `AssociationStructure`/`BindingConnector`/
`Succession`/`Step`/`Expression`/`BooleanExpression`/`Invariant`/`Flow`/
`SuccessionFlow`/`Metaclass`/`LibraryPackage`/`MultiplicityRange` declaration forms,
and `FunctionBody`'s `return`/result-expression parts -- all use richer grammar
(binary connector ends, function bodies with owned steps, ...) that would need the
containment-graph machinery this whole project deliberately drops; a plain `;` body
is used everywhere here instead, exactly like `Core.lean`'s `Type`/`Classifier`. -/

/-- `.toClassifier`-style coercion to `Classifier`, uniform across all nine
"classifier-like" declaration keywords below regardless of how deep their own
`extends` chain runs -- lets the shared elaboration helper call `.toClassifierC`
without caring which concrete type it's holding. -/
def DataType.toClassifierC (t : DataType) : Classifier := t.toClassifier
def KClass.toClassifierC (t : KClass) : Classifier := t.toClassifier
def KStructure.toClassifierC (t : KStructure) : Classifier := t.toKClass.toClassifier
def Association.toClassifierC (t : Association) : Classifier := t.toClassifier
def Behavior.toClassifierC (t : Behavior) : Classifier := t.toKClass.toClassifier
def KFunction.toClassifierC (t : KFunction) : Classifier := t.toClassifier
def Predicate.toClassifierC (t : Predicate) : Classifier := t.toKFunction.toClassifier
def Interaction.toClassifierC (t : Interaction) : Classifier := t.toAssociation.toClassifier

/-- `.toElement` for each of the nine, composed through `.toClassifierC` above. -/
def DataType.elt (t : DataType) : Element := t.toClassifierC.toKType.toNamespace.toElement
def KClass.elt (t : KClass) : Element := t.toClassifierC.toKType.toNamespace.toElement
def KStructure.elt (t : KStructure) : Element := t.toClassifierC.toKType.toNamespace.toElement
def Association.elt (t : Association) : Element := t.toClassifierC.toKType.toNamespace.toElement
def Behavior.elt (t : Behavior) : Element := t.toClassifierC.toKType.toNamespace.toElement
def KFunction.elt (t : KFunction) : Element := t.toClassifierC.toKType.toNamespace.toElement
def Predicate.elt (t : Predicate) : Element := t.toClassifierC.toKType.toNamespace.toElement
def Interaction.elt (t : Interaction) : Element := t.toClassifierC.toKType.toNamespace.toElement
def Package.elt (t : Package) : Element := t.toNamespace.toElement
def MultiplicityRange.elt (t : MultiplicityRange) : Element :=
  t.toMultiplicity.toFeature.toKType.toNamespace.toElement

def mkDataTypeStub (name : String) : DataType := { elementId := name, declaredName := some name }
def mkKClassStub (name : String) : KClass := { elementId := name, declaredName := some name }
def mkKStructureStub (name : String) : KStructure := { elementId := name, declaredName := some name }
def mkAssociationStub (name : String) : Association := { elementId := name, declaredName := some name }
def mkBehaviorStub (name : String) : Behavior := { elementId := name, declaredName := some name }
def mkKFunctionStub (name : String) : KFunction := { elementId := name, declaredName := some name }
def mkPredicateStub (name : String) : Predicate := { elementId := name, declaredName := some name }
def mkInteractionStub (name : String) : Interaction := { elementId := name, declaredName := some name }
def mkPackageStub (name : String) : Package := { elementId := name, declaredName := some name }

def dataTypeStubTerm (s : String) : MacroM (TSyntax `term) := `(mkDataTypeStub $(quote s))
def kClassStubTerm (s : String) : MacroM (TSyntax `term) := `(mkKClassStub $(quote s))
def kStructureStubTerm (s : String) : MacroM (TSyntax `term) := `(mkKStructureStub $(quote s))
def associationStubTerm (s : String) : MacroM (TSyntax `term) := `(mkAssociationStub $(quote s))
def behaviorStubTerm (s : String) : MacroM (TSyntax `term) := `(mkBehaviorStub $(quote s))
def kFunctionStubTerm (s : String) : MacroM (TSyntax `term) := `(mkKFunctionStub $(quote s))
def predicateStubTerm (s : String) : MacroM (TSyntax `term) := `(mkPredicateStub $(quote s))
def interactionStubTerm (s : String) : MacroM (TSyntax `term) := `(mkInteractionStub $(quote s))
def packageStubTerm (s : String) : MacroM (TSyntax `term) := `(mkPackageStub $(quote s))
def mkMultiplicityRangeStub (name : String) : MultiplicityRange := { elementId := name, declaredName := some name }
def multiplicityRangeStubTerm (s : String) : MacroM (TSyntax `term) := `(mkMultiplicityRangeStub $(quote s))
def MetadataFeature.elt (t : MetadataFeature) : Element := t.toFeature.toKType.toNamespace.toElement
def mkMetadataFeatureStub (name : String) : MetadataFeature := { elementId := name, declaredName := some name }

/-- Shared elaboration body for all nine "classifier-like" declaration keywords: one
stub for the primary declared name (via `mkStub`), plus one relationship `Element`
per `specializes`/`conjugates`/`disjoint from`/`unions`/`intersects`/`differences`
target, exactly mirroring `Core.lean`'s `type`/`classifier` elaboration (which this
calls into directly). -/
def classifierLikeDeclElems (mkStub : String → MacroM (TSyntax `term)) (a : TSyntax `ident)
    (specs : Option (Syntax.TSepArray `kermlQualName ",")) (conj : Option (TSyntax `kermlQualName))
    (disj uni inter diff : Option (Syntax.TSepArray `kermlQualName ",")) : MacroM (Array (TSyntax `term)) := do
  let an := a.getId.toString
  let aT ← mkStub an
  let aC ← `(($aT).toClassifierC)
  let aK ← `(($aC).toKType)
  let specElems ← match specs with
    | some ss => ss.getElems.mapM (fun g => do
        let gC ← classifierStubTermQ g
        let rel ← mkSubclassificationTerm aC gC an (qualNameStr g)
        `(($rel).elt))
    | none => pure #[]
  let conjElems ← match conj with
    | some c => do
        let cT ← kTypeStubTermQ c
        let rel ← mkConjugationTerm aK cT an (qualNameStr c)
        pure #[← `(($rel).elt)]
    | none => pure #[]
  let disjElems ← match disj with
    | some ds => ds.getElems.mapM (fun g => do
        let gT ← kTypeStubTermQ g
        let rel ← mkDisjoiningTerm aK gT an (qualNameStr g)
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
  pure (#[← `(($aT).elt)] ++ specElems ++ conjElems ++ disjElems ++ uniElems ++ interElems ++ diffElems)

declare_syntax_cat kernelDecl
/-- Declared here (category name only, matching `Assert.lean`'s own "declare every
category up front" lesson for forward references) so `predicate`'s own `syntax`
declaration below can end in it; its actual productions -- which need `kermlExpr`,
declared much later in this file -- are added alongside `elabKermlPredBody` after
that section. See that declaration's own doc comment for why `predicate` alone (not
the other eight classifier-like keywords) needs a body category richer than
`kermlBody`. -/
declare_syntax_cat kermlPredBody

syntax (kermlAbstractFlag)? "datatype " ident (" specializes " kermlQualName,+)? (" conjugates " kermlQualName)?
  (" disjoint" " from " kermlQualName,+)? (" unions " kermlQualName,+)? (" intersects " kermlQualName,+)?
  (" differences " kermlQualName,+)? kermlBody : kernelDecl
syntax (kermlAbstractFlag)? "class " ident (" specializes " kermlQualName,+)? (" conjugates " kermlQualName)?
  (" disjoint" " from " kermlQualName,+)? (" unions " kermlQualName,+)? (" intersects " kermlQualName,+)?
  (" differences " kermlQualName,+)? kermlBody : kernelDecl
syntax (kermlAbstractFlag)? "struct " ident (" specializes " kermlQualName,+)? (" conjugates " kermlQualName)?
  (" disjoint" " from " kermlQualName,+)? (" unions " kermlQualName,+)? (" intersects " kermlQualName,+)?
  (" differences " kermlQualName,+)? kermlBody : kernelDecl
syntax (kermlAbstractFlag)? "assoc " ident (" specializes " kermlQualName,+)? (" conjugates " kermlQualName)?
  (" disjoint" " from " kermlQualName,+)? (" unions " kermlQualName,+)? (" intersects " kermlQualName,+)?
  (" differences " kermlQualName,+)? kermlBody : kernelDecl
syntax (kermlAbstractFlag)? "behavior " ident (" specializes " kermlQualName,+)? (" conjugates " kermlQualName)?
  (" disjoint" " from " kermlQualName,+)? (" unions " kermlQualName,+)? (" intersects " kermlQualName,+)?
  (" differences " kermlQualName,+)? kermlBody : kernelDecl
syntax (kermlAbstractFlag)? "function " ident (" specializes " kermlQualName,+)? (" conjugates " kermlQualName)?
  (" disjoint" " from " kermlQualName,+)? (" unions " kermlQualName,+)? (" intersects " kermlQualName,+)?
  (" differences " kermlQualName,+)? kermlBody : kernelDecl
syntax (kermlAbstractFlag)? "predicate " ident (" specializes " kermlQualName,+)? (" conjugates " kermlQualName)?
  (" disjoint" " from " kermlQualName,+)? (" unions " kermlQualName,+)? (" intersects " kermlQualName,+)?
  (" differences " kermlQualName,+)? kermlPredBody : kernelDecl
syntax (kermlAbstractFlag)? "interaction " ident (" specializes " kermlQualName,+)? (" conjugates " kermlQualName)?
  (" disjoint" " from " kermlQualName,+)? (" unions " kermlQualName,+)? (" intersects " kermlQualName,+)?
  (" differences " kermlQualName,+)? kermlBody : kernelDecl
syntax "package " ident " ;" : kernelDecl
/-- KerML §8.2.5.11 `MultiplicityRange`, standalone: `multiplicity Name [N..M] ;`
(`Base.kerml`'s `exactlyOne`/`zeroOrOne`/`oneToMany`/`zeroToMany`). Bounds are parsed
(`kermlMult`, `Core.lean`) but not stored, same reason as `feature`'s own inline
bracket there -- `MultiplicityRange` has zero stored fields. -/
syntax "multiplicity " ident kermlMult kermlBody : kernelDecl

/-- One `name="value";` redefinition inside an `@Assert{...}`/`@Invariant{...}`
`MetadataBody` (KerML §8.2.5.12's `MetadataBodyFeature`, simplified to just a
name/string-value pair -- real KerML allows a full nested feature redefinition here,
this only covers the attribute-assignment shape every real `@Assert{...}` in this
repo actually uses). -/
declare_syntax_cat kermlMetaAttr
syntax ident " = " str " ;" : kermlMetaAttr

/-- KerML §8.2.5.12 `MetadataFeature`, scoped to the one real shape this repo uses
throughout (per `CLAUDE.md`): `@Assert{n="..."; f="<<...>>"; t="...";}`. Produces a
`MetadataFeature` element (structural, like every other `kermlDecl`) *and* --
genuinely wiring this up, not just parsing it -- re-parses the `f="..."` string's
*contents* against `Assert.lean`'s own `dslAssert` grammar and runs its real
`elabDslAssert` elaborator on the result, splicing the produced term into a `let`
binding that forces Lean to actually type-check the embedded Domain Logic formula as
part of elaborating this `kermlDecl`. A malformed or type-incorrect `f="..."` string
is now a genuine compile error here, the same way it already is when written directly
as `domain% <<...>>` in `Assert.lean` itself. Other metaclasses (`@Invariant`, ...)
and multi-valued `f=`/`t=` (KerML allows `f[1..*]`/`t[0..*]`) aren't covered --
matching every real formula in this repo, which uses exactly one `f=` value. -/
syntax "@" "Assert" "{" kermlMetaAttr* "}" : kernelDecl

/-! ### `kermlExpr` -- the expression language (KerML §8.2.5.8)

An operator-precedence expression grammar, in `Assert.lean`'s `dslTerm`
precedence-climbing style (`syntax:N`). Each `kermlExpr` elaborates to `Array
Element` (not a finished `List Element` term -- callers concatenate freely; only the
top-level `kexpr%` trigger wraps the final result), consistent with `kermlDecl`'s own
"flat list of implied elements, not a nested graph" principle: `1 + 2` becomes *three*
`Element`s (an `OperatorExpression` stub with `operator := "+"`, plus the two
`LiteralInteger` argument stubs) with no attempt to model the owning
`ArgumentMember`/`Argument`/`ArgumentValue` chain the real grammar uses to relate
them -- that chain is exactly the containment-graph machinery this whole project
drops (see file header).

**Covered** (KerML §8.2.5.8, Table 5/6): Boolean/Integer/Real/String/Infinity
literals, `null`, bare identifiers (`FeatureReferenceExpression`), function
invocation `f(a, b)`, `new T(a, b)` construction, feature chaining `.`, indexing
`#(...)`, unary `-`/`not`, and binary `^`/`**` `*` `/` `%` `+` `-` `<` `>` `<=` `>=`
`==` `!=` `and` `xor` `or` `implies` -- precedence/associativity ordering taken
directly from the spec's Table 6 (right-associative `^`/`**`, all others
left-associative), with `&`/`|` collapsed into `and`/`or` (documented simplification,
not a distinct KerML operator).

A bare identifier (`x`, `self`, ...) always elaborates to a `FeatureReferenceExpression`
stub, which is the semantically correct treatment, not just a fallback: per the repo's
`CLAUDE.md`, such names "may include names or identifiers visible in the scope where
they occur" -- a reference to some already-declared feature (an `in`/`out` feature of
whatever this expression is attached to, e.g.), never a fresh declaration of one. The
stub carries only the referenced name because this project has no symbol table to
actually resolve it against (same limitation as `kernelDecl`'s own reference targets
above), not because the reference is meant to be new.

**Not covered** (documented, not guessed at): `..` range construction, `??` null
coalescing, the classification/cast operators (`istype`/`hastype`/`@`/`@@`/`as`/
`meta`), the ternary conditional (`if ... ? ... else ...`), `[...]` bracket
invocation, `->` function-operation syntax, `.?` select / `.` collect (both share
concrete-syntax tokens with feature chaining and invocation respectively, requiring
lookahead this grammar doesn't attempt), sequence construction (`,`), and named
arguments (`name = value` inside a call) -- each would need either more grammar
machinery than is worth it here or (for select/collect) genuine disambiguation
lookahead; real formulas needing them aren't guessed at, matching this project's
established precedent (`Assert.lean`'s own `numberof`/`productof`/`sumof` scope note).

**Known limitation, not a bug**: Lean's own `ident` token already parses dotted
sequences (`x.y.z`) as a single compound identifier (the same mechanism that lets
`Nat.succ` be one token), so it wins over this file's `kermlExpr:90 "." ident`
feature-chaining rule for any chain of bare names -- `x.y.z` elaborates as one
`FeatureReferenceExpression` stub named `"x.y.z"`, never reaching the
`FeatureChainExpression` production at all. The chaining rule *does* fire whenever
the left side isn't itself a bare compound identifier, e.g. `(x).y` or `foo(a).b` --
verified via smoke test below. -/

def mkLiteralBooleanStub (name : String) (v : Bool) : LiteralBoolean := { elementId := name, value := v }
def mkLiteralIntegerStub (name : String) (v : Int) : LiteralInteger := { elementId := name, value := v }
def mkLiteralRationalStub (name : String) (v : Float) : LiteralRational := { elementId := name, value := v }
def mkLiteralStringStub (name : String) (v : String) : LiteralString := { elementId := name, value := v }
def mkLiteralInfinityStub (name : String) : LiteralInfinity := { elementId := name }
def mkNullExpressionStub (name : String) : NullExpression := { elementId := name }
def mkFeatureReferenceStub (name : String) : FeatureReferenceExpression := { elementId := name }
def mkInvocationStub (name : String) : InvocationExpression := { elementId := name }
def mkConstructorStub (name : String) : ConstructorExpression := { elementId := name }
def mkFeatureChainStub (name : String) : FeatureChainExpression := { elementId := name, operator := "." }
def mkOperatorStub (name op : String) : OperatorExpression := { elementId := name, operator := op }
def mkIndexStub (name : String) : IndexExpression := { elementId := name, operator := "#" }

def Expression.elt (e : Expression) : Element := e.toFeature.toKType.toNamespace.toElement
def LiteralExpression.elt (e : LiteralExpression) : Element := e.toExpression.elt
def LiteralBoolean.elt (e : LiteralBoolean) : Element := e.toLiteralExpression.elt
def LiteralInteger.elt (e : LiteralInteger) : Element := e.toLiteralExpression.elt
def LiteralRational.elt (e : LiteralRational) : Element := e.toLiteralExpression.elt
def LiteralString.elt (e : LiteralString) : Element := e.toLiteralExpression.elt
def LiteralInfinity.elt (e : LiteralInfinity) : Element := e.toLiteralExpression.elt
def NullExpression.elt (e : NullExpression) : Element := e.toExpression.elt
def FeatureReferenceExpression.elt (e : FeatureReferenceExpression) : Element := e.toExpression.elt
def InstantiationExpression.elt (e : InstantiationExpression) : Element := e.toExpression.elt
def InvocationExpression.elt (e : InvocationExpression) : Element := e.toInstantiationExpression.elt
def ConstructorExpression.elt (e : ConstructorExpression) : Element := e.toInstantiationExpression.elt
def OperatorExpression.elt (e : OperatorExpression) : Element := e.toInvocationExpression.elt
def FeatureChainExpression.elt (e : FeatureChainExpression) : Element := e.toOperatorExpression.elt
def IndexExpression.elt (e : IndexExpression) : Element := e.toOperatorExpression.elt

declare_syntax_cat kermlExpr

syntax "true" : kermlExpr
syntax "false" : kermlExpr
syntax num : kermlExpr
syntax scientific : kermlExpr
syntax str : kermlExpr
syntax "*" : kermlExpr
syntax "null" : kermlExpr
syntax kermlQualName : kermlExpr

syntax (priority := high) ident "(" kermlExpr,* ")" : kermlExpr
syntax "new " ident "(" kermlExpr,* ")" : kermlExpr

syntax:90 kermlExpr:90 "." ident : kermlExpr
syntax:90 kermlExpr:90 "#" "(" kermlExpr,* ")" : kermlExpr

syntax:80 "-" kermlExpr:80 : kermlExpr
syntax:80 "not " kermlExpr:80 : kermlExpr

syntax:76 kermlExpr:77 " ^ " kermlExpr:76 : kermlExpr
syntax:76 kermlExpr:77 " ** " kermlExpr:76 : kermlExpr
syntax:70 kermlExpr:70 " * " kermlExpr:71 : kermlExpr
syntax:70 kermlExpr:70 " / " kermlExpr:71 : kermlExpr
syntax:70 kermlExpr:70 " % " kermlExpr:71 : kermlExpr
syntax:65 kermlExpr:65 " + " kermlExpr:66 : kermlExpr
syntax:65 kermlExpr:65 " - " kermlExpr:66 : kermlExpr
syntax:60 kermlExpr:60 " < " kermlExpr:61 : kermlExpr
syntax:60 kermlExpr:60 " > " kermlExpr:61 : kermlExpr
syntax:60 kermlExpr:60 " <= " kermlExpr:61 : kermlExpr
syntax:60 kermlExpr:60 " >= " kermlExpr:61 : kermlExpr
syntax:55 kermlExpr:55 " == " kermlExpr:56 : kermlExpr
syntax:55 kermlExpr:55 " != " kermlExpr:56 : kermlExpr
syntax:50 kermlExpr:50 " and " kermlExpr:51 : kermlExpr
syntax:45 kermlExpr:45 " xor " kermlExpr:46 : kermlExpr
syntax:40 kermlExpr:40 " or " kermlExpr:41 : kermlExpr
syntax:35 kermlExpr:35 " implies " kermlExpr:36 : kermlExpr

syntax "(" kermlExpr ")" : kermlExpr

mutual

partial def elabKermlExpr : TSyntax `kermlExpr → MacroM (Array (TSyntax `term))
  | `(kermlExpr| true) => do pure #[← `((mkLiteralBooleanStub "lit-true" Bool.true).elt)]
  | `(kermlExpr| false) => do pure #[← `((mkLiteralBooleanStub "lit-false" Bool.false).elt)]
  | `(kermlExpr| $n:num) => do pure #[← `((mkLiteralIntegerStub "lit-int" $n).elt)]
  | `(kermlExpr| $n:scientific) => do pure #[← `((mkLiteralRationalStub "lit-real" $n).elt)]
  | `(kermlExpr| $s:str) => do pure #[← `((mkLiteralStringStub "lit-str" $s).elt)]
  | `(kermlExpr| *) => do pure #[← `((mkLiteralInfinityStub "infinity").elt)]
  | `(kermlExpr| null) => do pure #[← `((mkNullExpressionStub "null-expr").elt)]
  | `(kermlExpr| $x:kermlQualName) => do
    pure #[← `((mkFeatureReferenceStub $(quote (qualNameStr x))).elt)]
  | `(kermlExpr| $f:ident($args,*)) => do
    let argElems ← args.getElems.mapM elabKermlExpr
    pure (#[← `((mkInvocationStub $(quote f.getId.toString)).elt)] ++ argElems.foldl (· ++ ·) #[])
  | `(kermlExpr| new $t:ident($args,*)) => do
    let argElems ← args.getElems.mapM elabKermlExpr
    pure (#[← `((mkConstructorStub $(quote ("new-" ++ t.getId.toString))).elt)] ++
      argElems.foldl (· ++ ·) #[])
  | `(kermlExpr| $e:kermlExpr . $f:ident) => do
    let eElems ← elabKermlExpr e
    pure (#[← `((mkFeatureChainStub $(quote ("chain-" ++ f.getId.toString))).elt)] ++ eElems)
  | `(kermlExpr| $e:kermlExpr # ($args,*)) => do
    let eElems ← elabKermlExpr e
    let argElems ← args.getElems.mapM elabKermlExpr
    pure (#[← `((mkIndexStub "index-expr").elt)] ++ eElems ++ argElems.foldl (· ++ ·) #[])
  | `(kermlExpr| -$e:kermlExpr) => do
    let eElems ← elabKermlExpr e
    pure (#[← `((mkOperatorStub "unary-minus" "-").elt)] ++ eElems)
  | `(kermlExpr| not $e:kermlExpr) => do
    let eElems ← elabKermlExpr e
    pure (#[← `((mkOperatorStub "unary-not" "not").elt)] ++ eElems)
  | `(kermlExpr| $a:kermlExpr ^ $b:kermlExpr) => elabBinOp "^" a b
  | `(kermlExpr| $a:kermlExpr ** $b:kermlExpr) => elabBinOp "**" a b
  | `(kermlExpr| $a:kermlExpr * $b:kermlExpr) => elabBinOp "*" a b
  | `(kermlExpr| $a:kermlExpr / $b:kermlExpr) => elabBinOp "/" a b
  | `(kermlExpr| $a:kermlExpr % $b:kermlExpr) => elabBinOp "%" a b
  | `(kermlExpr| $a:kermlExpr + $b:kermlExpr) => elabBinOp "+" a b
  | `(kermlExpr| $a:kermlExpr - $b:kermlExpr) => elabBinOp "-" a b
  | `(kermlExpr| $a:kermlExpr < $b:kermlExpr) => elabBinOp "<" a b
  | `(kermlExpr| $a:kermlExpr > $b:kermlExpr) => elabBinOp ">" a b
  | `(kermlExpr| $a:kermlExpr <= $b:kermlExpr) => elabBinOp "<=" a b
  | `(kermlExpr| $a:kermlExpr >= $b:kermlExpr) => elabBinOp ">=" a b
  | `(kermlExpr| $a:kermlExpr == $b:kermlExpr) => elabBinOp "==" a b
  | `(kermlExpr| $a:kermlExpr != $b:kermlExpr) => elabBinOp "!=" a b
  | `(kermlExpr| $a:kermlExpr and $b:kermlExpr) => elabBinOp "and" a b
  | `(kermlExpr| $a:kermlExpr xor $b:kermlExpr) => elabBinOp "xor" a b
  | `(kermlExpr| $a:kermlExpr or $b:kermlExpr) => elabBinOp "or" a b
  | `(kermlExpr| $a:kermlExpr implies $b:kermlExpr) => elabBinOp "implies" a b
  | `(kermlExpr| ($e:kermlExpr)) => elabKermlExpr e
  | _ => Macro.throwUnsupported

/-- Shared by every binary-operator match arm above: one `OperatorExpression` stub
tagged with `op`, plus both operands' own elements. -/
partial def elabBinOp (op : String) (a b : TSyntax `kermlExpr) : MacroM (Array (TSyntax `term)) := do
  let aElems ← elabKermlExpr a
  let bElems ← elabKermlExpr b
  pure (#[← `((mkOperatorStub $(quote ("op-" ++ op)) $(quote op)).elt)] ++ aElems ++ bElems)

end

elab "kexpr% " e:kermlExpr : term => do
  let elems ← Elab.liftMacroM (elabKermlExpr e)
  let stx ← Elab.liftMacroM (mkListTerm elems.toList)
  Elab.Term.elabTerm stx none

/-- `predicate`'s own body category (see its `declare_syntax_cat` above): everything
`kermlBody` already covers (`;` / `{ kermlDecl* }`), plus a *new* shape --
declarations followed by a trailing bare `kermlExpr` -- matching how real KerML
predicates give their own value (`Allen.kerml`'s `predicate precedes { ... in x :
Occurrence; in y : Occurrence; x.endShot < y.startShot }`, the last line an
unwrapped expression, not a further declaration). This is `predicate`-specific (not
folded into `kermlBody` itself, usable by all nine classifier-like keywords) because
`kermlBody`/`elabKermlBody` live in `Core.lean`, compiled *before* `kermlExpr`
exists -- extending `kermlBody`'s own category from here would parse fine (Lean's
`syntax` categories are open across files) but `Core.lean`'s already-compiled
`elabKermlBody` could never dispatch on the new shape, silently dropping it. Giving
`predicate` alone a separate, richer category defined entirely in this file (both
grammar and elaborator) sidesteps that instead of fighting it. -/
syntax kermlBody : kermlPredBody
syntax " {" kermlDecl* kermlExpr "}" : kermlPredBody

def elabKermlPredBody : TSyntax `kermlPredBody → MacroM (Array (TSyntax `term))
  | `(kermlPredBody| $b:kermlBody) => elabKermlBody b
  | `(kermlPredBody| { $decls:kermlDecl* $e:kermlExpr }) => do
    let declElems ← decls.mapM elabKermlDecl
    let exprElems ← elabKermlExpr e
    pure (declElems.foldl (· ++ ·) #[] ++ exprElems)
  | _ => pure #[]

/-- `kernelDecl` → `Array (TSyntax term)`, matching `Core.lean`'s own
`elabKermlDecl` convention (adopted there first, for the same "nested `kermlBody`
content composes as a flat array, wrapped into a `List Element` only at the very top"
reason). Nested body content here is always `Core.lean`'s own `kermlDecl` (e.g. a
`feature` nested inside a `datatype`'s body), elaborated via `Core.lean`'s
`elabKermlBody` directly -- no new mutual recursion needed on this side, since
`elabKermlBody`'s own recursion only ever calls back into `Core.lean`'s
`elabKermlDecl`, not this file's `elabKernelDecl`. **Placed here, after
`elabKermlPredBody`/`elabKermlExpr`, not with `kernelDecl`'s own `syntax`
declarations above**: `predicate`'s own arm calls `elabKermlPredBody`, which in turn
needs `elabKermlExpr` -- ordinary (non-`mutual`) `def`s in Lean 4 can't forward-
reference a function defined later in the file, so this whole function had to move
down here once that dependency existed, even though the *syntax* declarations it
pattern-matches against are still declared earlier (grammar categories don't have
this ordering constraint, only the elaborator `def` does). -/
def kermlMetaAttrPair : TSyntax `kermlMetaAttr → (String × String)
  | `(kermlMetaAttr| $k:ident = $v:str ;) => (k.getId.toString, v.getString)
  | _ => ("", "")

def elabKernelDecl : TSyntax `kernelDecl → MacroM (Array (TSyntax `term))
  | `(kernelDecl| $[$_abs:kermlAbstractFlag]? datatype $a:ident $[specializes $specs,*]? $[conjugates $conj:kermlQualName]?
        $[disjoint from $disj,*]? $[unions $uni,*]? $[intersects $inter,*]? $[differences $diff,*]? $body:kermlBody) => do
    let declElems ← classifierLikeDeclElems dataTypeStubTerm a specs conj disj uni inter diff
    pure (declElems ++ (← elabKermlBody body))
  | `(kernelDecl| $[$_abs:kermlAbstractFlag]? class $a:ident $[specializes $specs,*]? $[conjugates $conj:kermlQualName]?
        $[disjoint from $disj,*]? $[unions $uni,*]? $[intersects $inter,*]? $[differences $diff,*]? $body:kermlBody) => do
    let declElems ← classifierLikeDeclElems kClassStubTerm a specs conj disj uni inter diff
    pure (declElems ++ (← elabKermlBody body))
  | `(kernelDecl| $[$_abs:kermlAbstractFlag]? struct $a:ident $[specializes $specs,*]? $[conjugates $conj:kermlQualName]?
        $[disjoint from $disj,*]? $[unions $uni,*]? $[intersects $inter,*]? $[differences $diff,*]? $body:kermlBody) => do
    let declElems ← classifierLikeDeclElems kStructureStubTerm a specs conj disj uni inter diff
    pure (declElems ++ (← elabKermlBody body))
  | `(kernelDecl| $[$_abs:kermlAbstractFlag]? assoc $a:ident $[specializes $specs,*]? $[conjugates $conj:kermlQualName]?
        $[disjoint from $disj,*]? $[unions $uni,*]? $[intersects $inter,*]? $[differences $diff,*]? $body:kermlBody) => do
    let declElems ← classifierLikeDeclElems associationStubTerm a specs conj disj uni inter diff
    pure (declElems ++ (← elabKermlBody body))
  | `(kernelDecl| $[$_abs:kermlAbstractFlag]? behavior $a:ident $[specializes $specs,*]? $[conjugates $conj:kermlQualName]?
        $[disjoint from $disj,*]? $[unions $uni,*]? $[intersects $inter,*]? $[differences $diff,*]? $body:kermlBody) => do
    let declElems ← classifierLikeDeclElems behaviorStubTerm a specs conj disj uni inter diff
    pure (declElems ++ (← elabKermlBody body))
  | `(kernelDecl| $[$_abs:kermlAbstractFlag]? function $a:ident $[specializes $specs,*]? $[conjugates $conj:kermlQualName]?
        $[disjoint from $disj,*]? $[unions $uni,*]? $[intersects $inter,*]? $[differences $diff,*]? $body:kermlBody) => do
    let declElems ← classifierLikeDeclElems kFunctionStubTerm a specs conj disj uni inter diff
    pure (declElems ++ (← elabKermlBody body))
  | `(kernelDecl| $[$_abs:kermlAbstractFlag]? predicate $a:ident $[specializes $specs,*]? $[conjugates $conj:kermlQualName]?
        $[disjoint from $disj,*]? $[unions $uni,*]? $[intersects $inter,*]? $[differences $diff,*]? $body:kermlPredBody) => do
    let declElems ← classifierLikeDeclElems predicateStubTerm a specs conj disj uni inter diff
    pure (declElems ++ (← elabKermlPredBody body))
  | `(kernelDecl| $[$_abs:kermlAbstractFlag]? interaction $a:ident $[specializes $specs,*]? $[conjugates $conj:kermlQualName]?
        $[disjoint from $disj,*]? $[unions $uni,*]? $[intersects $inter,*]? $[differences $diff,*]? $body:kermlBody) => do
    let declElems ← classifierLikeDeclElems interactionStubTerm a specs conj disj uni inter diff
    pure (declElems ++ (← elabKermlBody body))
  | `(kernelDecl| package $a:ident ;) => do
    let pT ← packageStubTerm a.getId.toString
    pure #[← `(($pT).elt)]
  | `(kernelDecl| multiplicity $a:ident $_mult:kermlMult $body:kermlBody) => do
    let mT ← multiplicityRangeStubTerm a.getId.toString
    pure (#[← `(($mT).elt)] ++ (← elabKermlBody body))
  | `(kernelDecl| @ Assert { $attrs:kermlMetaAttr* }) => do
    let pairs := attrs.map kermlMetaAttrPair
    let nameVal := (pairs.find? (·.1 == "n")).map (·.2)
    let elemId := nameVal.getD "assert"
    pure #[← `((mkMetadataFeatureStub $(quote elemId)).elt)]
  | _ => Macro.throwUnsupported

/-- `@Assert{...}`'s `f="..."` string genuinely re-parsed against `Assert.lean`'s own
`dslAssert` grammar and elaborated via its real `elabDslAssert`, forcing Lean to
type-check the embedded Domain Logic formula -- done here, in the *top-level*
`elab ... : term` trigger (`TermElabM`), not inside `elabKernelDecl` (`MacroM`):
`MacroM` has no `MonadEnv` instance (confirmed by `lake build`, not assumed), so
`Lean.Parser.runParserCategory` -- which needs a real `Environment` to know what
`dslAssert` even means -- simply isn't callable from there. The elaborated term's
*value* is discarded (`let _ := ...`); only the type-checking side effect matters,
same as writing `domain% <<...>>` directly in `Assert.lean` would. -/
elab "kernel% " d:kernelDecl : term => do
  match d with
  | `(kernelDecl| @ Assert { $attrs:kermlMetaAttr* }) => do
    let fVal := (attrs.map kermlMetaAttrPair).find? (·.1 == "f") |>.map (·.2)
    if let some fStr := fVal then
      let env ← getEnv
      match Lean.Parser.runParserCategory env `dslAssert fStr with
      | .error e => throwError s!"malformed @Assert f=\"...\" formula: {e}"
      | .ok stx =>
        let dslStx : TSyntax `dslAssert := ⟨stx⟩
        let assertStx ← Elab.liftMacroM (SFS.Assert.elabDslAssert dslStx)
        -- `elabDslAssert`'s output assumes `Assert.lean`'s own ambient `open SFS`
        -- (bare `death`/`birth`/...); `open SFS in ...` scopes that opening to just
        -- this one elaboration, not this whole file, avoiding the `Membership`
        -- collision risk a blanket `open SFS` alongside this file's own
        -- `open KerML.Root` would carry (the same hazard `SFS.lean` itself opens
        -- `KerML.Root` selectively to avoid, from the opposite direction).
        let wrappedStx ← `(open SFS in $assertStx)
        let _ ← Elab.Term.elabTerm wrappedStx none
  | _ => pure ()
  let elems ← Elab.liftMacroM (elabKernelDecl d)
  let stx ← Elab.liftMacroM (mkListTerm elems.toList)
  Elab.Term.elabTerm stx none

-- Smoke tests: real elaborations, type-checked by Lean.
#check kernel% datatype Real ;
#check kernel% class Vehicle specializes Car, Truck ;
#check kernel% struct Point3D specializes Point ;
#check kernel% assoc Owns specializes Association ;
#check kernel% behavior Drive specializes Behavior ;
#check kernel% function Sum specializes Function ;
#check kernel% predicate IsPositive specializes Predicate ;
#check kernel% interaction Handshake specializes Interaction ;
#check kernel% package VehicleModel ;

-- Base.kerml's own real declarations, as close to the real file's literal text as
-- this grammar gets (see Core.lean's own matching block for the same caveats --
-- `doc /* ... */`'s literal block-comment text and the `nonunique` flag are the
-- only remaining departures from the real file, both explicitly out of scope).
#check kernel% abstract datatype DataValue specializes Anything {
  doc "Value is the most general classifier of entities that are values that do not change over time."
  feature self : DataValue redefines Anything::self ;
}
#check kernel% multiplicity exactlyOne [1..1] {
  doc "exactlyOne is a multiplicity range requiring a cardinality of exactly one."
}
#check kernel% multiplicity zeroOrOne [0..1] {
  doc "zeroOrOne is a multiplicity range requiring a cardinality of zero or one."
}
#check kernel% multiplicity oneToMany [1..*] {
  doc "oneToMany is a multiplicity range allowing any cardinality of one or more."
}
#check kernel% multiplicity zeroToMany [0..*] {
  doc "zeroToMany is a multiplicity range allowing any cardinality of zero or more (that is, no restriction)."
}

-- Allen.kerml's own real `precedes` predicate: `in`/`out` parameter declarations
-- (no `feature` keyword) and a trailing bare-expression body giving the predicate
-- its own value -- both new (`kermlPredBody`) for this file. The surrounding
-- `library package`/`import` wrapper is out of scope for this pass.
#check kernel% predicate precedes {
  in x : Occurrence ;
  in y : Occurrence ;
  x.endShot < y.startShot
}

-- Allen.kerml's own real `@Assert{...}` on `precedes` -- the formula string is
-- genuinely re-parsed and elaborated via Assert.lean's own dslAssert grammar/
-- elabDslAssert (see the kernel% trigger's own doc comment), so this only
-- type-checks because SFS.lean's real `death`/`birth : Occurrence → Time` exist and
-- Time's DSLLt instance applies -- an actually malformed or type-incorrect formula
-- string here would be a genuine compile error, not silently accepted.
#check kernel% @Assert{n="precedes"; f="<<precedes : x~Occurrence, y~Occurrence : death(x) < birth(y) >>";}

#check kexpr% 1 + 2 * 3
#check kexpr% true and not false
#check kexpr% x.y.z
#check kexpr% (x).y
#check kexpr% foo(1, 2, x)
#check kexpr% new Widget(1, 2)
#check kexpr% -x + y
#check kexpr% a < b and b < c or d
#check kexpr% count#(1, 2)
#check kexpr% 3.14
#check kexpr% "hello"
#check kexpr% *
#check kexpr% null
#check kexpr% Anything::self

/-! ## Smoke tests

Real values, not just declarations -- construction and field projection through the
multi-`extends` (diamond) cases above is what actually exercises Lean's inheritance
merging, not just the `structure ... extends A, B` declarations type-checking. -/

private def _testAssoc : Association :=
  { elementId := "a" }
#check (_testAssoc.elementId, _testAssoc.isImplied, _testAssoc.isAbstract)

private def _testAssocStruct : AssociationStructure :=
  { elementId := "as" }
-- Reaches `elementId` (via `Element`, shared through both `Association` and
-- `KStructure`'s paths) and `isAbstract` (via `KType`, only reachable through the
-- `KStructure` path) on the *same* value -- exactly what a non-degenerate diamond
-- merge has to get right.
#check (_testAssocStruct.elementId, _testAssocStruct.isAbstract, _testAssocStruct.isImplied)

private def _testConnector : Connector :=
  { elementId := "conn" }
#check (_testConnector.elementId, _testConnector.isImplied, _testConnector.isAbstract)

private def _testFlow : Flow :=
  { elementId := "f" }
#check (_testFlow.elementId, _testFlow.isImplied, _testFlow.isDerived)

private def _testSuccFlow : SuccessionFlow :=
  { elementId := "sf" }
-- `Connector` is reachable through *two* paths here (`Succession → Connector` and
-- `Flow → Connector`) -- the deepest diamond in this file.
#check (_testSuccFlow.elementId, _testSuccFlow.isImplied, _testSuccFlow.isDerived)

private def _testInteraction : Interaction :=
  { elementId := "i" }
#check (_testInteraction.elementId, _testInteraction.isAbstract)

private def _testMetaFeature : MetadataFeature :=
  { elementId := "mf" }
#check (_testMetaFeature.elementId, _testMetaFeature.isVariable)

end KerML.Kernel