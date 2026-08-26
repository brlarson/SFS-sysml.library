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
  isNegated : Bool := Bool.false
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
  isDefault : Bool := Bool.false
  isInitial : Bool := Bool.false
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
  isStandard : Bool := Bool.false
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
def mkLibraryPackageStub (name : String) (isStd : Bool) : LibraryPackage :=
  { elementId := name, declaredName := some name, isStandard := isStd }
def LibraryPackage.elt (t : LibraryPackage) : Element := t.toPackage.toNamespace.toElement
def libraryPackageStubTerm (s : String) (isStd : Bool) : MacroM (TSyntax `term) :=
  `(mkLibraryPackageStub $(quote s) $(quote isStd))
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

/-- `Invariant` (KerML §8.3.4.7) and `FeatureValue` (§8.3.4.10) stubs -- both types
already existed in this file (from the original structural-only pass) but were never
wired to any concrete syntax until `Domain.kerml`'s own `inv {...}` blocks and
`feature ... = ...` default values needed them. Fixed, generic `elementId`s (`"invariant"`/
`"value"`), matching `mkDocumentationStub`'s own precedent of not trying to derive a
unique name from content that has none in the real grammar either. -/
def mkInvariantStub (name : String := "invariant") : Invariant := { elementId := name }
def Invariant.elt (i : Invariant) : Element := i.toBooleanExpression.toExpression.elt
def mkFeatureValueStub : FeatureValue :=
  { elementId := "value", memberElement := { elementId := "value" }, isDefault := Bool.true }
def FeatureValue.elt (v : FeatureValue) : Element := v.toOwningMembership.toMembership.toRelationship.toElement

/-- A `Feature`'s direction prefix, spelled with an explicit `feature` keyword right
after it (`Domain.kerml`'s own real `in feature d : Occurrence[1] {...}` /
`out feature v : Anything[0..1];` -- distinct from `Core.lean`'s bare `in x : T ;`
short form, which never uses the `feature` keyword; both are legitimate per the real
grammar, just different concrete choices different files happen to make). `return`
(KerML's `ReturnParameterMember`) is deliberately **not** one of these three -- it
never takes an explicit `feature` keyword in real text either (`Domain.kerml`'s own
`return result : Anything[0..1] = Get(d, now);`), so it gets its own dedicated
`kermlKDecl` production below instead of forcing an artificial shared shape. -/
declare_syntax_cat kermlDirFlag
syntax "in " : kermlDirFlag
syntax "out " : kermlDirFlag
syntax "inout " : kermlDirFlag

/-- A declared name that might be the literal word `result` -- an ordinary
identifier in real KerML (not a keyword there), but unusable as a bare `ident` in
*this* grammar once `Assert.lean` is imported (for `@Assert` wiring, see that entry
above): `Assert.lean` registers `"result"` as its own leading keyword (`dslTerm`'s
result-binding form), which reserves the word file-wide the same way `"true"`/
`"false"`/`"Assert"` did earlier -- not a KerML restriction, just this tool's. Used
at the return-parameter name position below (`Domain.kerml`'s own real `return
result : ...;`), the one place in this repo's real files the collision actually
surfaces. -/
declare_syntax_cat kermlIdent
syntax ident : kermlIdent
syntax "result" : kermlIdent

def kermlIdentStr : TSyntax `kermlIdent → String
  | `(kermlIdent| $i:ident) => i.getId.toString
  | `(kermlIdent| result) => "result"
  | _ => ""

def dirFlagTerm : TSyntax `kermlDirFlag → MacroM (TSyntax `term)
  | `(kermlDirFlag| in) => `(FeatureDirectionKind.inDir)
  | `(kermlDirFlag| out) => `(FeatureDirectionKind.outDir)
  | `(kermlDirFlag| inout) => `(FeatureDirectionKind.inoutDir)
  | _ => Macro.throwUnsupported

/-- Like `mkDirFeatureStub` (`Core.lean`), but `declaredName := none` -- for the
anonymous `in feature :>> d {...}` form (`kermlKDecl` below), which really has no
name in real KerML either. `elemId` is still synthesized (this project's `Element`
values always need one to be constructible/distinguishable, per `mkFeatureValueStub`'s
own precedent above), just not surfaced as `declaredName`. -/
def mkAnonDirFeatureStub (elemId : String) (dir : FeatureDirectionKind) : Feature :=
  { elementId := elemId, declaredName := none, direction := some dir }

declare_syntax_cat kernelDecl
/-- Declared here (category name only, matching `Assert.lean`'s own "declare every
category up front" lesson for forward references) so `predicate`'s own `syntax`
declaration below can end in it; its actual productions -- which need `kermlExpr`,
declared much later in this file -- are added alongside `elabKermlPredBody` after
that section. See that declaration's own doc comment for why `predicate` alone (not
the other eight classifier-like keywords) needs a body category richer than
`kermlBody`. **Since generalized to `behavior`/`function` too** (`Domain.kerml`'s
`function Get`/`GetNow`, `behavior SetNow`/`GetChange`, ... all need the same
`kermlExpr`-dependent parameter/return/default-value shapes `predicate` already
established the pattern for) -- kept the original name rather than renaming, since
every doc comment and smoke test referencing "predicate's own body category" already
existed before this widened its actual usage; treat "predicate" in older comments as
"predicate/function/behavior" from here on. -/
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
/-- `behavior` alone (of the nine classifier-like keywords) also accepts the symbolic
`:>` alternate spelling of `specializes` (`Domain.kerml`'s own real `behavior
GetBooleanChange :> GetChange {...}` / `behavior GetChangeToTrue :>
GetBooleanChange{...}`) -- `:>` is KerML's general "specialize-or-subset" symbol,
disambiguated by whether the owner is a `Classifier` (specializes) or `Feature`
(subsets); here the owner is always a `Classifier` (`behavior`), so it always means
`specializes`, feeding the same `Subclassification` elaboration as the keyword form.
Not added to the other eight classifier-like keywords -- no real file in this repo
uses `:>` on them, keeping the diff scoped to what's actually needed. -/
syntax (kermlAbstractFlag)? "behavior " ident (" specializes " kermlQualName,+)? (" :> " kermlQualName,+)?
  (" conjugates " kermlQualName)?
  (" disjoint" " from " kermlQualName,+)? (" unions " kermlQualName,+)? (" intersects " kermlQualName,+)?
  (" differences " kermlQualName,+)? kermlPredBody : kernelDecl
syntax (kermlAbstractFlag)? "function " ident (" specializes " kermlQualName,+)? (" conjugates " kermlQualName)?
  (" disjoint" " from " kermlQualName,+)? (" unions " kermlQualName,+)? (" intersects " kermlQualName,+)?
  (" differences " kermlQualName,+)? kermlPredBody : kernelDecl
syntax (kermlAbstractFlag)? "predicate " ident (" specializes " kermlQualName,+)? (" conjugates " kermlQualName)?
  (" disjoint" " from " kermlQualName,+)? (" unions " kermlQualName,+)? (" intersects " kermlQualName,+)?
  (" differences " kermlQualName,+)? kermlPredBody : kernelDecl
syntax (kermlAbstractFlag)? "interaction " ident (" specializes " kermlQualName,+)? (" conjugates " kermlQualName)?
  (" disjoint" " from " kermlQualName,+)? (" unions " kermlQualName,+)? (" intersects " kermlQualName,+)?
  (" differences " kermlQualName,+)? kermlBody : kernelDecl
/-- KerML §8.2.5.13 `Package`/`LibraryPackage`: `package Name { ... }` (`Base.kerml`'s
own package could have been written this way, though the real file's top level isn't
itself parsed here -- see the `library`/`standard library` forms just below, which
*are* matched against real files) or `[standard] library package Name { ... }`
(`Allen.kerml`'s `library package Allen { ... }`, `Base.kerml`'s `standard library
package Base { ... }`/`KerML.kerml`'s `standard library package KerML { ... }`). Real
KerML also allows `PrefixMetadataMember`s before the keyword -- not covered, matching
this grammar's usual scope discipline. -/
syntax "package " ident kermlBody : kernelDecl
syntax "library " "package " ident kermlBody : kernelDecl
syntax "standard " "library " "package " ident kermlBody : kernelDecl
/-- KerML §8.2.5.11 `MultiplicityRange`, standalone: `multiplicity Name [N..M] ;`
(`Base.kerml`'s `exactlyOne`/`zeroOrOne`/`oneToMany`/`zeroToMany`). Bounds are parsed
(`kermlMult`, `Core.lean`) but not stored, same reason as `feature`'s own inline
bracket there -- `MultiplicityRange` has zero stored fields. -/
syntax "multiplicity " ident kermlMult kermlBody : kernelDecl

/-- A `MetadataBodyFeature` attribute *value* (KerML §8.2.5.12): a bare string, a
`+`-concatenated chain of strings (`Domain.kerml`'s own real multi-line `f="..."+
"...";` formulas, split across lines for readability -- real KerML attribute values
are general `Expression`s, and string concatenation via `+` is a legitimate one, not
a new construct), or a parenthesized tuple of strings (`Domain.kerml`'s own real
`t=("Get","now");`, KerML's `t[0..*]` multiplicity spelled out literally). Only the
resulting *string content* is kept (`kermlMetaAttrValStr` below) -- `f=`'s value is
what actually gets re-parsed/elaborated (see the `kernel%` trigger's own doc
comment); `n=`/`t=` are bookkeeping only, so a tuple's exact structure (vs. a single
joined string) is never inspected downstream. -/
declare_syntax_cat kermlMetaAttrVal
syntax str (" + " str)* : kermlMetaAttrVal
syntax "(" str,+ ")" : kermlMetaAttrVal

def kermlMetaAttrValStr : TSyntax `kermlMetaAttrVal → String
  | `(kermlMetaAttrVal| $s:str $[+ $more:str]*) =>
      ((#[s] ++ more).map (·.getString)).foldl (· ++ ·) ""
  | `(kermlMetaAttrVal| ($ss,*)) =>
      String.intercalate "," (ss.getElems.map (·.getString)).toList
  | _ => ""

/-- One `name=value;` redefinition inside an `@Assert{...}`/`@Invariant{...}`
`MetadataBody` (KerML §8.2.5.12's `MetadataBodyFeature`, simplified to just a
name/string-value pair -- real KerML allows a full nested feature redefinition here,
this only covers the attribute-assignment shape every real `@Assert{...}` in this
repo actually uses). -/
declare_syntax_cat kermlMetaAttr
syntax ident " = " kermlMetaAttrVal " ;" : kermlMetaAttr

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
matching every real formula in this repo, which uses exactly one `f=` value.
The metaclass name is captured as a generic `ident`, not the literal keyword
`"Assert"` -- registering `"Assert"` itself as a reserved token would make that
word unusable as an ordinary `ident` anywhere else in this file's grammar,
which real files need (e.g. `import Assertion::Assert ;`, whose qualified name
ends in the bare identifier `Assert`). Both elaborator sites below instead
check the captured ident's string value at elaboration time. -/
syntax "@" ident "{" kermlMetaAttr* "}" : kernelDecl

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
/-- `result`, KerML's automatically-bound result feature (`Expression::result`),
referenced as a bare value -- `Regions.kerml`'s own real `(result as Region)...`
(`Location`/`RegionSurface`/`RegionInterior`/`RegionFilm`'s own `inv{...}` bodies). A
separate production from the bare-`kermlQualName` one below, same reason
`kermlIdent`/`Assert.lean`'s own `"result"` production exist: `Assert.lean` (imported
for `@Assert` wiring) reserves `"result"` as its own `dslTerm` keyword, unusable as a
plain `ident` (hence `kermlQualName`'s own `ident` component) anywhere in this file's
grammar once that import exists. -/
syntax "result" : kermlExpr
syntax kermlQualName : kermlExpr

syntax (priority := high) ident "(" kermlExpr,* ")" : kermlExpr
syntax "new " ident "(" kermlExpr,* ")" : kermlExpr

syntax:90 kermlExpr:90 "." ident : kermlExpr
syntax:90 kermlExpr:90 "#" "(" kermlExpr,* ")" : kermlExpr
/-- A unit-bracket suffix on a value, `Domain.kerml`'s own `feature start : Instant =
0.0 [s] {...}` (a `QuantityValue`-style unit-annotated literal, per the Kernel
Semantic/Quantities libraries, out of scope here). Not real `Quantity` semantics --
just captures both pieces of text as flat sibling elements (the value's own elements,
plus a `FeatureReferenceExpression` stub for the bracketed unit name), the same
"structure without semantics" trade this whole grammar already makes throughout. -/
syntax:90 kermlExpr:90 "[" kermlQualName "]" : kermlExpr
/-- KerML's `as` classification-cast operator (§7.4.6's `AsExpression`), `Regions.kerml`'s
own real `(result as Region).frameOfReference` (`Location`/`RegionSurface`/
`RegionInterior`/`RegionFilm`'s own `inv{...}` bodies). No `AsExpression` abstract-syntax
structure exists in this project (never extracted from the spec, structural-only scope) --
the cast target is parsed but discarded, and the operand's own elements pass through
unchanged, matching every other "structure without semantics" simplification this grammar
already makes (`kermlMult`, unit brackets, ...). -/
syntax:90 kermlExpr:90 " as " kermlQualName : kermlExpr

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
  | `(kermlExpr| result) => do pure #[← `((mkFeatureReferenceStub "result").elt)]
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
  | `(kermlExpr| $e:kermlExpr [$u:kermlQualName]) => do
    let eElems ← elabKermlExpr e
    pure (eElems ++ #[← `((mkFeatureReferenceStub $(quote (qualNameStr u))).elt)])
  | `(kermlExpr| $e:kermlExpr as $_ty:kermlQualName) => elabKermlExpr e
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

/-- `predicate`/`function`/`behavior`'s own body-item category: either a plain
`Core.lean` `kermlDecl` (passthrough, elaborated via `Core.lean`'s own
`elabKermlDecl`), or one of two new shapes `kermlDecl` itself can't express because
they need `kermlExpr` (compiled after `Core.lean`, see `kermlPredBody`'s own doc
comment for the same underlying file-ordering reason):
1. A direction-prefixed *explicit* `feature` keyword form, `Domain.kerml`'s own real
   `in feature d : Occurrence[1] {...}` / `out feature v : Anything[0..1];` --
   distinct from `Core.lean`'s bare `in x : T ;` short form (no `feature` keyword),
   which stays as-is; both are legitimate concrete spellings of the same abstract
   `Feature` with a `direction`. Optionally carries a trailing `= kermlExpr` default
   value too (not exercised by any real `in`/`out feature` in this repo yet, but
   symmetric with the `return`/plain-`feature` forms below, so not artificially
   dropped).
2. `return`'s own dedicated form (no `feature` keyword at all, per the real grammar --
   see `kermlDirFlag`'s own doc comment) and plain `feature`'s own form *with* a
   mandatory `= kermlExpr` default (mandatory so it never overlaps with the
   `kermlDecl`-passthrough `feature` production, which has no default-value clause at
   all): `Domain.kerml`'s own `return result : Anything[0..1] = Get(d, now);` and
   `feature start : Instant = 0.0 [s] {...}`. -/
declare_syntax_cat kermlKDecl
syntax kermlDecl : kermlKDecl
syntax kermlDirFlag "feature " kermlIdent (" : " kermlQualName,+)? (kermlMult)? (" :>> " kermlQualName)?
  (" = " kermlExpr)? kermlBody : kermlKDecl
syntax "return " kermlIdent " : " kermlQualName (kermlMult)? (" = " kermlExpr)? kermlBody : kermlKDecl
syntax "feature " kermlIdent " : " kermlQualName (kermlMult)? " = " kermlExpr kermlBody : kermlKDecl
/-- An **anonymous** direction-prefixed `Feature` -- no declared name at all, just a
`:>>` (`redefines`) target and its own nested body, `Domain.kerml`'s own real
`in feature :>> d { feature e : BooleanEvaluation[1] :>> f; }` (`GetBooleanChange`
redefining `GetChange`'s inherited `d` parameter to add a nested `e` feature, without
renaming `d`). Legitimate per the real grammar: `FeatureDeclaration`'s own
`Identification` is optional, and a `BasicFeaturePrefix` (`in`) plus a
`FeatureSpecializationPart` (`:>> d`) already disambiguate that a `Feature` is being
declared even with no name. `elementId`/`declaredName` are synthesized from the
redefined target's name (`declaredName` stays `none`, matching the real anonymity) --
see its own elaborator arm for why. -/
syntax kermlDirFlag "feature " " :>> " kermlQualName kermlBody : kermlKDecl

/-- `inv {...}` (KerML §8.3.4.7 `Invariant`, see its own standalone `kernelDecl`
production's doc comment for the general shape) is *also* a `kermlKDecl` item, unlike
`classifier`/`type` (`Core.lean`-owned, whose bodies can never reach it) --
`predicate`/`function`/`behavior` already use this richer, `Kernel.lean`-owned body
category, so `inv{}` genuinely nests here, no sibling-`#check` workaround needed.
`Regions.kerml`'s own real `predicate PointInRegion { ... inv { point.frameOfReference
== region.frameOfReference } }` is the first real use of this. -/
syntax "inv " "{" kermlExpr "}" : kermlKDecl

/-- Shared by the plain `feature ... = ...` production of `kermlKDecl` below (usable
nested inside a `predicate`/`function`/`behavior` body) and the identically-shaped
`kernelDecl` production declared further down (usable standalone/top-level, e.g.
`Domain.kerml`'s own package-level `feature start : Instant = 0.0 [s] {...}`) -- the
same declaration text is valid in both positions in real KerML, and this project's
grammar otherwise has no single category reachable from *both* `kernel%`'s top-level
trigger and a nested `kermlPredBody`, so the two productions/elaborator dispatches
stay separate, sharing just this one function. -/
def elabFeatureDefaultElems (an : String) (ty : TSyntax `kermlQualName)
    (val : TSyntax `kermlExpr) (body : TSyntax `kermlBody) : MacroM (Array (TSyntax `term)) := do
  let aT ← `(mkFeatureStub $(quote an))
  let tT ← kTypeStubTermQ ty
  let rel ← mkFeatureTypingTerm aT tT an (qualNameStr ty)
  let valElems ← elabKermlExpr val
  let bodyElems ← elabKermlBody body
  pure (#[← `(($aT).elt), ← `(($rel).elt), ← `((mkFeatureValueStub).elt)] ++ valElems ++ bodyElems)

def elabKermlKDecl : TSyntax `kermlKDecl → MacroM (Array (TSyntax `term))
  | `(kermlKDecl| $d:kermlDecl) => elabKermlDecl d
  | `(kermlKDecl| $dir:kermlDirFlag feature $a:kermlIdent $[: $tys,*]? $[$_mult:kermlMult]?
        $[:>> $redefT:kermlQualName]? $[= $val:kermlExpr]? $body:kermlBody) => do
    let an := kermlIdentStr a
    let dT ← dirFlagTerm dir
    let aT ← `(mkDirFeatureStub $(quote an) $dT)
    let tyElems ← (tys.map (·.getElems) |>.getD #[]).mapM (fun g => do
        let gT ← kTypeStubTermQ g
        let rel ← mkFeatureTypingTerm aT gT an (qualNameStr g)
        `(($rel).elt))
    let redefElems ← match redefT with
      | some g => do
          let gT ← featureStubTermQ g
          let rel ← mkRedefinitionTerm aT gT an (qualNameStr g)
          pure #[← `(($rel).elt)]
      | none => pure #[]
    let valElems ← match val with
      | some v => do pure (#[← `((mkFeatureValueStub).elt)] ++ (← elabKermlExpr v))
      | none => pure #[]
    let bodyElems ← elabKermlBody body
    pure (#[← `(($aT).elt)] ++ tyElems ++ redefElems ++ valElems ++ bodyElems)
  | `(kermlKDecl| $dir:kermlDirFlag feature :>> $redefT:kermlQualName $body:kermlBody) => do
    let dT ← dirFlagTerm dir
    let redefN := qualNameStr redefT
    let elemId := "anon-redefines-" ++ redefN
    let aT ← `(mkAnonDirFeatureStub $(quote elemId) $dT)
    let gT ← featureStubTermQ redefT
    let rel ← mkRedefinitionTerm aT gT elemId redefN
    let bodyElems ← elabKermlBody body
    pure (#[← `(($aT).elt), ← `(($rel).elt)] ++ bodyElems)
  | `(kermlKDecl| return $a:kermlIdent : $ty:kermlQualName $[$_mult:kermlMult]?
        $[= $val:kermlExpr]? $body:kermlBody) => do
    let an := kermlIdentStr a
    let aT ← `(mkDirFeatureStub $(quote an) FeatureDirectionKind.outDir)
    let tT ← kTypeStubTermQ ty
    let rel ← mkFeatureTypingTerm aT tT an (qualNameStr ty)
    let valElems ← match val with
      | some v => do pure (#[← `((mkFeatureValueStub).elt)] ++ (← elabKermlExpr v))
      | none => pure #[]
    let bodyElems ← elabKermlBody body
    pure (#[← `(($aT).elt), ← `(($rel).elt)] ++ valElems ++ bodyElems)
  | `(kermlKDecl| feature $a:kermlIdent : $ty:kermlQualName $[$_mult:kermlMult]? = $val:kermlExpr $body:kermlBody) =>
    elabFeatureDefaultElems (kermlIdentStr a) ty val body
  | `(kermlKDecl| inv { $e:kermlExpr }) => do
    pure (#[← `((mkInvariantStub).elt)] ++ (← elabKermlExpr e))
  | _ => Macro.throwUnsupported

/-- `predicate`/`function`/`behavior`'s own body category (see its
`declare_syntax_cat` above): everything `kermlBody` already covers (`;` / `{
kermlDecl* }`, now via `kermlKDecl`'s own passthrough), plus a *new* shape --
declarations followed by a trailing bare `kermlExpr` -- matching how real KerML
predicates give their own value (`Allen.kerml`'s `predicate precedes { ... in x :
Occurrence; in y : Occurrence; x.endShot < y.startShot }`, the last line an
unwrapped expression, not a further declaration). This is `predicate`/`function`/
`behavior`-specific (not folded into `kermlBody` itself, usable by all nine
classifier-like keywords) because `kermlBody`/`elabKermlBody` live in `Core.lean`,
compiled *before* `kermlExpr` exists -- extending `kermlBody`'s own category from
here would parse fine (Lean's `syntax` categories are open across files) but
`Core.lean`'s already-compiled `elabKermlBody` could never dispatch on the new shape,
silently dropping it. Giving these three keywords a separate, richer category defined
entirely in this file (both grammar and elaborator) sidesteps that instead of
fighting it. -/
syntax " ;" : kermlPredBody
syntax " {" kermlKDecl* "}" : kermlPredBody
syntax " {" kermlKDecl* kermlExpr "}" : kermlPredBody

def elabKermlPredBody : TSyntax `kermlPredBody → MacroM (Array (TSyntax `term))
  | `(kermlPredBody| ;) => pure #[]
  | `(kermlPredBody| { $decls:kermlKDecl* }) => do
    let declElems ← decls.mapM elabKermlKDecl
    pure (declElems.foldl (· ++ ·) #[])
  | `(kermlPredBody| { $decls:kermlKDecl* $e:kermlExpr }) => do
    let declElems ← decls.mapM elabKermlKDecl
    let exprElems ← elabKermlExpr e
    pure (declElems.foldl (· ++ ·) #[] ++ exprElems)
  | _ => pure #[]

/-- KerML §8.3.4.7 `Invariant`, standalone body form: `inv { <expr> }`
(`Domain.kerml`'s own real `inv {lowerBound <= upperBound}`, inside `classifier
Interval {...}`'s body). **Not** nestable inside `classifier`'s own body in this
grammar -- `classifier` is `Core.lean`'s own keyword, whose body is `Core.lean`'s
`kermlBody` (`kermlDecl*`, compiled before `kermlExpr`/`Invariant` exist), the exact
same category-layering constraint documented at length for `library package`
vs. `predicate`/`@Assert` in `Allen.kerml`'s own entry -- kept as a separate, sibling
`kernelDecl`/`#check` instead, not nested inside `Interval`'s own smoke test. Real
negated invariants (`inv not {...}`) aren't covered -- not present in any real file
this project's smoke tests target. -/
syntax "inv " "{" kermlExpr "}" : kernelDecl

/-- Standalone/top-level counterpart to `kermlKDecl`'s own `feature ... = ...`
production (see `elabFeatureDefaultElems`'s own doc comment for why these are two
separate productions sharing one elaborator): `Domain.kerml`'s own package-level
`feature start : Instant = 0.0 [s] {...}` sits directly inside `library package
Domain {...}`'s body, not nested inside a `predicate`/`function`/`behavior` -- but
(same constraint as `inv`/`@Assert` above) can't actually nest inside the wrapper's
own `#check` either, since `library package`'s body is `Core.lean`'s `kermlBody`,
compiled before `kermlExpr` exists; kept as its own sibling `#check`. -/
syntax "feature " kermlIdent " : " kermlQualName (kermlMult)? " = " kermlExpr kermlBody : kernelDecl

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
  | `(kermlMetaAttr| $k:ident = $v:kermlMetaAttrVal ;) => (k.getId.toString, kermlMetaAttrValStr v)
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
  | `(kernelDecl| $[$_abs:kermlAbstractFlag]? behavior $a:ident $[specializes $specs,*]? $[:> $specs2,*]?
        $[conjugates $conj:kermlQualName]?
        $[disjoint from $disj,*]? $[unions $uni,*]? $[intersects $inter,*]? $[differences $diff,*]? $body:kermlPredBody) => do
    let declElems ← classifierLikeDeclElems behaviorStubTerm a specs conj disj uni inter diff
    let an := a.getId.toString
    let symSpecElems ← match specs2 with
      | some ss => ss.getElems.mapM (fun g => do
          let aT ← behaviorStubTerm an
          let aC ← `(($aT).toClassifierC)
          let gC ← classifierStubTermQ g
          let rel ← mkSubclassificationTerm aC gC an (qualNameStr g)
          `(($rel).elt))
      | none => pure #[]
    pure (declElems ++ symSpecElems ++ (← elabKermlPredBody body))
  | `(kernelDecl| $[$_abs:kermlAbstractFlag]? function $a:ident $[specializes $specs,*]? $[conjugates $conj:kermlQualName]?
        $[disjoint from $disj,*]? $[unions $uni,*]? $[intersects $inter,*]? $[differences $diff,*]? $body:kermlPredBody) => do
    let declElems ← classifierLikeDeclElems kFunctionStubTerm a specs conj disj uni inter diff
    pure (declElems ++ (← elabKermlPredBody body))
  | `(kernelDecl| $[$_abs:kermlAbstractFlag]? predicate $a:ident $[specializes $specs,*]? $[conjugates $conj:kermlQualName]?
        $[disjoint from $disj,*]? $[unions $uni,*]? $[intersects $inter,*]? $[differences $diff,*]? $body:kermlPredBody) => do
    let declElems ← classifierLikeDeclElems predicateStubTerm a specs conj disj uni inter diff
    pure (declElems ++ (← elabKermlPredBody body))
  | `(kernelDecl| $[$_abs:kermlAbstractFlag]? interaction $a:ident $[specializes $specs,*]? $[conjugates $conj:kermlQualName]?
        $[disjoint from $disj,*]? $[unions $uni,*]? $[intersects $inter,*]? $[differences $diff,*]? $body:kermlBody) => do
    let declElems ← classifierLikeDeclElems interactionStubTerm a specs conj disj uni inter diff
    pure (declElems ++ (← elabKermlBody body))
  | `(kernelDecl| package $a:ident $body:kermlBody) => do
    let pT ← packageStubTerm a.getId.toString
    pure (#[← `(($pT).elt)] ++ (← elabKermlBody body))
  | `(kernelDecl| library package $a:ident $body:kermlBody) => do
    let pT ← libraryPackageStubTerm a.getId.toString Bool.false
    pure (#[← `(($pT).elt)] ++ (← elabKermlBody body))
  | `(kernelDecl| standard library package $a:ident $body:kermlBody) => do
    let pT ← libraryPackageStubTerm a.getId.toString Bool.true
    pure (#[← `(($pT).elt)] ++ (← elabKermlBody body))
  | `(kernelDecl| multiplicity $a:ident $_mult:kermlMult $body:kermlBody) => do
    let mT ← multiplicityRangeStubTerm a.getId.toString
    pure (#[← `(($mT).elt)] ++ (← elabKermlBody body))
  | `(kernelDecl| inv { $e:kermlExpr }) => do
    pure (#[← `((mkInvariantStub).elt)] ++ (← elabKermlExpr e))
  | `(kernelDecl| feature $a:kermlIdent : $ty:kermlQualName $[$_mult:kermlMult]? = $val:kermlExpr $body:kermlBody) =>
    elabFeatureDefaultElems (kermlIdentStr a) ty val body
  | `(kernelDecl| @ $mc:ident { $attrs:kermlMetaAttr* }) => do
    let pairs := attrs.map kermlMetaAttrPair
    let nameVal := (pairs.find? (·.1 == "n")).map (·.2)
    let elemId := nameVal.getD mc.getId.toString
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
  | `(kernelDecl| @ $mc:ident { $attrs:kermlMetaAttr* }) => do
    let fVal := if mc.getId.toString == "Assert" then
        (attrs.map kermlMetaAttrPair).find? (·.1 == "f") |>.map (·.2)
      else none
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

-- Allen.kerml's own real `library package Allen { ... }` wrapper, containing its
-- own real `import` statements (`private` isn't parsed, see `import`'s own note in
-- Core.lean; dropped here, same as every other unparsed prefix flag throughout this
-- grammar) and its own real `doc`. `predicate`/`@Assert` are *not* nested inside
-- here, even though the real file nests them -- `kermlBody`'s `kermlDecl*` (used by
-- `library package`'s own body, like every other body in this grammar) only ever
-- holds `Core.lean`-layer content (`Core.lean` is compiled before `Kernel.lean`
-- exists, so its `elabKermlBody` has no way to dispatch on Kernel-layer shapes like
-- `predicate`/`@Assert` -- the same category-layering constraint `kermlPredBody`
-- itself was built to route around, but only for `kermlExpr`, not for other
-- `kernelDecl` keywords nested inside each other). Kept as separate, sibling
-- `#check`s below instead, each demonstrating its own piece faithfully.
#check kernel% library package Allen {
  import Assertion::Assert ;
  import Occurrences::Occurrence ;
  import Domain::next ;
  doc "SFS: Allen's Intervals -- death defined by df-bl.death; birth defined by df-bl.birth"
}

-- Allen.kerml's own real `precedes` predicate: `in`/`out` parameter declarations
-- (no `feature` keyword) and a trailing bare-expression body giving the predicate
-- its own value -- both new (`kermlPredBody`) for this file.
#check kernel% predicate precedes {
  in x : Occurrence ;
  in y : Occurrence ;
  x.endShot < y.startShot
}

-- The remaining eight `Allen.kerml` predicate bodies, verbatim (2026-08-26):
-- `==`/`!=`/`<=`/`>=`/`or`/`not`, dot-access chained with a comparison, and (for
-- `nearlyMeets`) a bare `ident "(" kermlExpr,* ")"` invocation of `next` are all
-- already covered by the operator table above -- no new grammar needed, this is
-- pure coverage confirming every real predicate body in the file actually parses.
#check kernel% predicate meets {
  in x : Occurrence ;
  in y : Occurrence ;
  x.endShot == y.startShot and not x.openRight and not y.openLeft
}

#check kernel% predicate overlaps {
  in x : Occurrence ;
  in y : Occurrence ;
  y.startShot < x.endShot
}

#check kernel% predicate starts {
  in x : Occurrence ;
  in y : Occurrence ;
  (x.startShot == y.startShot) and (y.endShot < x.endShot)
    and x.openLeft == y.openLeft
}

#check kernel% predicate during {
  in x : Occurrence ;
  in y : Occurrence ;
  (y.startShot <= x.startShot) and (x.endShot <= y.endShot)
}

#check kernel% predicate finishes {
  in x : Occurrence ;
  in y : Occurrence ;
  y.startShot < x.startShot and x.endShot == y.endShot
    and x.openRight==y.openRight
}

#check kernel% predicate coincident {
  in x : Occurrence ;
  in y : Occurrence ;
  y.startShot == x.startShot and x.endShot == y.endShot
    and x.openLeft == y.openLeft and x.openRight==y.openRight
}

#check kernel% predicate nonoverlaps {
  in x : Occurrence ;
  in y : Occurrence ;
  (y.startShot > x.endShot) or (x.startShot > y.endShot)
}

-- `nearlyMeets`'s body: its structural KerML body -- `next(x.endShot,
-- y.startShot)` as a plain invocation, not through the Domain-logic DSL at all --
-- parses and elaborates fine, and (2026-08-26) so does its `@Assert` formula
-- below, via the new `DSLNext` class.
#check kernel% predicate nearlyMeets {
  in x : Occurrence ;
  in y : Occurrence ;
  ( x.endShot==y.startShot and ( x.openRight or y.openLeft) ) or next(x.endShot, y.startShot)
}

-- Allen.kerml's own real `@Assert{...}` formulas, verbatim, now live again
-- (2026-08-25, "extend Domain logic for compare only when defined" -- see
-- Assert.lean's own new `DSLLt`/`DSLLe`/`DSLEq`/`DSLAnd`/`DSLOr` outParam
-- instances, and SFS.lean's `kand`/`kor`/`klt`/`kle`/`keq` Strong Kleene
-- combinators). Briefly, after `death` became `Occurrence → Option Time`
-- (2026-08-25, fixing the `birth`/`deathIff` inconsistency), `death(x) < birth(y)`
-- stopped elaborating: comparing `Option Time` to `Time` had no instance. Rather
-- than treating that as an unfixable gap, the DSL itself was taught genuine
-- partiality -- comparisons/`and`/`or` over an `Option`-wrapped operand now
-- propagate undefinedness (Strong Kleene, "compare only when defined"), short-
-- circuiting to a definite answer where one is already forced (e.g. a known-false
-- conjunct makes the whole `and` false even if the other side is unknown). The
-- formula text below is *unchanged* from Allen.kerml -- only the semantics/types
-- assigned to it changed; see Assert.lean's own `example ... := rfl` checks for
-- confirmation each elaborates to exactly `SFS.lean`'s real predicate.
#check kernel% @Assert{n="precedes"; f="<<precedes : x~Occurrence, y~Occurrence : death(x) < birth(y) >>"; t="precedes";}

#check kernel% @Assert{n="meets"; f="<<meets : x~Occurrence, y~Occurrence : death(x) = birth(y) >>"; t="meets";}

#check kernel% @Assert{n="overlaps"; f="<<overlaps : x~Occurrence, y~Occurrence : birth(y) <  death(x)>>"; t="overlaps";}

#check kernel% @Assert{n="during"; f="<<during : x~Occurrence, y~Occurrence : birth(y) <= birth(x) and death(x) <= death(y)>>"; t="during";}

#check kernel% @Assert{n="nonoverlaps"; f="<<nonoverlaps : x~Occurrence, y~Occurrence : birth(y) > death(x) or birth(x) > death(y)>>"; t="nonoverlaps";}

-- `starts`/`finishes`/`coincident`, now that `x.openLeft`/`y.openRight` dot-access
-- has real grammar support (`Assert.lean`'s `elabDslTerm`/`freeIdentsInTerm`, the
-- `$x:ident` case: an unspaced `x.openLeft` is one compound identifier by the time
-- Lean's *lexer* sees it, so the fix splits it there rather than adding a doomed
-- separate `dslTerm "." ident` grammar production, which could never actually fire
-- for real, unspaced formula text) and `SFS.lean`'s own definitions (2026-08-26)
-- gained the `openLeft`/`openRight` conjunct they had been missing. See
-- `Assert.lean`'s own `example ... := rfl` checks (bare `domain%`, not the full
-- `@Assert{...}` wrapper this file's own `kernel%` elaborates) for confirmation
-- each elaborates to exactly `SFS.lean`'s real, current predicate.
#check kernel% @Assert{n="starts"; f="<<starts : x~Occurrence, y~Occurrence :"+
  " birth(x) = birth(y) and death(y) < death(x)"+
  " and x.openLeft = y.openLeft >>"; t="starts";}

#check kernel% @Assert{n="finishes"; f="<<finishes : x~Occurrence, y~Occurrence :"+
  " birth(y) < birth(x) and death(x) = death(y)"+
  " and x.openRight = y.openRight >>"; t="finishes";}

#check kernel% @Assert{n="coincident"; f="<<coincident : x~Occurrence, y~Occurrence :"+
  " birth(y) = birth(x) and death(x) = death(y)"+
  " and x.openLeft = y.openLeft and x.openRight = y.openRight >>"; t="coincident";}

-- `nearlyMeets`'s own `@Assert` formula, the last of the nine (2026-08-26, at
-- direct request: "let next be false if either of its parameters is undefined"):
-- `next(death(x), birth(y))` now routes through `DSLNext`'s `(Option Time) Time
-- Prop` instance, landing on `SFS.nextO`'s deliberately non-Kleene semantics --
-- see `SFS.lean`'s own doc comment on `nextO` for why "false," not "undefined,"
-- is the right reading specifically for this predicate. `SFS.lean`'s `nearlyMeets`
-- was rewritten the same day onto the shared `kand`/`kor`/`nextO` combinators so
-- this agrees exactly with the DSL-elaborated formula (see `Assert.lean`'s own
-- `example ... := rfl`). This closes the last documented gap in this file's
-- Allen.kerml coverage -- all nine predicates now have both a live structural
-- body `#check` and a live `@Assert` formula `#check`.
#check kernel% @Assert{n="nearlyMeets"; f="<<nearlyMeets : x~Occurrence, y~Occurrence :"+
  " (birth(y) = death(x) and (x.openRight or y.openLeft)) or next(death(x), birth(y))>>";}

-- Domain.kerml's own real `library package Domain { ... }` wrapper: nine real
-- `private import ...;` statements (the new `kermlVisibilityFlag`, Core.lean),
-- Kernel-layer content (`classifier`/`predicate`/`function`/`behavior`) kept as
-- separate sibling `#check`s below, same constraint/precedent as Allen.kerml's own
-- wrapper above.
#check kernel% library package Domain {
  private import ScalarValues::Real ;
  private import ScalarValues::Boolean ;
  private import Base::DataValue ;
  private import Assertion::Assert ;
  private import Occurrences::Occurrence ;
  private import SI::s ;
  private import Performances::BooleanEvaluation ;
  private import Base::Anything ;
  private import ISQSpaceTime::TimeValue ;
}

-- Domain.kerml's own real `type Instant specializes TimeValue {...}` -- already
-- fully covered by existing `Core.lean` grammar, no new machinery.
#check kerml% type Instant specializes TimeValue {
  doc "an instant of time"
}

-- Domain.kerml's own real `classifier Interval {...}` -- `inv {...}` kept separate
-- below (see `inv`'s own doc comment for why it can't nest here).
#check kerml% classifier Interval {
  doc "an interval is a duration between two instants"
  feature lowerBound : Instant ;
  feature upperBound : Instant ;
  feature openLeft : Boolean ;
  feature openRight : Boolean ;
}

-- Domain.kerml's own real `inv {lowerBound <= upperBound}`, `Interval`'s own
-- invariant (new `inv` production).
#check kernel% inv { lowerBound <= upperBound }

-- Domain.kerml's own real `feature now : Instant {...}` -- plain top-level feature,
-- no default value, already covered by existing `Core.lean` grammar.
#check kerml% feature now : Instant {
  doc "the current instant of time"
}

-- Domain.kerml's own real `feature start : Instant = 0.0 [s] {...}` -- the new
-- mandatory-default `feature` form (`kermlKDecl`) plus the new unit-bracket
-- `kermlExpr` postfix.
#check kernel% feature start : Instant = 0.0 [s] {
  doc "the beginning of system operation, start=0"
}

-- Domain.kerml's own real `predicate next {...}` -- two `in feature` parameters
-- (explicit `feature` keyword, unlike Allen.kerml's bare `in x : T` form), no
-- trailing bare expression (predicate's own declarations-only `kermlPredBody`
-- alternative). `@Assert{...}` kept as a separate sibling `#check` below, same as
-- Allen.kerml's own `precedes`/`@Assert` split above -- the `elab "kernel% "`
-- trigger's own formula-validation special-case only fires when `@Assert{...}` is
-- the *entire* outer `kernelDecl` being checked, not when it's nested inside
-- another declaration's body (nesting still produces the right structural
-- `MetadataFeature` stub via `elabKermlKDecl`'s plain `kernelDecl`-shaped-content
-- passthrough is *not* wired for `@Assert` specifically, so it would in fact fail to
-- parse there at all -- kept out of every nested body below for this reason, not
-- just the weaker formula-validation one).
#check kernel% predicate next {
  doc "tau1 precedes tau2 and there are no instants in between"
  in feature tau1 : Instant ;
  in feature tau2 : Instant ;
}
#check kernel% @Assert{n="next"; f="<<next : tau1~Instant, tau2~Instant : (tau1 < tau2 and "+
  " not exists tau~Instant that (tau1 < tau and tau < tau2) )  >>";
    t="next";}

-- Domain.kerml's own real `function Get {...}` -- a nested `in feature d : ... {
-- feature f : ...; }` (own body, Core.lean-layer `feature` nested inside a
-- Kernel-layer `in feature`), and `return result : ...;` with no default (the new
-- keyword-less `return` form). `result` is an ordinary identifier in real KerML,
-- not a keyword -- it only needs `kermlIdent` (rather than bare `ident`) here
-- because `Assert.lean` (imported for `@Assert` wiring, see that entry above)
-- separately reserves `"result"` as its own leading keyword (`dslTerm`'s
-- result-binding form), the same file-wide keyword-reservation collision already
-- hit twice before (`true`/`false`, `Assert`) -- this tool's limitation, not
-- KerML's.
#check kernel% function Get {
  doc "Get(d,f,tau) returns the value of the feature d::f at time tau."
  in feature d : Occurrence[1] {
    feature f : Anything[1] ;
  }
  in feature tau : Instant[1] ;
  return result : Anything[0..1] ;
}
#check kernel% @Assert{n="Get"; f="<<Get : d~Occurrence, f~Anything, tau~Instant := I[[d::f,tau]] >>";
    t="Get";}

-- Domain.kerml's own real `function GetNow {...}` -- `return`'s own default-value
-- form, `= Get(d, now)` (a real function-call `kermlExpr`).
#check kernel% function GetNow {
  doc "GetNow(d,f) returns the value of the feature d::f at the current time, now."
  in feature d : Occurrence[1] {
    feature f : Anything[1] ;
  }
  return result : Anything[0..1] = Get(d, now) ;
}
#check kernel% @Assert{n="GetNow"; f="<<GetNow : d~Occurrence, f~Anything := I[[d::f,now]] >>";
    t=("Get","now");}

-- Domain.kerml's own real `behavior SetNow {...}` -- two `in feature` parameters,
-- no return.
#check kernel% behavior SetNow {
  doc "SetNow(d,f,v) sets the value of the feature d::f to v at the current time, now."
  in feature d : Occurrence[1] {
    feature f : Anything[1] ;
  }
  in feature v : Anything[1] ;
}
#check kernel% @Assert{n="SetNow"; f="<<SetNow : d~Occurrence, f~Anything : I[[d::f,now]] = v >>";
    t="SetNow";}

-- Domain.kerml's own real `behavior GetChange {...}` -- adds `out feature v : ...;`
-- (the new `out`-direction explicit-`feature`-keyword form).
#check kernel% behavior GetChange {
  doc "GetChange(d,f) waits for value of the feature d::f to change from its value at time tau."
  in feature d : Occurrence[1] {
    feature f : Anything[1] ;
  }
  in feature tau : Instant[1] ;
  out feature v : Anything[0..1] ;
}
#check kernel% @Assert{n="GetChange"; f="<<GetChange : d~Occurrence, f~Anything, tau~Instant : "+
    "(I[[d::f,tau]] <> I[[d::f,now]] and forall t~Instant in tau ., now are I[[d::f,t]] = I[[d::f,tau]])"+
    " implies v = I[[d::f,now]] >>";
    t="GetChange";}

-- Domain.kerml's own real `behavior GetBooleanChange :> GetChange {...}` -- the
-- symbolic `:>` specializes header (new, `behavior`-only) and the anonymous
-- `in feature :>> d {...}` redefining `GetChange`'s own `d` parameter (new,
-- `kermlKDecl`), whose own nested `feature e : BooleanEvaluation[1] :>> f;` uses the
-- symbolic `:>>` redefines clause on Core.lean's plain `feature` (new). `out feature
-- b : Boolean[1] :>> v;` closes the loop with `:>>` on the named direction-prefixed
-- form too (new).
#check kernel% behavior GetBooleanChange :> GetChange {
  doc "GetBooleanChange, like GetChange, waits for d::e to toggle"
  in feature :>> d {
    feature e : BooleanEvaluation[1] :>> f ;
  }
  in feature tau : Instant[1] ;
  out feature b : Boolean[1] :>> v ;
}
#check kernel% @Assert{n="GetBooleanChange"; f="<<GetBooleanChange : d~Occurrence, e~BooleanEvaluation, tau~Instant : "+
    "(I[[d::e,tau]] <> I[[d::e,now]] and forall t~Instant in tau ., now are I[[d::e,t]] = I[[d::e,tau]])"+
    " implies b = I[[d::e,now]] >>";
    t="GetBooleanChange";}

-- Domain.kerml's own real `behavior GetChangeToTrue :> GetBooleanChange{...}` --
-- empty body (`;`-equivalent `{}`), no new machinery beyond the symbolic `:>` header
-- already exercised above.
#check kernel% behavior GetChangeToTrue :> GetBooleanChange {
  doc "GetChangeToTrue does not wait if d::e is already true"
}
#check kernel% @Assert{n="GetChangeToTrue"; f="<<GetChangeToTrue : d~Occurrence, e~BooleanEvaluation, tau~Instant : "+
    "(I[[d::e,now]] and forall t~Instant in tau ., now are not I[[d::e,t]] )"+
    " implies b = true >>";
    t="GetChangeToTrue";}

-- Domain.kerml's own real `behavior GetChangeToFalse :> GetBooleanChange{...}`.
#check kernel% behavior GetChangeToFalse :> GetBooleanChange {
  doc "GetChangeToFalse does not wait if d::e is already false"
}
#check kernel% @Assert{n="GetChangeToFalse"; f="<<GetChangeToFalse : d~Occurrence, e~BooleanEvaluation, tau~Instant : "+
    "(not I[[d::e,now]] and forall t~Instant in tau ., now are I[[d::e,t]] )"+
    " implies b = false >>";
    t="GetChangeToFalse";}

-- Mereology.kerml's own real `library package Mereology { ... }` wrapper: three
-- real `private import ...;` statements, same sibling-`#check` treatment as
-- Allen.kerml/Domain.kerml's own wrappers above.
#check kernel% library package Mereology {
  doc "SFS: Merology is the metaphysics of parthood. Predicates are Performances::BooleanEvaluation in KerML, but metaphysical predicates aren't meant to be executed. Need something to define values rather than operations."
  private import Performances::BooleanEvaluation ;
  private import Occurrences::Occurrence ;
  private import Assertion::Assert ;
}

-- Mereology.kerml's own real `abstract predicate PartOf specializes
-- BooleanEvaluation {...}` -- `abstract`/`specializes` on `predicate`, both
-- already-existing grammar (`kermlAbstractFlag`, `predicate`'s own
-- `specializes`-clause production), exercised together here for the first time.
-- `@Assert`/`doc` kept as separate sibling `#check`s below, same constraint as
-- every other nested-body case in this file.
#check kernel% abstract predicate PartOf specializes BooleanEvaluation {
  in x : Occurrence ;
  in y : Occurrence ;
}

-- `PartOf`'s own `@Assert` body, `xPy`, is the informal "x P y" shorthand
-- (`Assert.lean`'s own documented, deliberate exclusion -- see its "Formulas
-- deliberately *not* included" list): `xPy` is a bare `dslWff` identifier that
-- `freeIdentsInWff` never auto-binds, so this fails honestly with "unknown
-- identifier xPy," not attempted as a live `#check` here either, same reasoning.

-- `PAR`/`PTR`: bare top-level `@Assert{...}` declarations, not nested inside any
-- predicate -- stating a fact about `PartOf` rather than defining a new one, same
-- shape as `Allen.kerml`'s own top-level formulas.
#check kernel% @Assert{n="PAR"; f="<< PAR : : forall x~Occurrence are not PartOf(x,x) >>"; t="par";}
#check kernel% @Assert{n="PTR"; f="<< PTR : : forall x,y,z~Occurrence are "+
  "( (PartOf(x,y) and PartOf(y,z)) implies PartOf(x,z) ) >>"; t="ptr";}

#check kernel% abstract predicate PartOverlap specializes BooleanEvaluation {
  in x : Occurrence ;
  in y : Occurrence ;
}
#check kernel% @Assert{n="PartOverlap"; f="<< PartOverlap : x~Occurrence, y~Occurrence : "+
  "exists z~Occurrence that ( PartOf(z,x) and PartOf(z,y) ) >>"; t="PartOverlap";}

#check kernel% abstract predicate PartUnderlap specializes BooleanEvaluation {
  in x : Occurrence ;
  in y : Occurrence ;
}
#check kernel% @Assert{n="PartUnderlap"; f="<< PartUnderlap : x~Occurrence, y~Occurrence : "+
  "exists z~Occurrence that ( PartOf(x,z) and PartOf(y,z) ) >>"; t="PartUnderlap";}

#check kernel% abstract predicate ImproperPart specializes BooleanEvaluation {
  in x : Occurrence ;
  in y : Occurrence ;
}
#check kernel% @Assert{n="ImproperPart"; f="<< ImproperPart : x~Occurrence, y~Occurrence : PartOf(x,y) or x=y >>"; t="ImproperPart";}

#check kernel% abstract predicate PartDisjoint specializes BooleanEvaluation {
  in x : Occurrence ;
  in y : Occurrence ;
}
#check kernel% @Assert{n="PartDisjoint"; f="<< PartDisjoint : x~Occurrence, y~Occurrence : not PartOverlap(x,y) >>";
    t="PartDisjoint";}

-- `PCH`: another bare top-level `@Assert{...}`, same shape as `PAR`/`PTR` above.
#check kernel% @Assert{n="PCH"; f="<< PCH : : forall x,y~Occurrence are "+
  "( (x=y or PartOf(x,y) or PartOf(y,x) or PartDisjoint(x,y))"+
  "and not (PartOf(x,y) and PartOf(y,x)) ) >>"; t="pch";}

#check kernel% abstract predicate AtomicPart specializes BooleanEvaluation {
  in x : Occurrence ;
}
#check kernel% @Assert{n="AtomicPart";f="<< AtomicPart : x~Occurrence : not exists z~Occurrence that PartOf(z,x) >>";
    t="AtomicPart";}

-- Regions.kerml's own real `library package Regions { ... }` wrapper: six real
-- `private import ...;` statements, all Core.lean-layer content.
#check kernel% library package Regions {
  private import SpatialFrames::SpatialFrame ;
  private import Occurrences::Occurrence ;
  private import Assertion::Assert ;
  private import Performances::BooleanEvaluation ;
  private import Clocks::Clock ;
  private import Clocks::universalClock ;
}

-- Regions.kerml's own real `type FrameOfReference {...}` -- the new `default` clause
-- (parsed, not stored) on a nested `feature`.
#check kerml% type FrameOfReference specializes Base::Anything {
  doc "A frame of reference serves as the reference for the location of an occurrence."
  feature clock : Clock default universalClock ;
}

-- Regions.kerml's own real `feature universalFrameOfReference : FrameOfReference {...}`
-- -- the new undirected anonymous `feature :>> clock = universalClock;`.
#check kerml% feature universalFrameOfReference : FrameOfReference {
  doc "universalFrameOfReference is a fixed frame of reference used as a universal default."
  feature :>> clock = universalClock ;
}

#check kerml% type Region specializes Base::Anything {
  doc "A region is a contiguous, three-dimensional volume at a particular place in a particular frame-of-reference."
  feature frameOfReference : FrameOfReference default universalFrameOfReference ;
}

#check kerml% type Point specializes Base::Anything {
  doc "Point is a metaphysical 0-dimensional entity."
  feature frameOfReference : FrameOfReference default universalFrameOfReference ;
}

#check kerml% type Surface specializes Base::Anything {
  doc "Surface is the set of points at the boundary of a Region."
  feature frameOfReference : FrameOfReference default universalFrameOfReference ;
}

-- Regions.kerml's own real `function Location {...}` -- `inv{...}` now genuinely
-- nested (new, via kermlKDecl) and the new `as` cast expression
-- (`(result as Region).frameOfReference`). Its own `@Assert` formula (`o L result`)
-- is a known, permanent gap, at direct request: `SFS.lean`'s `Location` is now a
-- real function (`Occurrence → Region`, 2026-08-21, matching Regions.kerml's own
-- functional declaration), but the infix `L` notation those real formulas'
-- *definitions* use is deliberately not wired up (no `L` alias added) -- disregarded
-- on purpose, not an oversight. Confirmed via a real build attempt: still fails with
-- "Unknown identifier `L`" specifically, nothing else.
#check kernel% function Location {
  doc "The location function relates spatial occurrences to their region."
  in o : Occurrence ;
  return result : Region ;
  inv { o.isClosed and o.innerSpaceDimension == 3 and o.outerSpaceDimension == 3
    and o.frameOfReference == (result as Region).frameOfReference }
}

#check kernel% predicate PointInRegion {
  doc "Point is contained in Region; \"in\" is a set membership relation"
  in point : Point ;
  in region : Region ;
  inv { point.frameOfReference == region.frameOfReference }
}
#check kernel% @Assert{n="PointInRegion"; f="<< PointInRegion : point~Point, region~Region : "+
    " point in region >>";}

#check kernel% predicate PointOnSurface {
  doc "Point is on a Surface"
  in point : Point ;
  in surface : Surface ;
  inv { point.frameOfReference == surface.frameOfReference }
}
#check kernel% @Assert{n="PointOnSurface"; f="<< PointOnSurface : point~Point, surface~Surface : "+
    " point in surface >>";}

#check kernel% predicate RegionOverlap {
  doc "Two regions containing the same point overlap. This is the \"O\" relation (df-rov)."
  in r1 : Region ;
  in r2 : Region ;
  inv { r1.frameOfReference == r2.frameOfReference }
}
#check kernel% @Assert{n="RegionOverlap"; f="<< RegionOverlap : r1~Region, r2~Region :"+
    "exists p~Point that (PointInRegion(p,r1) and PointInRegion(p,r2)) >>"; t="RegionOverlap";}

#check kernel% predicate RegionContainment {
  doc "A region contains another, when it contains all of its points."
  in r1 : Region ;
  in r2 : Region ;
  inv { r1.frameOfReference == r2.frameOfReference }
}
#check kernel% @Assert{n="RegionContainment"; f="<< RegionContainment : r1~Region, r2~Region :"+
    "forall p~Point are (PointInRegion(p,r2) implies PointInRegion(p,r1)) >>"; t="RegionContainment";}

#check kernel% predicate AtomicRegion {
  doc "A region is atomic when it contains no other regions (in the location relation)."
  in r : Region ;
}
#check kernel% @Assert{n="AtomicRegion"; f="<< AtomicRegion : r~Region : "+
    "forall r1~Region are ( RegionContainment(r,r1) implies r = r1 ) >>"; t="AtomicRegion";}

-- LFU/LIN/EXPNS/APAR's own real formulas each call `Location(x)` as a one-argument
-- function returning a `Region` -- now that `Location` is genuinely a
-- one-argument function itself (`Occurrence → Region`, 2026-08-21), the previously-
-- documented one-arg-call-vs-two-arg-relation mismatch is gone and all four
-- elaborate live, confirmed via a real build attempt (not assumed from the type
-- change alone).
#check kernel% @Assert{n="locational functionality";
    f="<< LFU : : forall x~Occurrence forall r1,r2~Region are"+
      " ( (Location(x)=r1 and Location(x)=r2) implies r1=r2 ) >>"; t="lfu";}

#check kernel% @Assert{n="injectivity of location";
    f="<< LIN : : forall x,y~Occurrence forall r~Region are"+
      " ( (Location(x)=r and Location(y)=r) implies x=y ) >>"; t="lin";}

#check kernel% @Assert{n="EXPNS"; f="<< EXPNS : : forall x,y~Occurrence forall r1,r2~Region are "+
    "( (Location(x)=r1 and Location(y)=r2 and PartOf(x,y)) implies RegionContainment(r2,r1) ) >>"; t="expansivity";}

#check kernel% @Assert{n="APAR"; f="<< APAR : : forall x~Occurrence forall r~Region are "+
    "(Location(x)=r and AtomicPart(x)) implies AtomicRegion(r) >>"; t="apar";}

#check kernel% @Assert{n="NOINTP"; f="<< NOINTP : : forall r1,r2~Region are "+
    "RegionOverlap(r1,r2) implies (RegionContainment(r1,r2) or RegionContainment(r2,r1)) >>"; t="no_interpenetration";}

#check kernel% predicate AtomicRegionDisjoint {
  doc "Atomic regions are disjoint (df-rdi)"
}
#check kernel% @Assert{n="AtomicRegionDisjoint"; f="<< AtomicRegionDisjoint : :"+
    "forall r1,r2~Region are "+
    "   ( (AtomicRegion(r1) and AtomicRegion(r2)) implies "+
    "     (not RegionOverlap(r1,r2) or r1=r2) ) >>"; t="rdi";}

-- Regions.kerml's own real `predicate Adjacent {...}` -- `p1`/`p2` infinitesimally
-- close points, now a real `SFS.lean` primitive (`axiom Adjacent : Point → Point →
-- Prop`, 2026-08-21). Its own `@Assert` formula body (`p1Ap2`) is the same
-- informal, bare-`dslWff`-identifier shorthand `Mereology.kerml`'s own `PartOf`
-- formula uses (`xPy`) for a genuinely primitive relation with no further
-- reduction -- expected to keep failing honestly (`freeIdentsInWff`'s own
-- bare-identifier case deliberately never auto-binds this), not attempted live,
-- same as `PartOf`'s own body above. `Adjacent(p1,p2)` used as a real predicate
-- *application* elsewhere (below) is a different case entirely and does resolve.
#check kernel% predicate Adjacent {
  doc "Adjacent is the infinitesimal-closeness relation p1Ap2 -- p1 and p2 are infinitesimally close points."
  in p1 : Point ;
  in p2 : Point ;
}

-- RegionSurface/RegionInterior/RegionFilm's own structural declarations (including
-- `inv{...}`'s new `as` cast) elaborate fine. `RegionSurface`/`RegionFilm : Region →
-- Surface` and `RegionInterior : Region → Region` are real one-argument functions in
-- `SFS.lean` (2026-08-21, same as `Location`), so their own `RegionSurface(r)`/
-- `RegionFilm(r)` calls don't arity-mismatch; and now that `Adjacent` is a real
-- primitive too, `RegionSurface`'s/`RegionFilm`'s own formulas (which replace
-- `Regions.kerml`'s old `p2 in Adj(p)` set-membership idiom with a direct
-- `Adjacent(p,p2)` predicate application) elaborate live as well -- no longer
-- excluded.
#check kernel% function RegionSurface {
  doc "The surface of a region is all the points on its boundary"
  in r : Region ;
  return result : Surface ;
  inv { r.frameOfReference == (result as Surface).frameOfReference }
}
#check kernel% @Assert{n="RegionSurface"; f="<< RegionSurface : r~Region := result~Surface | "+
    "forall p~Point are (PointOnSurface(p,result) iff (PointInRegion(p,r) and "+
    "  exists p2~Point that ( Adjacent(p,p2) and not PointInRegion(p2,r) ))) >>"; t="RegionSurface";}

#check kernel% function RegionInterior {
  doc "The interior of a region includes all the points in a region not on its surface"
  in r : Region ;
  return result : Region ;
  inv { r.frameOfReference == (result as Region).frameOfReference }
}
#check kernel% @Assert{n="RegionInterior"; f="<< RegionInterior : r~Region := result~Region | "+
    "forall p~Point are (PointInRegion(p,result) iff "+
    "  (PointInRegion(p,r) and not PointOnSurface(p,RegionSurface(r))) ) >>"; t="RegionInterior";}

#check kernel% function RegionFilm {
  doc "The film of a region is a surface of which it's the interior"
  in r : Region ;
  return result : Surface ;
  inv { r.frameOfReference == (result as Surface).frameOfReference }
}
#check kernel% @Assert{n="RegionFilm"; f="<< RegionFilm : r~Region := result~Surface | "+
    " forall p~Point are ( PointOnSurface(p,result) iff "+
    " (not PointInRegion(p,r) and exists p2~Point that "+
    "    (PointOnSurface(p2,RegionSurface(r)) and Adjacent(p,p2)))) >>"; t="RegionFilm";}

-- ExternallyConnected/FilmConnected each call `RegionFilm(r1)` as a one-argument
-- function too -- now that `RegionFilm` really is one, both elaborate live
-- (confirmed via a real build attempt), no longer excluded.
#check kernel% predicate ExternallyConnected {
  doc "This is the externally connected (EC) relation of Region Connection Calculus"
  in r1 : Region ;
  in r2 : Region ;
  inv { r1.frameOfReference == r2.frameOfReference }
}
#check kernel% @Assert{n="ExternallyConnected"; f="<< ExternallyConnected : r1~Region, r2~Region : "+
    " not RegionOverlap(r1,r2) and exists p~Point that ( PointOnSurface(p,RegionFilm(r1)) and PointInRegion(p,r2) ) >>"; t="ExternallyConnected";}

#check kernel% predicate FilmConnected {
  doc "This is needed for Occurrences::JustOutsideOf."
  in r1 : Region ;
  in r2 : Region ;
  inv { r1.frameOfReference == r2.frameOfReference }
}
#check kernel% @Assert{n="FilmConnected"; f="<< FilmConnected : r1~Region, r2~Region :"+
    " exists p~Point that ( PointOnSurface(p,RegionFilm(r1)) and PointOnSurface(p,RegionFilm(r2)) ) >>";}

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