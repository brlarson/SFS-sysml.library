/-
Lean 4 formalization of the KerML (Kernel Modeling Language, OMG SysML v2 Release,
"Kernel Modeling Language v1.0 Beta 3") **Kernel** package's metamodel: KerML §8.3.4
"Kernel Abstract Syntax" (§8.2.5 "Kernel Concrete Syntax" is cited for context only,
not implemented -- see the note at the end of this header). Builds on `Core.lean`
(itself building on `Root.lean`) the same way KerML's own Kernel package imports Core,
which imports Root (Figure 1, "KerML Syntax Layers") -- this completes the three-layer
KerML metamodel.

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

**KerML §8.2.5 Kernel Concrete Syntax**: unlike `Core.lean`, this file does *not* add
`syntax`/`elab` productions for Kernel's (much larger) textual notation. That was a
separate, explicit follow-up request for Core; if wanted for Kernel too, it's a
natural next step, following the same `declare_syntax_cat`/`syntax`/`elab` house style
established in `DSL.lean` and `Core.lean`'s own concrete-syntax section.
-/

import Root
import Core

namespace KerML.Kernel

open KerML.Root
open KerML.Core

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
structure Connector extends Relationship, Feature where
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

/-- KerML §8.3.4.7 `Expression`. A `Step` typed by a `KFunction`; always has a single
result parameter (redefining its function's result), enabling tree-structured
interconnection of `Expression`s. Constraint (not encoded): must specialize
`Performances::evaluations`; must have exactly one result parameter. -/
structure Expression extends Step where
  deriving Repr

/-- KerML §8.3.4.7 `BooleanExpression`. A Boolean-valued `Expression` whose type is a
`Predicate`; represents the logical condition resulting from evaluating that
`Predicate`. Constraint (not encoded): must specialize
`Performances::booleanEvaluations`. -/
structure BooleanExpression extends Expression where
  deriving Repr

/-- KerML §8.3.4.7 `Function` (renamed `KFunction`, see file header). A `Behavior`
with an `out` parameter identified as its result; represents performance of a
calculation producing the result's value(s), possibly decomposed into `Expression`s
as steps. Constraint (not encoded): must specialize `Performances::Evaluation`; must
have exactly one `ReturnParameterMembership`. -/
structure KFunction extends Behavior where
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

/-- KerML §8.3.4.8 `LiteralRational`. A `LiteralExpression` whose Real-valued
`value` (`Float`, see file header) is the result. -/
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
structure Interaction extends Behavior, Association where
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
structure MetadataFeature extends Feature, AnnotatingElement where
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
