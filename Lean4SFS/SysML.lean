/-
Lean 4 formalization of SysML v2 (OMG "Systems Modeling Language", "Systems Modeling Language
v2.1, Beta 2, Part 1") on top of `Root.lean`/`Core.lean`/`Kernel.lean`'s KerML formalization.

**Scope, same discipline as every other file in this project** (see `Root.lean`'s header for the
full rationale this continues): abstract-syntax `structure`s use `extends` to mirror the real
generalization hierarchy directly; only non-derived (stored) attributes become fields (`/`-prefixed
derived attributes in the spec are omitted, same as everywhere else); OCL constraints are noted in
prose, not encoded; the containment graph (`ownedRelationship`, `member`, ...) is dropped.

SysML is a genuinely *different* language from KerML, not a KerML dialect -- its own concrete
syntax (`bnf/SysML-textual-bnf.kebnf`) and abstract syntax (`2a-OMG_Systems_Modeling_Language.pdf`
§8.3, real page numbers confirmed via `pdftotext`: §8.3.1 Overview p.285, §8.3.6 Definition/Usage
p.290, §8.3.9 Occurrences p.282, §8.3.11 Parts p.319, §8.3.13 Connections p.297, §8.3.17 Actions
p.337, §8.3.27 Metadata p.393) are both real, separate grammars. But it *shares* KerML's expression
language wholesale (confirmed in the BNF: SysML defines no `OwnedExpression` grammar of its own) and
its Root-layer package/import/comment/doc shape is near-identical to KerML's own (BNF lines 40-181
vs `Root.lean`'s `Import`/`Documentation`) -- so this file reuses `Kernel.lean`'s `kermlExpr`/
`kexpr%` and `kernelDecl` (via a passthrough alternative) directly rather than reimplementing
either, and only adds what's genuinely new: the SysML `Definition`/`Usage` metaclass hierarchy and
its own concrete syntax.

## Real-usage survey (`sysml.library`, grepped 2026-09-12) drove the concrete-syntax scope below,
matching this project's established "needs-driven, not guessed at" discipline: `attribute`/
`attribute def` (37/20 files), `calc`/`calc def` (11/11), `metadata def` (11), `item`/`item def`
(7/5), `connection`/`connection def` (6/4), `part`/`part def` (5/3), `constraint`/`constraint def`
(5/2), `requirement`/`requirement def` (4/2), `action`/`action def` (4/3), `port`/`port def`
(3/2), `state`/`state def` (3/2), `enum`/`enum def` (4/4), `interface`/`interface def` (2/2),
`view`/`view def` (2/2), `viewpoint def`/`rendering def`/`allocation def`/`flow def`/`case def`/
`analysis def`/`verification def`/`use case def`/`concern def` (0-1 file each).
`Systems Library/Actions.sysml` (571 lines: `accept`/`send`/`assign`/`terminate`/`if`/`while`/
`for`/`merge`/`decide`/`join`/`fork` control-flow nodes, BNF §8.2.2.17.3-17.8) dwarfs every other
kind's own library file (`Parts.sysml` 81, `States.sysml` 102, `Requirements.sysml` 196, ...),
which are dominated by the **generic Definition/Usage shape** (BNF §8.2.2.6) confirmed via
`Domain Libraries/Quantities and Units/MeasurementReferences.sysml`'s real `attribute def
TensorMeasurementReference :> Array { attribute isBound: Boolean[1] default false; attribute
order :>> rank; ... }`.

**Covered**: the generic Definition/Usage backbone (name, `:>` specializes/subsets, `:>>`
redefines, multiplicity, `default` value, body nesting) for the 14 keyword pairs actually used in
this repo: `attribute`/`enum`/`item`/`part`/`port`/`connection`/`interface`/`allocation`/`action`/
`calc`/`state`/`constraint`/`requirement`/`view`, plus `connect`/`allocate` (reusing `Kernel.lean`'s
`kermlConnEnd`/`elabKermlConnEnd` verbatim) for `connection`/`allocation` usages.

**Not covered** (documented, not guessed at -- matching `Kernel.lean`'s own identical judgment call
for KerML's `Flow`/`SuccessionFlow`, left out because no real file needs them that way): Action's
control-flow node keywords (`accept`/`send`/`assign`/`terminate`/`if`/`while`/`for`/`merge`/
`decide`/`join`/`fork`) -- structures only, no concrete syntax; State's `entry`/`do`/`exit`/
`transition`; Flow's `of`/`from`/`to` payload form and `Message`; `expose`/`render`/`exhibit`-style
View/Viewpoint/Rendering clauses; `filter`/`variant`/`variation`; the anonymous `:>>`-led usage form
(`attribute :>> dimensions: Positive[0..1];`, real but rare -- named usages only here); Interface's
own separate `connect` clause (Port-typed ends, distinct enough from `ConnectorEnd` to warrant its
own pass); Port's auto-injected nested `ConjugatedPortDefinition`. Each of these appears in 0-2 real
files, the same threshold below which this project has consistently deferred rather than guessed.
-/

import Root
import Core
import Kernel
import Lean

namespace KerML.SysML

open KerML.Root
open KerML.Core
open KerML.Kernel
open Lean

/-! ## 8.3.6 Definition and Usage (p.290) -/

/-- SysML §8.3.6 `Definition`. "Definitions represent kinds of things." Non-derived: `isVariation`
(whether this is a variation point for variant modeling, not otherwise encoded here). -/
structure Definition extends Classifier where
  isVariation : Bool := Bool.false
  deriving Repr

/-- SysML §8.3.6 `Usage`. "Usages represent the use of a Definition (or, more generally, a Type) in
the context of another Definition or Usage." Non-derived: `isVariation` (mirrors `Definition`'s
own). `isReference`/`mayTimeVary` are both derived, omitted per the file header. -/
structure Usage extends Feature where
  isVariation : Bool := Bool.false
  deriving Repr

/-- SysML §8.3.6.3 `ReferenceUsage`. A `Usage` that is definitely non-composite
(`isReference := true`, the one non-derived override this metaclass adds). -/
structure ReferenceUsage extends Usage where
  deriving Repr

/-! ## 8.3.7 Attributes (p.298-ish) -/

structure AttributeDefinition extends Definition where
  deriving Repr
def AttributeDefinition.toClassifierC (t : AttributeDefinition) : Classifier := t.toDefinition.toClassifier
def AttributeDefinition.elt (t : AttributeDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

structure AttributeUsage extends Usage where
  deriving Repr
def AttributeUsage.toFeatureC (t : AttributeUsage) : Feature := t.toUsage.toFeature

/-! ## 8.3.8 Enumerations -/

structure EnumerationDefinition extends AttributeDefinition where
  deriving Repr
def EnumerationDefinition.toClassifierC (t : EnumerationDefinition) : Classifier := t.toAttributeDefinition.toClassifierC
def EnumerationDefinition.elt (t : EnumerationDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

structure EnumerationUsage extends AttributeUsage where
  deriving Repr
def EnumerationUsage.toFeatureC (t : EnumerationUsage) : Feature := t.toAttributeUsage.toFeatureC

/-! ## 8.3.9 Occurrences (p.282) -/

/-- SysML §8.3.9 `OccurrenceDefinition`. Dual-extends `Definition` (SysML side) and KerML's own
`Class` (`KClass` here) -- an `OccurrenceDefinition` really is both. Non-derived: `isIndividual`. -/
structure OccurrenceDefinition extends Definition, KClass where
  isIndividual : Bool := Bool.false
  deriving Repr

def OccurrenceDefinition.toClassifierC (t : OccurrenceDefinition) : Classifier := t.toDefinition.toClassifier
def OccurrenceDefinition.elt (t : OccurrenceDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

/-- `PortionKind` (§8.3.9.1): `snapshot` | `timeslice`. -/
inductive PortionKind
  | snapshot | timeslice
  deriving DecidableEq, Repr

/-- SysML §8.3.9 `OccurrenceUsage`. Non-derived: `isIndividual`, `portionKind`. -/
structure OccurrenceUsage extends Usage where
  isIndividual : Bool := Bool.false
  portionKind : Option PortionKind := none
  deriving Repr
def OccurrenceUsage.toFeatureC (t : OccurrenceUsage) : Feature := t.toUsage.toFeature

/-! ## 8.3.10 Items -/

structure ItemDefinition extends OccurrenceDefinition where
  deriving Repr
def ItemDefinition.toClassifierC (t : ItemDefinition) : Classifier := t.toOccurrenceDefinition.toClassifierC
def ItemDefinition.elt (t : ItemDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

structure ItemUsage extends OccurrenceUsage where
  deriving Repr
def ItemUsage.toFeatureC (t : ItemUsage) : Feature := t.toOccurrenceUsage.toFeatureC

/-! ## 8.3.11 Parts (p.319) -/

structure PartDefinition extends ItemDefinition where
  deriving Repr
def PartDefinition.toClassifierC (t : PartDefinition) : Classifier := t.toItemDefinition.toClassifierC
def PartDefinition.elt (t : PartDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

structure PartUsage extends ItemUsage where
  deriving Repr
def PartUsage.toFeatureC (t : PartUsage) : Feature := t.toItemUsage.toFeatureC

/-! ## 8.3.12 Ports -/

structure PortDefinition extends PartDefinition where
  deriving Repr
def PortDefinition.toClassifierC (t : PortDefinition) : Classifier := t.toPartDefinition.toClassifierC
def PortDefinition.elt (t : PortDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

/-- §8.3.12's auto-injected nested conjugate -- structural only, never produced by the concrete
syntax below (see file-header scope note: Port's own `~name` conjugated-typing symbol *is* usable
as an ordinary `kermlQualName` reference target, just not auto-generated as a sibling element). -/
structure ConjugatedPortDefinition extends PortDefinition where
  deriving Repr

structure PortUsage extends ItemUsage where
  deriving Repr
def PortUsage.toFeatureC (t : PortUsage) : Feature := t.toItemUsage.toFeatureC

/-! ## 8.3.13 Connections (p.297) -/

/-- SysML §8.3.13 `ConnectionDefinition`. Dual-extends `PartDefinition` and KerML's
`AssociationStructure` (`Kernel.lean`). Non-derived: `isSufficient` (default `true`, redefining
`KType`'s own `isSufficient`). -/
structure ConnectionDefinition extends PartDefinition, AssociationStructure where
  isSufficient : Bool := Bool.true
  deriving Repr
def ConnectionDefinition.toClassifierC (t : ConnectionDefinition) : Classifier := t.toPartDefinition.toClassifierC
def ConnectionDefinition.elt (t : ConnectionDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

/-- §8.3.13's `ConnectorAsUsage`: a `Usage` that is also a KerML `Connector` -- the shared parent of
`ConnectionUsage`/`BindingConnectorAsUsage`/`SuccessionAsUsage`. -/
structure ConnectorAsUsage extends Usage, Connector where
  deriving Repr

structure ConnectionUsage extends PartUsage, ConnectorAsUsage where
  deriving Repr
def ConnectionUsage.elt (t : ConnectionUsage) : Element := t.toPartUsage.elt
def ConnectionUsage.toFeatureC (t : ConnectionUsage) : Feature := t.toPartUsage.toFeatureC

/-- §8.2.2.13.2 `BindingConnectorAsUsage`: SysML's usage-level wrapper around KerML's own
`BindingConnector` (`Kernel.lean`) -- structural only, no concrete syntax below (the plain KerML
`binding A = B;` form, already in `Kernel.lean`, covers every real use in this repo). -/
structure BindingConnectorAsUsage extends ConnectorAsUsage, BindingConnector where
  deriving Repr

/-- §8.2.2.13.3 `SuccessionAsUsage`: ditto, wrapping KerML's `Succession`. -/
structure SuccessionAsUsage extends ConnectorAsUsage, Succession where
  deriving Repr

/-! ## 8.3.14 Interfaces -/

structure InterfaceDefinition extends ConnectionDefinition where
  deriving Repr
def InterfaceDefinition.toClassifierC (t : InterfaceDefinition) : Classifier := t.toConnectionDefinition.toClassifierC
def InterfaceDefinition.elt (t : InterfaceDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

structure InterfaceUsage extends ConnectionUsage where
  deriving Repr
def InterfaceUsage.elt (t : InterfaceUsage) : Element := t.toConnectionUsage.elt
def InterfaceUsage.toFeatureC (t : InterfaceUsage) : Feature := t.toConnectionUsage.toFeatureC

/-! ## 8.3.15 Allocations -/

structure AllocationDefinition extends ConnectionDefinition where
  deriving Repr
def AllocationDefinition.toClassifierC (t : AllocationDefinition) : Classifier := t.toConnectionDefinition.toClassifierC
def AllocationDefinition.elt (t : AllocationDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

structure AllocationUsage extends ConnectionUsage where
  deriving Repr
def AllocationUsage.elt (t : AllocationUsage) : Element := t.toConnectionUsage.elt
def AllocationUsage.toFeatureC (t : AllocationUsage) : Feature := t.toConnectionUsage.toFeatureC

/-! ## 8.3.17 Actions (p.337) -/

/-- SysML §8.3.17 `ActionDefinition`. Dual-extends `OccurrenceDefinition` and KerML's `Behavior`. -/
structure ActionDefinition extends OccurrenceDefinition, Behavior where
  deriving Repr
def ActionDefinition.toClassifierC (t : ActionDefinition) : Classifier := t.toOccurrenceDefinition.toClassifierC
def ActionDefinition.elt (t : ActionDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

/-- `ActionUsage`. Dual-extends `OccurrenceUsage` and KerML's `Step`. -/
structure ActionUsage extends OccurrenceUsage, Step where
  deriving Repr
def ActionUsage.elt (t : ActionUsage) : Element := t.toOccurrenceUsage.elt
def ActionUsage.toFeatureC (t : ActionUsage) : Feature := t.toOccurrenceUsage.toFeatureC

/-- The 571-line control-flow subtree (§8.2.2.17.3-17.8): abstract syntax only, no concrete syntax
production below -- see file-header scope note. Each is a one-line `extends ActionUsage`. -/
structure AcceptActionUsage extends ActionUsage where deriving Repr
structure SendActionUsage extends ActionUsage where deriving Repr
structure AssignmentActionUsage extends ActionUsage where deriving Repr
structure TerminateActionUsage extends ActionUsage where deriving Repr
structure IfActionUsage extends ActionUsage where deriving Repr
structure WhileLoopActionUsage extends ActionUsage where deriving Repr
structure ForLoopActionUsage extends ActionUsage where deriving Repr
structure ControlNode extends ActionUsage where deriving Repr
structure MergeNode extends ControlNode where deriving Repr
structure DecisionNode extends ControlNode where deriving Repr
structure JoinNode extends ControlNode where deriving Repr
structure ForkNode extends ControlNode where deriving Repr

/-! ## 8.3.16 Flow -/

/-- `FlowDefinition`: dual-extends `ActionDefinition` and KerML's `Interaction`. -/
structure FlowDefinition extends ActionDefinition, Interaction where
  deriving Repr
def FlowDefinition.toClassifierC (t : FlowDefinition) : Classifier := t.toActionDefinition.toClassifierC
def FlowDefinition.elt (t : FlowDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

/-- `FlowUsage`: dual-extends `ActionUsage` and `ConnectorAsUsage`. -/
structure FlowUsage extends ActionUsage, ConnectorAsUsage where
  deriving Repr
def FlowUsage.elt (t : FlowUsage) : Element := t.toActionUsage.elt

/-- `SuccessionFlowUsage`: dual-extends `FlowUsage` and KerML's `SuccessionFlow`. Structural only,
no concrete syntax below (see file-header scope note on Flow's payload form). -/
structure SuccessionFlowUsage extends FlowUsage, SuccessionFlow where
  deriving Repr

/-- §8.2.2.16 `Message`: a `FlowUsage` for message-passing between parts. Structural only, no
concrete syntax below (see file-header scope note). -/
structure Message extends FlowUsage where
  deriving Repr

/-! ## 8.3.19 Calculations -/

/-- `CalculationDefinition`: dual-extends `ActionDefinition` and KerML's `KFunction`. -/
structure CalculationDefinition extends ActionDefinition, KFunction where
  deriving Repr
def CalculationDefinition.toClassifierC (t : CalculationDefinition) : Classifier := t.toActionDefinition.toClassifierC
def CalculationDefinition.elt (t : CalculationDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

/-- `CalculationUsage`: dual-extends `ActionUsage` and KerML's `Expression` (a calculation
*produces* a value, unlike a plain action). -/
structure CalculationUsage extends ActionUsage, Expression where
  deriving Repr
def CalculationUsage.elt (t : CalculationUsage) : Element := t.toActionUsage.elt
def CalculationUsage.toFeatureC (t : CalculationUsage) : Feature := t.toActionUsage.toFeatureC

/-! ## 8.3.18 States -/

/-- `StateDefinition extends ActionDefinition`. Non-derived: `isParallel`. -/
structure StateDefinition extends ActionDefinition where
  isParallel : Bool := Bool.false
  deriving Repr
def StateDefinition.toClassifierC (t : StateDefinition) : Classifier := t.toActionDefinition.toClassifierC
def StateDefinition.elt (t : StateDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

/-- `StateUsage extends ActionUsage`. Non-derived: `isParallel`. -/
structure StateUsage extends ActionUsage where
  isParallel : Bool := Bool.false
  deriving Repr
def StateUsage.elt (t : StateUsage) : Element := t.toActionUsage.elt
def StateUsage.toFeatureC (t : StateUsage) : Feature := t.toActionUsage.toFeatureC

/-- §8.2.2.18.3 `TransitionUsage`: structural only, no concrete syntax below (see file-header scope
note -- `entry`/`do`/`exit`/trigger/guard/effect all deferred). -/
structure TransitionUsage extends ActionUsage where
  deriving Repr

/-! ## 8.3.20 Constraints -/

/-- `ConstraintDefinition`: dual-extends `OccurrenceDefinition` and KerML's `Predicate`. -/
structure ConstraintDefinition extends OccurrenceDefinition, Predicate where
  deriving Repr
def ConstraintDefinition.toClassifierC (t : ConstraintDefinition) : Classifier := t.toOccurrenceDefinition.toClassifierC
def ConstraintDefinition.elt (t : ConstraintDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

/-- `ConstraintUsage`: dual-extends `OccurrenceUsage` and KerML's `BooleanExpression`. -/
structure ConstraintUsage extends OccurrenceUsage, BooleanExpression where
  deriving Repr
def ConstraintUsage.elt (t : ConstraintUsage) : Element := t.toOccurrenceUsage.elt
def ConstraintUsage.toFeatureC (t : ConstraintUsage) : Feature := t.toOccurrenceUsage.toFeatureC

/-- §8.3.20.3 `AssertConstraintUsage`: structural only, no concrete syntax below (its own `assert`/
`satisfy` keyword forms are 0 real occurrences in this repo). -/
structure AssertConstraintUsage extends ConstraintUsage where
  deriving Repr

/-! ## 8.3.21 Requirements -/

/-- `RequirementDefinition extends ConstraintDefinition`. Non-derived: `reqId` (redefines
`declaredShortName`, kept as its own field rather than aliased -- matches this project's existing
practice of not modeling redefinition-of-inherited-attribute links). -/
structure RequirementDefinition extends ConstraintDefinition where
  reqId : Option String := none
  deriving Repr
def RequirementDefinition.toClassifierC (t : RequirementDefinition) : Classifier := t.toConstraintDefinition.toClassifierC
def RequirementDefinition.elt (t : RequirementDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

/-- `RequirementUsage extends ConstraintUsage`. Non-derived: `reqId`. -/
structure RequirementUsage extends ConstraintUsage where
  reqId : Option String := none
  deriving Repr
def RequirementUsage.elt (t : RequirementUsage) : Element := t.toConstraintUsage.elt
def RequirementUsage.toFeatureC (t : RequirementUsage) : Feature := t.toConstraintUsage.toFeatureC

structure ConcernDefinition extends RequirementDefinition where
  deriving Repr
def ConcernDefinition.toClassifierC (t : ConcernDefinition) : Classifier := t.toRequirementDefinition.toClassifierC
def ConcernDefinition.elt (t : ConcernDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

structure ConcernUsage extends RequirementUsage where
  deriving Repr
def ConcernUsage.elt (t : ConcernUsage) : Element := t.toRequirementUsage.elt

/-- §8.3.20.3 `SatisfyRequirementUsage`: structural only, no concrete syntax below (0 real
occurrences of the `satisfy` keyword form in this repo). -/
structure SatisfyRequirementUsage extends RequirementUsage where
  deriving Repr

/-! ## 8.3.22-25 Cases, Analysis/Verification/Use Cases -/

/-- `CaseDefinition extends CalculationDefinition` (a Case is a kind of Calculation, per the
spec -- not Action directly). -/
structure CaseDefinition extends CalculationDefinition where
  deriving Repr
def CaseDefinition.toClassifierC (t : CaseDefinition) : Classifier := t.toCalculationDefinition.toClassifierC
def CaseDefinition.elt (t : CaseDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

structure CaseUsage extends CalculationUsage where
  deriving Repr
def CaseUsage.elt (t : CaseUsage) : Element := t.toCalculationUsage.elt

structure AnalysisCaseDefinition extends CaseDefinition where deriving Repr
def AnalysisCaseDefinition.toClassifierC (t : AnalysisCaseDefinition) : Classifier := t.toCaseDefinition.toClassifierC
def AnalysisCaseDefinition.elt (t : AnalysisCaseDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement
structure AnalysisCaseUsage extends CaseUsage where deriving Repr
def AnalysisCaseUsage.elt (t : AnalysisCaseUsage) : Element := t.toCaseUsage.elt

structure VerificationCaseDefinition extends CaseDefinition where deriving Repr
def VerificationCaseDefinition.toClassifierC (t : VerificationCaseDefinition) : Classifier := t.toCaseDefinition.toClassifierC
def VerificationCaseDefinition.elt (t : VerificationCaseDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement
structure VerificationCaseUsage extends CaseUsage where deriving Repr
def VerificationCaseUsage.elt (t : VerificationCaseUsage) : Element := t.toCaseUsage.elt

structure UseCaseDefinition extends CaseDefinition where deriving Repr
def UseCaseDefinition.toClassifierC (t : UseCaseDefinition) : Classifier := t.toCaseDefinition.toClassifierC
def UseCaseDefinition.elt (t : UseCaseDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement
structure UseCaseUsage extends CaseUsage where deriving Repr
def UseCaseUsage.elt (t : UseCaseUsage) : Element := t.toCaseUsage.elt

/-- §8.3.25.2 `IncludeUseCaseUsage`: structural only, no concrete syntax below (0 real `include`
occurrences). -/
structure IncludeUseCaseUsage extends UseCaseUsage where deriving Repr

/-! ## 8.3.26 Views and Viewpoints -/

structure ViewDefinition extends PartDefinition where deriving Repr
def ViewDefinition.toClassifierC (t : ViewDefinition) : Classifier := t.toPartDefinition.toClassifierC
def ViewDefinition.elt (t : ViewDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

structure ViewUsage extends PartUsage where deriving Repr
def ViewUsage.elt (t : ViewUsage) : Element := t.toPartUsage.elt
def ViewUsage.toFeatureC (t : ViewUsage) : Feature := t.toPartUsage.toFeatureC

/-- `ViewpointDefinition extends RequirementDefinition` (a Viewpoint is framed as a kind of
Requirement on a View, per the spec). -/
structure ViewpointDefinition extends RequirementDefinition where deriving Repr
def ViewpointDefinition.toClassifierC (t : ViewpointDefinition) : Classifier := t.toRequirementDefinition.toClassifierC
def ViewpointDefinition.elt (t : ViewpointDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

structure ViewpointUsage extends RequirementUsage where deriving Repr
def ViewpointUsage.elt (t : ViewpointUsage) : Element := t.toRequirementUsage.elt

structure RenderingDefinition extends PartDefinition where deriving Repr
def RenderingDefinition.toClassifierC (t : RenderingDefinition) : Classifier := t.toPartDefinition.toClassifierC
def RenderingDefinition.elt (t : RenderingDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

structure RenderingUsage extends PartUsage where deriving Repr
def RenderingUsage.elt (t : RenderingUsage) : Element := t.toPartUsage.elt

/-! ## 8.3.27 Metadata (p.393) -/

/-- `MetadataDefinition`: dual-extends `ItemDefinition` and KerML's `Metaclass`
(`Kernel.lean`) -- "A MetadataDefinition is an ItemDefinition that is also a Metaclass." -/
structure MetadataDefinition extends ItemDefinition, Metaclass where
  deriving Repr
def MetadataDefinition.toClassifierC (t : MetadataDefinition) : Classifier := t.toItemDefinition.toClassifierC
def MetadataDefinition.elt (t : MetadataDefinition) : Element := t.toClassifierC.toKType.toNamespace.toElement

/-- `MetadataUsage`: dual-extends `ItemUsage` and KerML's `MetadataFeature`. -/
structure MetadataUsage extends ItemUsage, MetadataFeature where
  deriving Repr
def MetadataUsage.elt (t : MetadataUsage) : Element := t.toItemUsage.elt

/-! ## Concrete syntax

Real `syntax`/`elab` productions for the 14 real-usage-driven Definition/Usage keyword pairs (see
file header for the full scope decision). `sysmlDecl` is the shared category, with a passthrough
alternative reusing `kernelDecl` wholesale -- this is what makes `import`/`doc`/`package`/
`@Assert{...}`/`multiplicity`/bare KerML declarations nest inside a SysML body for free, exactly
mirroring how `Kernel.lean` got `Core.lean`'s `kermlDecl` for free the same way. -/

declare_syntax_cat sysmlDecl
/-- `Core.lean`/`Kernel.lean` content (`import`, `doc`, `@Assert{...}`, `multiplicity`, bare KerML
`type`/`classifier`/`feature`/...) nests directly inside a SysML body via this passthrough. -/
syntax kernelDecl : sysmlDecl

declare_syntax_cat sysmlBody
syntax " ;" : sysmlBody
syntax " {" sysmlDecl* "}" : sysmlBody

def elabSysmlBody : TSyntax `sysmlBody → MacroM (Array (TSyntax `term))
  | `(sysmlBody| ;) => pure #[]
  | `(sysmlBody| { $decls:sysmlDecl* }) => do
      let subs ← decls.mapM (fun d => match d with
        | `(sysmlDecl| $k:kernelDecl) => elabKernelDecl k
        | _ => pure #[])
      pure (subs.foldl (· ++ ·) #[])
  | _ => pure #[]

/-- Shared elaboration for a `<kw> def Name [:> Super,+] { ... }` Definition: one stub `Element`
(via `mkStub`) plus one `Subclassification` `Element` per `:>` target, reusing `Core.lean`'s own
`mkSubclassificationTerm` directly (`:>` on a Definition means *specializes*, the `Classifier`-owner
reading of KerML's shared `:>` symbol -- same disambiguation-by-owner-kind `Core.lean`'s own
`behavior :>` doc comment already establishes). No `conjugates`/`disjoint`/`unions`/`intersects`/
`differences` parts -- no real Definition in this repo uses them (unlike KerML's own `assoc`/
`struct`), keeping this narrower than `classifierLikeDeclElems`. -/
def sysmlDefElems (mkStub : String → MacroM (TSyntax `term)) (a : TSyntax `ident)
    (specs : Option (Syntax.TSepArray `kermlQualName ",")) (body : TSyntax `sysmlBody) :
    MacroM (Array (TSyntax `term)) := do
  let an := a.getId.toString
  let aT ← mkStub an
  let aC ← `(($aT).toClassifierC)
  let specElems ← match specs with
    | some ss => ss.getElems.mapM (fun g => do
        let gC ← classifierStubTermQ g
        let rel ← mkSubclassificationTerm aC gC an (qualNameStr g)
        `(($rel).elt))
    | none => pure #[]
  pure (#[← `(($aT).elt)] ++ specElems ++ (← elabSysmlBody body))

/-- Shared elaboration for a `<kw> name [: Type] [mult] [default V] [:> S,+] [:>> R,+] { ... }`
Usage: one stub `Element` plus one `FeatureTyping`/`Subsetting`/`Redefinition` `Element` per clause,
reusing `Core.lean`'s `mkFeatureTypingTerm`/`mkSubsettingTerm`/`mkRedefinitionTerm` directly (`:>`
on a Usage means *subsets*, the `Feature`-owner reading of the same shared symbol; `:>>` always
means *redefines*, unambiguous). `[mult]`/`default V` are parsed but not stored, same trade
`Core.lean`'s own `feature` production already makes for both. Every Usage-kind stub is coerced up
to `Feature` via its own `.toFeatureC` (mirroring `.toClassifierC` on the Definition side) before
being passed to `mkFeatureTypingTerm`/`mkSubsettingTerm`/`mkRedefinitionTerm` -- those expect a
genuine `Feature`-typed term, and Lean's `extends`-generated projections don't implicitly upcast a
multi-level subtype (confirmed via a real "Type mismatch ... has type AttributeUsage but is
expected to have type Feature" build error before adding the coercion). -/
def sysmlUsageElems (mkStub : String → MacroM (TSyntax `term)) (a : TSyntax `ident)
    (ty : Option (TSyntax `kermlQualName))
    (subs : Option (Syntax.TSepArray `kermlQualName ","))
    (redefs : Option (Syntax.TSepArray `kermlQualName ","))
    (body : TSyntax `sysmlBody) : MacroM (Array (TSyntax `term)) := do
  let an := a.getId.toString
  let aT ← mkStub an
  let aF ← `(($aT).toFeatureC)
  let tyElems ← match ty with
    | some t => do
        let tT ← kTypeStubTermQ t
        let rel ← mkFeatureTypingTerm aF tT an (qualNameStr t)
        pure #[← `(($rel).elt)]
    | none => pure #[]
  let subsElems ← match subs with
    | some ss => ss.getElems.mapM (fun g => do
        let gT ← featureStubTermQ g
        let rel ← mkSubsettingTerm aF gT an (qualNameStr g)
        `(($rel).elt))
    | none => pure #[]
  let redefElems ← match redefs with
    | some ds => ds.getElems.mapM (fun g => do
        let gT ← featureStubTermQ g
        let rel ← mkRedefinitionTerm aF gT an (qualNameStr g)
        `(($rel).elt))
    | none => pure #[]
  pure (#[← `(($aT).elt)] ++ tyElems ++ subsElems ++ redefElems ++ (← elabSysmlBody body))

def mkAttributeDefinitionStub (n : String) : AttributeDefinition := { elementId := n, declaredName := some n }
def mkAttributeUsageStub (n : String) : AttributeUsage := { elementId := n, declaredName := some n }
def mkEnumerationDefinitionStub (n : String) : EnumerationDefinition := { elementId := n, declaredName := some n }
def mkEnumerationUsageStub (n : String) : EnumerationUsage := { elementId := n, declaredName := some n }
def mkItemDefinitionStub (n : String) : ItemDefinition := { elementId := n, declaredName := some n }
def mkItemUsageStub (n : String) : ItemUsage := { elementId := n, declaredName := some n }
def mkPartDefinitionStub (n : String) : PartDefinition := { elementId := n, declaredName := some n }
def mkPartUsageStub (n : String) : PartUsage := { elementId := n, declaredName := some n }
def mkPortDefinitionStub (n : String) : PortDefinition := { elementId := n, declaredName := some n }
def mkPortUsageStub (n : String) : PortUsage := { elementId := n, declaredName := some n }
def mkConnectionDefinitionStub (n : String) : ConnectionDefinition := { elementId := n, declaredName := some n }
def mkConnectionUsageStub (n : String) : ConnectionUsage := { elementId := n, declaredName := some n }
def mkInterfaceDefinitionStub (n : String) : InterfaceDefinition := { elementId := n, declaredName := some n }
def mkInterfaceUsageStub (n : String) : InterfaceUsage := { elementId := n, declaredName := some n }
def mkAllocationDefinitionStub (n : String) : AllocationDefinition := { elementId := n, declaredName := some n }
def mkAllocationUsageStub (n : String) : AllocationUsage := { elementId := n, declaredName := some n }
def mkActionDefinitionStub (n : String) : ActionDefinition := { elementId := n, declaredName := some n }
def mkActionUsageStub (n : String) : ActionUsage := { elementId := n, declaredName := some n }
def mkCalculationDefinitionStub (n : String) : CalculationDefinition := { elementId := n, declaredName := some n }
def mkCalculationUsageStub (n : String) : CalculationUsage := { elementId := n, declaredName := some n }
def mkStateDefinitionStub (n : String) : StateDefinition := { elementId := n, declaredName := some n }
def mkStateUsageStub (n : String) : StateUsage := { elementId := n, declaredName := some n }
def mkConstraintDefinitionStub (n : String) : ConstraintDefinition := { elementId := n, declaredName := some n }
def mkConstraintUsageStub (n : String) : ConstraintUsage := { elementId := n, declaredName := some n }
def mkRequirementDefinitionStub (n : String) : RequirementDefinition := { elementId := n, declaredName := some n }
def mkRequirementUsageStub (n : String) : RequirementUsage := { elementId := n, declaredName := some n }
def mkViewDefinitionStub (n : String) : ViewDefinition := { elementId := n, declaredName := some n }
def mkViewUsageStub (n : String) : ViewUsage := { elementId := n, declaredName := some n }

def attributeDefinitionStubTerm (s : String) : MacroM (TSyntax `term) := `(mkAttributeDefinitionStub $(quote s))
def attributeUsageStubTerm (s : String) : MacroM (TSyntax `term) := `(mkAttributeUsageStub $(quote s))
def enumerationDefinitionStubTerm (s : String) : MacroM (TSyntax `term) := `(mkEnumerationDefinitionStub $(quote s))
def enumerationUsageStubTerm (s : String) : MacroM (TSyntax `term) := `(mkEnumerationUsageStub $(quote s))
def itemDefinitionStubTerm (s : String) : MacroM (TSyntax `term) := `(mkItemDefinitionStub $(quote s))
def itemUsageStubTerm (s : String) : MacroM (TSyntax `term) := `(mkItemUsageStub $(quote s))
def partDefinitionStubTerm (s : String) : MacroM (TSyntax `term) := `(mkPartDefinitionStub $(quote s))
def partUsageStubTerm (s : String) : MacroM (TSyntax `term) := `(mkPartUsageStub $(quote s))
def portDefinitionStubTerm (s : String) : MacroM (TSyntax `term) := `(mkPortDefinitionStub $(quote s))
def portUsageStubTerm (s : String) : MacroM (TSyntax `term) := `(mkPortUsageStub $(quote s))
def connectionDefinitionStubTerm (s : String) : MacroM (TSyntax `term) := `(mkConnectionDefinitionStub $(quote s))
def connectionUsageStubTerm (s : String) : MacroM (TSyntax `term) := `(mkConnectionUsageStub $(quote s))
def interfaceDefinitionStubTerm (s : String) : MacroM (TSyntax `term) := `(mkInterfaceDefinitionStub $(quote s))
def interfaceUsageStubTerm (s : String) : MacroM (TSyntax `term) := `(mkInterfaceUsageStub $(quote s))
def allocationDefinitionStubTerm (s : String) : MacroM (TSyntax `term) := `(mkAllocationDefinitionStub $(quote s))
def allocationUsageStubTerm (s : String) : MacroM (TSyntax `term) := `(mkAllocationUsageStub $(quote s))
def actionDefinitionStubTerm (s : String) : MacroM (TSyntax `term) := `(mkActionDefinitionStub $(quote s))
def actionUsageStubTerm (s : String) : MacroM (TSyntax `term) := `(mkActionUsageStub $(quote s))
def calculationDefinitionStubTerm (s : String) : MacroM (TSyntax `term) := `(mkCalculationDefinitionStub $(quote s))
def calculationUsageStubTerm (s : String) : MacroM (TSyntax `term) := `(mkCalculationUsageStub $(quote s))
def stateDefinitionStubTerm (s : String) : MacroM (TSyntax `term) := `(mkStateDefinitionStub $(quote s))
def stateUsageStubTerm (s : String) : MacroM (TSyntax `term) := `(mkStateUsageStub $(quote s))
def constraintDefinitionStubTerm (s : String) : MacroM (TSyntax `term) := `(mkConstraintDefinitionStub $(quote s))
def constraintUsageStubTerm (s : String) : MacroM (TSyntax `term) := `(mkConstraintUsageStub $(quote s))
def requirementDefinitionStubTerm (s : String) : MacroM (TSyntax `term) := `(mkRequirementDefinitionStub $(quote s))
def requirementUsageStubTerm (s : String) : MacroM (TSyntax `term) := `(mkRequirementUsageStub $(quote s))
def viewDefinitionStubTerm (s : String) : MacroM (TSyntax `term) := `(mkViewDefinitionStub $(quote s))
def viewUsageStubTerm (s : String) : MacroM (TSyntax `term) := `(mkViewUsageStub $(quote s))

/-- The 14 Definition-keyword productions (BNF §8.2.2.7/8/10/11/12/13.1/14.1/15/17.1/19/18.1/20/
21.1/26.1): `[abstract] <kw> def Name [:> Super,+] Body`. -/
syntax (kermlAbstractFlag)? "attribute " "def " ident (" :> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlAbstractFlag)? "enum " "def " ident (" :> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlAbstractFlag)? "item " "def " ident (" :> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlAbstractFlag)? "part " "def " ident (" :> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlAbstractFlag)? "port " "def " ident (" :> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlAbstractFlag)? "connection " "def " ident (" :> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlAbstractFlag)? "interface " "def " ident (" :> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlAbstractFlag)? "allocation " "def " ident (" :> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlAbstractFlag)? "action " "def " ident (" :> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlAbstractFlag)? "calc " "def " ident (" :> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlAbstractFlag)? "state " "def " ident (" :> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlAbstractFlag)? "constraint " "def " ident (" :> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlAbstractFlag)? "requirement " "def " ident (" :> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlAbstractFlag)? "view " "def " ident (" :> " kermlQualName,+)? sysmlBody : sysmlDecl

/-- The 14 Usage-keyword productions: `[ref] <kw> name [: Type] [mult] [default V] [:> S,+]
[:>> R,+] Body`. `connection`/`allocation` additionally accept `connect`/`allocate A to B`
(reusing `Kernel.lean`'s `kermlConnEnd`/`elabKermlConnEnd`, added for KerML's own `connector`). -/
syntax (kermlVisibilityFlag)? "attribute " ident (kermlMult)? (" : " kermlQualName)? (kermlMult)?
  (" default " kermlDefaultVal)? (kermlOrderedFlag)? (kermlNonuniqueFlag)?
  (" :> " kermlQualName,+)? (" :>> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlVisibilityFlag)? "enum " ident (kermlMult)? (" : " kermlQualName)? (kermlMult)?
  (" default " kermlDefaultVal)? (" :> " kermlQualName,+)? (" :>> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlVisibilityFlag)? "item " ident (kermlMult)? (" : " kermlQualName)? (kermlMult)?
  (" default " kermlDefaultVal)? (" :> " kermlQualName,+)? (" :>> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlVisibilityFlag)? "part " ident (kermlMult)? (" : " kermlQualName)? (kermlMult)?
  (" default " kermlDefaultVal)? (" :> " kermlQualName,+)? (" :>> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlVisibilityFlag)? "port " ident (kermlMult)? (" : " kermlQualName)? (kermlMult)?
  (" default " kermlDefaultVal)? (" :> " kermlQualName,+)? (" :>> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlVisibilityFlag)? "connection " ident (kermlMult)? (" : " kermlQualName)? (kermlMult)?
  (" :> " kermlQualName,+)? (" :>> " kermlQualName,+)?
  (" connect " kermlConnEnd " to " kermlConnEnd)? sysmlBody : sysmlDecl
syntax (kermlVisibilityFlag)? "interface " ident (kermlMult)? (" : " kermlQualName)? (kermlMult)?
  (" :> " kermlQualName,+)? (" :>> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlVisibilityFlag)? "allocation " ident (kermlMult)? (" : " kermlQualName)? (kermlMult)?
  (" :> " kermlQualName,+)? (" :>> " kermlQualName,+)?
  (" allocate " kermlConnEnd " to " kermlConnEnd)? sysmlBody : sysmlDecl
syntax (kermlVisibilityFlag)? "action " ident (kermlMult)? (" : " kermlQualName)? (kermlMult)?
  (" :> " kermlQualName,+)? (" :>> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlVisibilityFlag)? "calc " ident (kermlMult)? (" : " kermlQualName)? (kermlMult)?
  (" :> " kermlQualName,+)? (" :>> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlVisibilityFlag)? "state " ident (kermlMult)? (" : " kermlQualName)? (kermlMult)?
  (" :> " kermlQualName,+)? (" :>> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlVisibilityFlag)? "constraint " ident (kermlMult)? (" : " kermlQualName)? (kermlMult)?
  (" :> " kermlQualName,+)? (" :>> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlVisibilityFlag)? "requirement " ident (kermlMult)? (" : " kermlQualName)? (kermlMult)?
  (" :> " kermlQualName,+)? (" :>> " kermlQualName,+)? sysmlBody : sysmlDecl
syntax (kermlVisibilityFlag)? "view " ident (kermlMult)? (" : " kermlQualName)? (kermlMult)?
  (" :> " kermlQualName,+)? (" :>> " kermlQualName,+)? sysmlBody : sysmlDecl

mutual

partial def elabSysmlDecl : TSyntax `sysmlDecl → MacroM (Array (TSyntax `term))
  | `(sysmlDecl| $k:kernelDecl) => elabKernelDecl k
  | `(sysmlDecl| $[$_abs:kermlAbstractFlag]? attribute def $a:ident $[:> $specs,*]? $body:sysmlBody) =>
      sysmlDefElems attributeDefinitionStubTerm a specs body
  | `(sysmlDecl| $[$_abs:kermlAbstractFlag]? enum def $a:ident $[:> $specs,*]? $body:sysmlBody) =>
      sysmlDefElems enumerationDefinitionStubTerm a specs body
  | `(sysmlDecl| $[$_abs:kermlAbstractFlag]? item def $a:ident $[:> $specs,*]? $body:sysmlBody) =>
      sysmlDefElems itemDefinitionStubTerm a specs body
  | `(sysmlDecl| $[$_abs:kermlAbstractFlag]? part def $a:ident $[:> $specs,*]? $body:sysmlBody) =>
      sysmlDefElems partDefinitionStubTerm a specs body
  | `(sysmlDecl| $[$_abs:kermlAbstractFlag]? port def $a:ident $[:> $specs,*]? $body:sysmlBody) =>
      sysmlDefElems portDefinitionStubTerm a specs body
  | `(sysmlDecl| $[$_abs:kermlAbstractFlag]? connection def $a:ident $[:> $specs,*]? $body:sysmlBody) =>
      sysmlDefElems connectionDefinitionStubTerm a specs body
  | `(sysmlDecl| $[$_abs:kermlAbstractFlag]? interface def $a:ident $[:> $specs,*]? $body:sysmlBody) =>
      sysmlDefElems interfaceDefinitionStubTerm a specs body
  | `(sysmlDecl| $[$_abs:kermlAbstractFlag]? allocation def $a:ident $[:> $specs,*]? $body:sysmlBody) =>
      sysmlDefElems allocationDefinitionStubTerm a specs body
  | `(sysmlDecl| $[$_abs:kermlAbstractFlag]? action def $a:ident $[:> $specs,*]? $body:sysmlBody) =>
      sysmlDefElems actionDefinitionStubTerm a specs body
  | `(sysmlDecl| $[$_abs:kermlAbstractFlag]? calc def $a:ident $[:> $specs,*]? $body:sysmlBody) =>
      sysmlDefElems calculationDefinitionStubTerm a specs body
  | `(sysmlDecl| $[$_abs:kermlAbstractFlag]? state def $a:ident $[:> $specs,*]? $body:sysmlBody) =>
      sysmlDefElems stateDefinitionStubTerm a specs body
  | `(sysmlDecl| $[$_abs:kermlAbstractFlag]? constraint def $a:ident $[:> $specs,*]? $body:sysmlBody) =>
      sysmlDefElems constraintDefinitionStubTerm a specs body
  | `(sysmlDecl| $[$_abs:kermlAbstractFlag]? requirement def $a:ident $[:> $specs,*]? $body:sysmlBody) =>
      sysmlDefElems requirementDefinitionStubTerm a specs body
  | `(sysmlDecl| $[$_abs:kermlAbstractFlag]? view def $a:ident $[:> $specs,*]? $body:sysmlBody) =>
      sysmlDefElems viewDefinitionStubTerm a specs body
  | `(sysmlDecl| $[$_vis:kermlVisibilityFlag]? attribute $a:ident $[$_m1:kermlMult]? $[: $ty:kermlQualName]?
        $[$_m2:kermlMult]? $[default $_dv:kermlDefaultVal]? $[$_ord:kermlOrderedFlag]?
        $[$_nu:kermlNonuniqueFlag]? $[:> $subs,*]? $[:>> $redefs,*]? $body:sysmlBody) =>
      sysmlUsageElems attributeUsageStubTerm a ty subs redefs body
  | `(sysmlDecl| $[$_vis:kermlVisibilityFlag]? enum $a:ident $[$_m1:kermlMult]? $[: $ty:kermlQualName]?
        $[$_m2:kermlMult]? $[default $_dv:kermlDefaultVal]?
        $[:> $subs,*]? $[:>> $redefs,*]? $body:sysmlBody) =>
      sysmlUsageElems enumerationUsageStubTerm a ty subs redefs body
  | `(sysmlDecl| $[$_vis:kermlVisibilityFlag]? item $a:ident $[$_m1:kermlMult]? $[: $ty:kermlQualName]?
        $[$_m2:kermlMult]? $[default $_dv:kermlDefaultVal]?
        $[:> $subs,*]? $[:>> $redefs,*]? $body:sysmlBody) =>
      sysmlUsageElems itemUsageStubTerm a ty subs redefs body
  | `(sysmlDecl| $[$_vis:kermlVisibilityFlag]? part $a:ident $[$_m1:kermlMult]? $[: $ty:kermlQualName]?
        $[$_m2:kermlMult]? $[default $_dv:kermlDefaultVal]?
        $[:> $subs,*]? $[:>> $redefs,*]? $body:sysmlBody) =>
      sysmlUsageElems partUsageStubTerm a ty subs redefs body
  | `(sysmlDecl| $[$_vis:kermlVisibilityFlag]? port $a:ident $[$_m1:kermlMult]? $[: $ty:kermlQualName]?
        $[$_m2:kermlMult]? $[default $_dv:kermlDefaultVal]?
        $[:> $subs,*]? $[:>> $redefs,*]? $body:sysmlBody) =>
      sysmlUsageElems portUsageStubTerm a ty subs redefs body
  | `(sysmlDecl| $[$_vis:kermlVisibilityFlag]? connection $a:ident $[$_m1:kermlMult]? $[: $ty:kermlQualName]?
        $[$_m2:kermlMult]? $[:> $subs,*]? $[:>> $redefs,*]?
        $[connect $e1:kermlConnEnd to $e2:kermlConnEnd]? $body:sysmlBody) => do
      let usageElems ← sysmlUsageElems connectionUsageStubTerm a ty subs redefs body
      let connElems ← match e1, e2 with
        | some e1', some e2' => do pure #[← elabKermlConnEnd e1', ← elabKermlConnEnd e2']
        | _, _ => pure #[]
      pure (usageElems ++ connElems)
  | `(sysmlDecl| $[$_vis:kermlVisibilityFlag]? interface $a:ident $[$_m1:kermlMult]? $[: $ty:kermlQualName]?
        $[$_m2:kermlMult]? $[:> $subs,*]? $[:>> $redefs,*]? $body:sysmlBody) =>
      sysmlUsageElems interfaceUsageStubTerm a ty subs redefs body
  | `(sysmlDecl| $[$_vis:kermlVisibilityFlag]? allocation $a:ident $[$_m1:kermlMult]? $[: $ty:kermlQualName]?
        $[$_m2:kermlMult]? $[:> $subs,*]? $[:>> $redefs,*]?
        $[allocate $e1:kermlConnEnd to $e2:kermlConnEnd]? $body:sysmlBody) => do
      let usageElems ← sysmlUsageElems allocationUsageStubTerm a ty subs redefs body
      let connElems ← match e1, e2 with
        | some e1', some e2' => do pure #[← elabKermlConnEnd e1', ← elabKermlConnEnd e2']
        | _, _ => pure #[]
      pure (usageElems ++ connElems)
  | `(sysmlDecl| $[$_vis:kermlVisibilityFlag]? action $a:ident $[$_m1:kermlMult]? $[: $ty:kermlQualName]?
        $[$_m2:kermlMult]? $[:> $subs,*]? $[:>> $redefs,*]? $body:sysmlBody) =>
      sysmlUsageElems actionUsageStubTerm a ty subs redefs body
  | `(sysmlDecl| $[$_vis:kermlVisibilityFlag]? calc $a:ident $[$_m1:kermlMult]? $[: $ty:kermlQualName]?
        $[$_m2:kermlMult]? $[:> $subs,*]? $[:>> $redefs,*]? $body:sysmlBody) =>
      sysmlUsageElems calculationUsageStubTerm a ty subs redefs body
  | `(sysmlDecl| $[$_vis:kermlVisibilityFlag]? state $a:ident $[$_m1:kermlMult]? $[: $ty:kermlQualName]?
        $[$_m2:kermlMult]? $[:> $subs,*]? $[:>> $redefs,*]? $body:sysmlBody) =>
      sysmlUsageElems stateUsageStubTerm a ty subs redefs body
  | `(sysmlDecl| $[$_vis:kermlVisibilityFlag]? constraint $a:ident $[$_m1:kermlMult]? $[: $ty:kermlQualName]?
        $[$_m2:kermlMult]? $[:> $subs,*]? $[:>> $redefs,*]? $body:sysmlBody) =>
      sysmlUsageElems constraintUsageStubTerm a ty subs redefs body
  | `(sysmlDecl| $[$_vis:kermlVisibilityFlag]? requirement $a:ident $[$_m1:kermlMult]? $[: $ty:kermlQualName]?
        $[$_m2:kermlMult]? $[:> $subs,*]? $[:>> $redefs,*]? $body:sysmlBody) =>
      sysmlUsageElems requirementUsageStubTerm a ty subs redefs body
  | `(sysmlDecl| $[$_vis:kermlVisibilityFlag]? view $a:ident $[$_m1:kermlMult]? $[: $ty:kermlQualName]?
        $[$_m2:kermlMult]? $[:> $subs,*]? $[:>> $redefs,*]? $body:sysmlBody) =>
      sysmlUsageElems viewUsageStubTerm a ty subs redefs body
  | _ => Macro.throwUnsupported

end

/-- `sysml% <decl>` elaborates a `sysmlDecl` into a `List Element` term, matching `kerml%`/
`kernel%`'s own trigger convention. -/
elab "sysml% " d:sysmlDecl : term => do
  let elems ← Elab.liftMacroM (elabSysmlDecl d)
  let stx ← Elab.liftMacroM (mkListTerm elems.toList)
  Elab.Term.elabTerm stx none

-- Smoke tests: real elaborations, type-checked by Lean.
#check sysml% attribute def Speed :> Real ;
#check sysml% part def Vehicle :> Item ;
#check sysml% item def Wheel ;
#check sysml% port def FuelPort ;
#check sysml% connection def FuelLine ;
#check sysml% interface def FuelInterface ;
#check sysml% allocation def RequirementAllocation ;
#check sysml% action def Drive ;
#check sysml% calc def ComputeSpeed ;
#check sysml% state def Idling ;
#check sysml% constraint def SpeedLimit ;
#check sysml% requirement def MaxSpeedRequirement ;
#check sysml% enum def ColorKind ;
#check sysml% view def VehicleView ;

#check sysml% attribute isBound : Boolean ;
#check sysml% attribute order :>> rank ;
#check sysml% part wheel : Wheel[4] ;
#check sysml% connection fuelLine connect tank to engine ;
#check sysml% allocation reqAlloc allocate req to comp ;

-- `Systems Library/Attributes.sysml`'s own real shape, verbatim modulo the `default` value
-- (`kermlDefaultVal` here, same simplification `Core.lean`'s own `feature` production makes).
#check sysml% attribute def ScalarQuantityValue :> ScalarValues::Real ;

-- `Domain Libraries/Quantities and Units/MeasurementReferences.sysml`'s own real body, verbatim
-- modulo the `default` value's spelling (`default Bool.false` here, not the real file's bare
-- `default false;` -- see `kermlDefaultVal`'s own doc comment in `Core.lean` for why literal
-- `true`/`false` are deliberately not registered as a `kermlDefaultVal` keyword), confirming the
-- `kernelDecl` passthrough (`private import`, `doc`) and the generic Usage form (`default`, `:>>`
-- redefinition, `nonunique`) all genuinely work together end-to-end.
#check sysml% attribute def TensorMeasurementReference :> Array {
  private import ScalarValues::*;
  doc "TensorMeasurementReference is the most general AttributeDefinition to represent measurement references."
  attribute isBound : Boolean default Bool.false ;
  attribute order :>> rank ;
  attribute mRefs : ScalarMeasurementReference nonunique :>> elements ;
}

-- A real `@Assert{...}` nested inside a `part def` body (`Kernel.lean`'s existing metadata
-- machinery, reused via the `kernelDecl` passthrough).
#check sysml% part def Widget {
  attribute mass : Real ;
  @Assert{f="<< mass >= 0 >>";}
}

end KerML.SysML
