import TypedLayout.Backend.ExactCssProjection

namespace TypedLayout.Backend.ExactCss

open TypedLayout.Core

namespace ExactDocument
namespace ProbePlan

/-- Typed selector handle for a generated exact-fragment node.

The selector stays class-label based inside the probe plan. Raw selector text is
only projected at the outer browser-probe boundary. -/
inductive Selector where
  | generatedClass (className : ClassName)
  deriving DecidableEq, Repr

namespace Selector

def className : Selector → ClassName
  | .generatedClass className => className

/-- Outer-boundary CSS selector text for a future browser harness. -/
def text : Selector → String
  | .generatedClass className => "." ++ ClassName.render className

theorem generatedClass_className (className : ClassName) :
    (Selector.generatedClass className).className = className :=
  rfl

theorem generatedClass_text (className : ClassName) :
    (Selector.generatedClass className).text = "." ++ ClassName.render className :=
  rfl

end Selector

/-- Typed probe target for one lowered exact-fragment node. -/
structure Target where
  selector : Selector
  kind : LayoutKind
  backendStyle : Style
  sourceBox : Box
  deriving DecidableEq, Repr

namespace Target

def className (target : Target) : ClassName :=
  target.selector.className

def selectorText (target : Target) : String :=
  target.selector.text

def origin (target : Target) : Origin :=
  target.sourceBox.origin

def extent (target : Target) : ExactExtent :=
  target.sourceBox.extent

def size (target : Target) : Size :=
  target.backendStyle.size

/-- Convert a typed backend-fidelity node expectation into a browser-probe target. -/
def ofExpectation (expectation : Fidelity.NodeExpectation) : Target :=
  { selector := .generatedClass expectation.className
  , kind := expectation.kind
  , backendStyle := expectation.style
  , sourceBox := expectation.box
  }

theorem ofExpectation_className (expectation : Fidelity.NodeExpectation) :
    (ofExpectation expectation).className = expectation.className :=
  rfl

theorem ofExpectation_kind (expectation : Fidelity.NodeExpectation) :
    (ofExpectation expectation).kind = expectation.kind :=
  rfl

theorem ofExpectation_backendStyle (expectation : Fidelity.NodeExpectation) :
    (ofExpectation expectation).backendStyle = expectation.style :=
  rfl

theorem ofExpectation_sourceBox (expectation : Fidelity.NodeExpectation) :
    (ofExpectation expectation).sourceBox = expectation.box :=
  rfl

theorem ofExpectation_selectorText (expectation : Fidelity.NodeExpectation) :
    (ofExpectation expectation).selectorText = "." ++ ClassName.render expectation.className :=
  rfl

theorem ofExpectation_origin (expectation : Fidelity.NodeExpectation) :
    (ofExpectation expectation).origin = expectation.origin :=
  rfl

theorem ofExpectation_extent (expectation : Fidelity.NodeExpectation) :
    (ofExpectation expectation).extent = expectation.extent :=
  rfl

theorem ofExpectation_size (expectation : Fidelity.NodeExpectation) :
    (ofExpectation expectation).size = expectation.size :=
  rfl

end Target

/-- Typed browser-probe plan for a lowered exact-fragment document. -/
structure Plan where
  targetProfile : BlessedCssProfile
  sourceGuarantee : GuaranteeClass
  root : Target
  targets : List Target
  deriving DecidableEq, Repr

namespace Plan

def nodeCount (plan : Plan) : Nat :=
  plan.targets.length

def rootClassName (plan : Plan) : ClassName :=
  plan.root.className

def labels (plan : Plan) : List ClassName :=
  plan.targets.map Target.className

def kinds (plan : Plan) : List LayoutKind :=
  plan.targets.map Target.kind

def styles (plan : Plan) : List Style :=
  plan.targets.map Target.backendStyle

def boxes (plan : Plan) : List Box :=
  plan.targets.map Target.sourceBox

def sizes (plan : Plan) : List Size :=
  plan.targets.map Target.size

def selectorTexts (plan : Plan) : List String :=
  plan.targets.map Target.selectorText

theorem labels_length (plan : Plan) :
    plan.labels.length = plan.nodeCount := by
  simp [labels, nodeCount]

theorem boxes_length (plan : Plan) :
    plan.boxes.length = plan.nodeCount := by
  simp [boxes, nodeCount]

theorem styles_length (plan : Plan) :
    plan.styles.length = plan.nodeCount := by
  simp [styles, nodeCount]

theorem sizes_length (plan : Plan) :
    plan.sizes.length = plan.nodeCount := by
  simp [sizes, nodeCount]

theorem selectorTexts_length (plan : Plan) :
    plan.selectorTexts.length = plan.nodeCount := by
  simp [selectorTexts, nodeCount]

/-- Convert typed backend-fidelity expectations into a typed browser-probe plan. -/
def ofExpectation (expectation : Fidelity.DocumentExpectation) : Plan :=
  { targetProfile := expectation.targetProfile
  , sourceGuarantee := expectation.sourceGuarantee
  , root := Target.ofExpectation expectation.root
  , targets := expectation.nodes.map Target.ofExpectation
  }

theorem ofExpectation_targetProfile (expectation : Fidelity.DocumentExpectation) :
    (ofExpectation expectation).targetProfile = expectation.targetProfile :=
  rfl

theorem ofExpectation_sourceGuarantee (expectation : Fidelity.DocumentExpectation) :
    (ofExpectation expectation).sourceGuarantee = expectation.sourceGuarantee :=
  rfl

theorem ofExpectation_rootClassName (expectation : Fidelity.DocumentExpectation) :
    (ofExpectation expectation).rootClassName = expectation.rootClassName :=
  rfl

theorem ofExpectation_labels (expectation : Fidelity.DocumentExpectation) :
    (ofExpectation expectation).labels = expectation.labels := by
  simp [ofExpectation, labels, Fidelity.DocumentExpectation.labels, Target.ofExpectation,
    Target.className, Selector.className]

theorem ofExpectation_kinds (expectation : Fidelity.DocumentExpectation) :
    (ofExpectation expectation).kinds = expectation.kinds := by
  simp [ofExpectation, kinds, Fidelity.DocumentExpectation.kinds, Target.ofExpectation]

theorem ofExpectation_styles (expectation : Fidelity.DocumentExpectation) :
    (ofExpectation expectation).styles = expectation.styles := by
  simp [ofExpectation, styles, Fidelity.DocumentExpectation.styles, Target.ofExpectation]

theorem ofExpectation_boxes (expectation : Fidelity.DocumentExpectation) :
    (ofExpectation expectation).boxes = expectation.boxes := by
  simp [ofExpectation, boxes, Fidelity.DocumentExpectation.boxes, Target.ofExpectation]

theorem ofExpectation_sizes (expectation : Fidelity.DocumentExpectation) :
    (ofExpectation expectation).sizes = expectation.sizes := by
  simp [ofExpectation, sizes, Fidelity.DocumentExpectation.sizes, Target.ofExpectation,
    Target.size, Fidelity.NodeExpectation.size, List.map_map]

theorem ofExpectation_selectorTexts (expectation : Fidelity.DocumentExpectation) :
    (ofExpectation expectation).selectorTexts =
      expectation.labels.map (fun className => "." ++ ClassName.render className) := by
  simp [ofExpectation, selectorTexts, Fidelity.DocumentExpectation.labels, Target.ofExpectation,
    Target.selectorText, Selector.text, List.map_map]

theorem ofExpectation_nodeCount (expectation : Fidelity.DocumentExpectation) :
    (ofExpectation expectation).nodeCount = expectation.nodeCount := by
  simp [ofExpectation, nodeCount, Fidelity.DocumentExpectation.nodeCount]

/-- Derive a typed browser-probe plan directly from a successful exact check. -/
def ofCheckedWithin {available : AvailableSpace} (checked : CheckedWithin available) : Plan :=
  ofExpectation (Fidelity.ofCheckedWithin checked)

theorem ofCheckedWithin_targetProfile {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).targetProfile = .exact1D_v1 := by
  simp [ofCheckedWithin]

theorem ofCheckedWithin_sourceGuarantee {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).sourceGuarantee = .exact := by
  simpa [ofCheckedWithin] using Fidelity.ofCheckedWithin_sourceGuarantee checked

theorem ofCheckedWithin_rootClassName {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).rootClassName = { serial := 0 } := by
  simpa [ofCheckedWithin] using Fidelity.ofCheckedWithin_rootClassName checked

theorem ofCheckedWithin_labels_eq_ruleClassNames {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).labels =
      (ExactDocument.ofArtifact (Artifact.ofCheckedWithin checked)).ruleClassNames := by
  calc
    (ofCheckedWithin checked).labels = (Fidelity.ofCheckedWithin checked).labels := by
      simpa [ofCheckedWithin] using ofExpectation_labels (Fidelity.ofCheckedWithin checked)
    _ = (ExactDocument.ofArtifact (Artifact.ofCheckedWithin checked)).ruleClassNames := by
      exact Fidelity.ofCheckedWithin_labels_eq_ruleClassNames checked

theorem ofCheckedWithin_labels_eq_classReferences {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).labels =
      (ExactDocument.ofArtifact (Artifact.ofCheckedWithin checked)).classReferences := by
  calc
    (ofCheckedWithin checked).labels = (Fidelity.ofCheckedWithin checked).labels := by
      simpa [ofCheckedWithin] using ofExpectation_labels (Fidelity.ofCheckedWithin checked)
    _ = (ExactDocument.ofArtifact (Artifact.ofCheckedWithin checked)).classReferences := by
      exact Fidelity.ofCheckedWithin_labels_eq_classReferences checked

theorem ofCheckedWithin_boxes_eq_expectation_boxes {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).boxes = (Fidelity.ofCheckedWithin checked).boxes := by
  simpa [ofCheckedWithin] using ofExpectation_boxes (Fidelity.ofCheckedWithin checked)

theorem ofCheckedWithin_styles_eq_expectation_styles {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).styles = (Fidelity.ofCheckedWithin checked).styles := by
  simpa [ofCheckedWithin] using ofExpectation_styles (Fidelity.ofCheckedWithin checked)

theorem ofCheckedWithin_nodeCount_eq_ruleCount {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).nodeCount =
      (ExactDocument.ofArtifact (Artifact.ofCheckedWithin checked)).stylesheet.rules.length := by
  calc
    (ofCheckedWithin checked).nodeCount = (Fidelity.ofCheckedWithin checked).nodeCount := by
      simpa [ofCheckedWithin] using ofExpectation_nodeCount (Fidelity.ofCheckedWithin checked)
    _ = (ExactDocument.ofArtifact (Artifact.ofCheckedWithin checked)).stylesheet.rules.length := by
      exact Fidelity.ofCheckedWithin_nodeCount_eq_ruleCount checked

theorem ofCheckedWithin_selectorTexts_length_eq_ruleCount {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).selectorTexts.length =
      (ExactDocument.ofArtifact (Artifact.ofCheckedWithin checked)).stylesheet.rules.length := by
  rw [selectorTexts_length, ofCheckedWithin_nodeCount_eq_ruleCount]

end Plan

end ProbePlan
end ExactDocument

namespace ExactProjection

def probePlan
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : ExactDocument.ProbePlan.Plan :=
  ExactDocument.ProbePlan.Plan.ofCheckedWithin projection.checked

theorem probePlan_targetProfile_exact1D_v1
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.probePlan.targetProfile = .exact1D_v1 := by
  show (ExactDocument.ProbePlan.Plan.ofCheckedWithin projection.checked).targetProfile = .exact1D_v1
  exact ExactDocument.ProbePlan.Plan.ofCheckedWithin_targetProfile projection.checked

theorem probePlan_sourceGuarantee_exact
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.probePlan.sourceGuarantee = .exact := by
  simpa [probePlan] using
    ExactDocument.ProbePlan.Plan.ofCheckedWithin_sourceGuarantee projection.checked

theorem probePlan_labels_eq_expectation_labels
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.probePlan.labels = projection.expectations.labels := by
  simpa [probePlan, expectations] using
    ExactDocument.ProbePlan.Plan.ofExpectation_labels projection.expectations

theorem probePlan_boxes_eq_expectation_boxes
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.probePlan.boxes = projection.expectations.boxes := by
  simpa [probePlan, expectations] using
    ExactDocument.ProbePlan.Plan.ofExpectation_boxes projection.expectations

theorem probePlan_nodeCount_eq_documentRuleCount
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.probePlan.nodeCount = projection.document.stylesheet.rules.length := by
  simpa [probePlan, document] using
    ExactDocument.ProbePlan.Plan.ofCheckedWithin_nodeCount_eq_ruleCount projection.checked

end ExactProjection

/-- Project a successful exact check straight to a typed browser-probe plan. -/
def checkWithinProbePlan (available : AvailableSpace) (layout : Layout) :
    CheckResult ExactDocument.ProbePlan.Plan :=
  (checkWithin available layout).map ExactDocument.ProbePlan.Plan.ofCheckedWithin

/-- Alias for `checkWithinProbePlan` at the public exact-check boundary. -/
def checkProbePlan (available : AvailableSpace) (layout : Layout) :
    CheckResult ExactDocument.ProbePlan.Plan :=
  checkWithinProbePlan available layout

end TypedLayout.Backend.ExactCss
