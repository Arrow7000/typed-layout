import TypedLayout.Backend.ExactCssManifest

namespace TypedLayout.Backend.ExactCss
namespace Interchange

open TypedLayout.Core
open TypedLayout.Backend.ExactCssFixtures
open TypedLayout.Backend.ExactCssManifest

/-- Harness-facing exact-fixture reference carrying the stable export-boundary
identifiers without performing any IO. -/
structure FixtureRef where
  fixtureId : FixtureId
  slug : String
  documentHtmlFile : String
  stylesheetCssFile : String
  standalonePageHtmlFile : String
  deriving DecidableEq, Repr

namespace FixtureRef

def ofFixtureId (fixtureId : FixtureId) : FixtureRef :=
  let names := fixtureId.exportNames
  { fixtureId := fixtureId
  , slug := names.slug
  , documentHtmlFile := names.documentHtmlFile
  , stylesheetCssFile := names.stylesheetCssFile
  , standalonePageHtmlFile := names.standalonePageHtmlFile
  }

def ofFixture (fixture : Fixture) : FixtureRef :=
  ofFixtureId fixture.id

def ofRenderedFixtureExport (entry : RenderedFixtureExport) : FixtureRef :=
  ofFixtureId entry.id

def fileNames (ref : FixtureRef) : List String :=
  [ ref.documentHtmlFile
  , ref.stylesheetCssFile
  , ref.standalonePageHtmlFile
  ]

theorem ofFixtureId_slug (fixtureId : FixtureId) :
    (ofFixtureId fixtureId).slug = fixtureId.slug :=
  rfl

theorem ofFixture_fixtureId (fixture : Fixture) :
    (ofFixture fixture).fixtureId = fixture.id :=
  rfl

theorem ofFixture_slug (fixture : Fixture) :
    (ofFixture fixture).slug = fixture.id.slug :=
  rfl

theorem ofRenderedFixtureExport_fixtureId (entry : RenderedFixtureExport) :
    (ofRenderedFixtureExport entry).fixtureId = entry.id :=
  rfl

theorem fileNames_length (ref : FixtureRef) :
    ref.fileNames.length = 3 := by
  rfl

theorem ofFixtureId_fileNames (fixtureId : FixtureId) :
    (ofFixtureId fixtureId).fileNames =
      [ fixtureId.exportNames.documentHtmlFile
      , fixtureId.exportNames.stylesheetCssFile
      , fixtureId.exportNames.standalonePageHtmlFile
      ] := by
  rfl

end FixtureRef

/-- Harness-facing handle for one lowered exact-fragment node.

The handle preserves the typed generated-class identity while also projecting the
stable text forms a future external harness will need. -/
structure TargetHandle where
  className : ExactDocument.ClassName
  classToken : String
  selectorText : String
  deriving DecidableEq, Repr

namespace TargetHandle

def ofClassName (className : ExactDocument.ClassName) : TargetHandle :=
  { className := className
  , classToken := ExactDocument.ClassName.render className
  , selectorText := "." ++ ExactDocument.ClassName.render className
  }

def ofSelector (selector : ExactDocument.ProbePlan.Selector) : TargetHandle :=
  ofClassName selector.className

def toSelector (handle : TargetHandle) : ExactDocument.ProbePlan.Selector :=
  .generatedClass handle.className

@[simp] theorem ofClassName_className (className : ExactDocument.ClassName) :
    (ofClassName className).className = className :=
  rfl

theorem ofClassName_classToken (className : ExactDocument.ClassName) :
    (ofClassName className).classToken = ExactDocument.ClassName.render className :=
  rfl

theorem ofClassName_selectorText (className : ExactDocument.ClassName) :
    (ofClassName className).selectorText = "." ++ ExactDocument.ClassName.render className :=
  rfl

@[simp] theorem toSelector_ofClassName (className : ExactDocument.ClassName) :
    (ofClassName className).toSelector = .generatedClass className :=
  rfl

@[simp] theorem ofSelector_className (selector : ExactDocument.ProbePlan.Selector) :
    (ofSelector selector).className = selector.className := by
  cases selector <;> rfl

@[simp] theorem toSelector_ofSelector (selector : ExactDocument.ProbePlan.Selector) :
    (ofSelector selector).toSelector = selector := by
  cases selector <;> rfl

end TargetHandle

/-- Harness-facing exact expected target.

This common boundary shape is shared by fidelity expectations and probe plans: a
typed node identity, source-semantic box, backend style, and source layout kind. -/
structure ExpectedTarget where
  handle : TargetHandle
  kind : LayoutKind
  backendStyle : Style
  sourceBox : Box
  deriving DecidableEq, Repr

namespace ExpectedTarget

def className (target : ExpectedTarget) : ExactDocument.ClassName :=
  target.handle.className

def selectorText (target : ExpectedTarget) : String :=
  target.handle.selectorText

def origin (target : ExpectedTarget) : Origin :=
  target.sourceBox.origin

def extent (target : ExpectedTarget) : ExactExtent :=
  target.sourceBox.extent

def size (target : ExpectedTarget) : Size :=
  target.backendStyle.size

def ofExpectation (expectation : ExactDocument.Fidelity.NodeExpectation) : ExpectedTarget :=
  { handle := TargetHandle.ofClassName expectation.className
  , kind := expectation.kind
  , backendStyle := expectation.style
  , sourceBox := expectation.box
  }

def toExpectation (target : ExpectedTarget) : ExactDocument.Fidelity.NodeExpectation :=
  { className := target.className
  , kind := target.kind
  , style := target.backendStyle
  , box := target.sourceBox
  }

def ofProbeTarget (target : ExactDocument.ProbePlan.Target) : ExpectedTarget :=
  { handle := TargetHandle.ofSelector target.selector
  , kind := target.kind
  , backendStyle := target.backendStyle
  , sourceBox := target.sourceBox
  }

def toProbeTarget (target : ExpectedTarget) : ExactDocument.ProbePlan.Target :=
  { selector := target.handle.toSelector
  , kind := target.kind
  , backendStyle := target.backendStyle
  , sourceBox := target.sourceBox
  }

theorem ofExpectation_className (expectation : ExactDocument.Fidelity.NodeExpectation) :
    (ofExpectation expectation).className = expectation.className :=
  rfl

theorem ofProbeTarget_className (target : ExactDocument.ProbePlan.Target) :
    (ofProbeTarget target).className = target.className :=
  rfl

@[simp] theorem toExpectation_ofExpectation
    (expectation : ExactDocument.Fidelity.NodeExpectation) :
    (ofExpectation expectation).toExpectation = expectation := by
  rfl

@[simp] theorem toProbeTarget_ofProbeTarget
    (target : ExactDocument.ProbePlan.Target) :
    (ofProbeTarget target).toProbeTarget = target := by
  cases target
  simp [ofProbeTarget, toProbeTarget]

theorem ofProbeTarget_ofExpectation
    (expectation : ExactDocument.Fidelity.NodeExpectation) :
    ofProbeTarget (ExactDocument.ProbePlan.Target.ofExpectation expectation) =
      ofExpectation expectation := by
  rfl

end ExpectedTarget

/-- Harness-facing exact expectation payload. -/
structure ExpectationPayload where
  targetProfile : BlessedCssProfile
  sourceGuarantee : GuaranteeClass
  root : ExpectedTarget
  targets : List ExpectedTarget
  deriving DecidableEq, Repr

namespace ExpectationPayload

private theorem expectedTarget_labels_ofExpectations
    (nodes : List ExactDocument.Fidelity.NodeExpectation) :
    (nodes.map ExpectedTarget.ofExpectation).map ExpectedTarget.className =
      nodes.map ExactDocument.Fidelity.NodeExpectation.className := by
  induction nodes with
  | nil =>
      rfl
  | cons node nodes ih =>
      cases node
      simp [ExpectedTarget.ofExpectation, ExpectedTarget.className, ih]

theorem expectedTarget_probeTargets_ofExpectations
    (nodes : List ExactDocument.Fidelity.NodeExpectation) :
    nodes.map (fun node => ExpectedTarget.ofProbeTarget (ExactDocument.ProbePlan.Target.ofExpectation node)) =
      nodes.map ExpectedTarget.ofExpectation := by
  induction nodes with
  | nil =>
      rfl
  | cons node nodes ih =>
      have hHead :
          ExpectedTarget.ofProbeTarget (ExactDocument.ProbePlan.Target.ofExpectation node) =
            ExpectedTarget.ofExpectation node := by
        cases node
        rfl
      simp [ih, hHead]

def nodeCount (payload : ExpectationPayload) : Nat :=
  payload.targets.length

def rootClassName (payload : ExpectationPayload) : ExactDocument.ClassName :=
  payload.root.className

def labels (payload : ExpectationPayload) : List ExactDocument.ClassName :=
  payload.targets.map ExpectedTarget.className

def selectorTexts (payload : ExpectationPayload) : List String :=
  payload.targets.map ExpectedTarget.selectorText

def kinds (payload : ExpectationPayload) : List LayoutKind :=
  payload.targets.map ExpectedTarget.kind

def styles (payload : ExpectationPayload) : List Style :=
  payload.targets.map ExpectedTarget.backendStyle

def boxes (payload : ExpectationPayload) : List Box :=
  payload.targets.map ExpectedTarget.sourceBox

def sizes (payload : ExpectationPayload) : List Size :=
  payload.targets.map ExpectedTarget.size

def ofExpectation (expectation : ExactDocument.Fidelity.DocumentExpectation) : ExpectationPayload :=
  { targetProfile := expectation.targetProfile
  , sourceGuarantee := expectation.sourceGuarantee
  , root := ExpectedTarget.ofExpectation expectation.root
  , targets := expectation.nodes.map ExpectedTarget.ofExpectation
  }

def ofCheckedWithin {available : AvailableSpace}
    (checked : CheckedWithin available) : ExpectationPayload :=
  ofExpectation (ExactDocument.Fidelity.ofCheckedWithin checked)

theorem labels_length (payload : ExpectationPayload) :
    payload.labels.length = payload.nodeCount := by
  simp [labels, nodeCount]

theorem selectorTexts_length (payload : ExpectationPayload) :
    payload.selectorTexts.length = payload.nodeCount := by
  simp [selectorTexts, nodeCount]

theorem boxes_length (payload : ExpectationPayload) :
    payload.boxes.length = payload.nodeCount := by
  simp [boxes, nodeCount]

theorem ofExpectation_rootClassName
    (expectation : ExactDocument.Fidelity.DocumentExpectation) :
    (ofExpectation expectation).rootClassName = expectation.rootClassName :=
  rfl

theorem ofExpectation_labels
    (expectation : ExactDocument.Fidelity.DocumentExpectation) :
    (ofExpectation expectation).labels = expectation.labels := by
  simpa [ofExpectation, labels, ExactDocument.Fidelity.DocumentExpectation.labels] using
    expectedTarget_labels_ofExpectations expectation.nodes

theorem ofExpectation_selectorTexts
    (expectation : ExactDocument.Fidelity.DocumentExpectation) :
    (ofExpectation expectation).selectorTexts =
      expectation.labels.map (fun className => "." ++ ExactDocument.ClassName.render className) := by
  simp [ofExpectation, selectorTexts, ExactDocument.Fidelity.DocumentExpectation.labels,
    ExpectedTarget.ofExpectation, ExpectedTarget.selectorText, TargetHandle.ofClassName,
    List.map_map]

theorem ofExpectation_boxes
    (expectation : ExactDocument.Fidelity.DocumentExpectation) :
    (ofExpectation expectation).boxes = expectation.boxes := by
  simp [ofExpectation, boxes, ExactDocument.Fidelity.DocumentExpectation.boxes,
    ExpectedTarget.ofExpectation]

theorem ofExpectation_styles
    (expectation : ExactDocument.Fidelity.DocumentExpectation) :
    (ofExpectation expectation).styles = expectation.styles := by
  simp [ofExpectation, styles, ExactDocument.Fidelity.DocumentExpectation.styles,
    ExpectedTarget.ofExpectation]

theorem ofExpectation_nodeCount
    (expectation : ExactDocument.Fidelity.DocumentExpectation) :
    (ofExpectation expectation).nodeCount = expectation.nodeCount := by
  simp [ofExpectation, nodeCount, ExactDocument.Fidelity.DocumentExpectation.nodeCount]

end ExpectationPayload

/-- Harness-facing exact probe-plan payload. -/
structure ProbePlanPayload where
  targetProfile : BlessedCssProfile
  sourceGuarantee : GuaranteeClass
  root : ExpectedTarget
  targets : List ExpectedTarget
  deriving DecidableEq, Repr

namespace ProbePlanPayload

private theorem expectedTarget_labels_ofProbeTargets
    (targets : List ExactDocument.ProbePlan.Target) :
    (targets.map ExpectedTarget.ofProbeTarget).map ExpectedTarget.className =
      targets.map ExactDocument.ProbePlan.Target.className := by
  induction targets with
  | nil =>
      rfl
  | cons target targets ih =>
      have hHead : (ExpectedTarget.ofProbeTarget target).className = target.className := by
        cases target
        simp [ExpectedTarget.ofProbeTarget, ExpectedTarget.className,
          ExactDocument.ProbePlan.Target.className]
      simp [ih, hHead]

private theorem expectedTarget_selectorTexts_ofProbeTargets
    (targets : List ExactDocument.ProbePlan.Target) :
    (targets.map ExpectedTarget.ofProbeTarget).map ExpectedTarget.selectorText =
      targets.map ExactDocument.ProbePlan.Target.selectorText := by
  induction targets with
  | nil =>
      rfl
  | cons target targets ih =>
      cases target with
      | mk selector kind backendStyle sourceBox =>
          cases selector with
          | generatedClass className =>
              simp [ExpectedTarget.ofProbeTarget, ExpectedTarget.selectorText,
                TargetHandle.ofSelector, TargetHandle.ofClassName,
                ExactDocument.ProbePlan.Selector.className,
                ExactDocument.ProbePlan.Target.selectorText,
                ExactDocument.ProbePlan.Selector.text, ih]

def nodeCount (payload : ProbePlanPayload) : Nat :=
  payload.targets.length

def rootClassName (payload : ProbePlanPayload) : ExactDocument.ClassName :=
  payload.root.className

def labels (payload : ProbePlanPayload) : List ExactDocument.ClassName :=
  payload.targets.map ExpectedTarget.className

def selectorTexts (payload : ProbePlanPayload) : List String :=
  payload.targets.map ExpectedTarget.selectorText

def boxes (payload : ProbePlanPayload) : List Box :=
  payload.targets.map ExpectedTarget.sourceBox

def styles (payload : ProbePlanPayload) : List Style :=
  payload.targets.map ExpectedTarget.backendStyle

def ofPlan (plan : ExactDocument.ProbePlan.Plan) : ProbePlanPayload :=
  { targetProfile := plan.targetProfile
  , sourceGuarantee := plan.sourceGuarantee
  , root := ExpectedTarget.ofProbeTarget plan.root
  , targets := plan.targets.map ExpectedTarget.ofProbeTarget
  }

def ofCheckedWithin {available : AvailableSpace}
    (checked : CheckedWithin available) : ProbePlanPayload :=
  ofPlan (ExactDocument.ProbePlan.Plan.ofCheckedWithin checked)

theorem labels_length (payload : ProbePlanPayload) :
    payload.labels.length = payload.nodeCount := by
  simp [labels, nodeCount]

theorem selectorTexts_length (payload : ProbePlanPayload) :
    payload.selectorTexts.length = payload.nodeCount := by
  simp [selectorTexts, nodeCount]

theorem ofPlan_rootClassName (plan : ExactDocument.ProbePlan.Plan) :
    (ofPlan plan).rootClassName = plan.rootClassName :=
  rfl

theorem ofPlan_labels (plan : ExactDocument.ProbePlan.Plan) :
    (ofPlan plan).labels = plan.labels := by
  simpa [ofPlan, labels, ExactDocument.ProbePlan.Plan.labels] using
    expectedTarget_labels_ofProbeTargets plan.targets

theorem ofPlan_selectorTexts (plan : ExactDocument.ProbePlan.Plan) :
    (ofPlan plan).selectorTexts = plan.selectorTexts := by
  simpa [ofPlan, selectorTexts, ExactDocument.ProbePlan.Plan.selectorTexts] using
    expectedTarget_selectorTexts_ofProbeTargets plan.targets

theorem ofPlan_boxes (plan : ExactDocument.ProbePlan.Plan) :
    (ofPlan plan).boxes = plan.boxes := by
  simp [ofPlan, boxes, ExactDocument.ProbePlan.Plan.boxes, ExpectedTarget.ofProbeTarget]

theorem ofPlan_styles (plan : ExactDocument.ProbePlan.Plan) :
    (ofPlan plan).styles = plan.styles := by
  simp [ofPlan, styles, ExactDocument.ProbePlan.Plan.styles, ExpectedTarget.ofProbeTarget]

theorem ofPlan_nodeCount (plan : ExactDocument.ProbePlan.Plan) :
    (ofPlan plan).nodeCount = plan.nodeCount := by
  simp [ofPlan, nodeCount, ExactDocument.ProbePlan.Plan.nodeCount]

theorem ofExpectation_targets
    (expectation : ExactDocument.Fidelity.DocumentExpectation) :
    (ofPlan (ExactDocument.ProbePlan.Plan.ofExpectation expectation)).targets =
      (ExpectationPayload.ofExpectation expectation).targets := by
  simpa [ofPlan, ExpectationPayload.ofExpectation, ExactDocument.ProbePlan.Plan.ofExpectation] using
    ExpectationPayload.expectedTarget_probeTargets_ofExpectations expectation.nodes

theorem ofExpectation_labels
    (expectation : ExactDocument.Fidelity.DocumentExpectation) :
    (ofPlan (ExactDocument.ProbePlan.Plan.ofExpectation expectation)).labels =
      (ExpectationPayload.ofExpectation expectation).labels := by
  simp [ofExpectation_targets, labels, ExpectationPayload.labels]

theorem ofExpectation_nodeCount
    (expectation : ExactDocument.Fidelity.DocumentExpectation) :
    (ofPlan (ExactDocument.ProbePlan.Plan.ofExpectation expectation)).nodeCount =
      (ExpectationPayload.ofExpectation expectation).nodeCount := by
  simp [ofExpectation_targets, nodeCount, ExpectationPayload.nodeCount]

end ProbePlanPayload

/-- Harness-facing exact observed target. -/
structure ObservedTarget where
  handle : TargetHandle
  box : ExactDocument.ProbeObservation.ObservedBox
  style : ExactDocument.ProbeObservation.ObservedStyle
  deriving DecidableEq, Repr

namespace ObservedTarget

def className (target : ObservedTarget) : ExactDocument.ClassName :=
  target.handle.className

def selectorText (target : ObservedTarget) : String :=
  target.handle.selectorText

def origin (target : ObservedTarget) : Origin :=
  target.box.origin

def extent (target : ObservedTarget) : ExactExtent :=
  target.box.extent

def size (target : ObservedTarget) : Size :=
  target.style.size

def sourceBox (target : ObservedTarget) : Box :=
  target.box.toSourceBox

def backendStyle (target : ObservedTarget) : Style :=
  target.style.toBackendStyle

def ofObservationTarget (target : ExactDocument.ProbeObservation.Target) : ObservedTarget :=
  { handle := TargetHandle.ofSelector target.selector
  , box := target.box
  , style := target.style
  }

def toObservationTarget (target : ObservedTarget) : ExactDocument.ProbeObservation.Target :=
  { selector := target.handle.toSelector
  , box := target.box
  , style := target.style
  }

def ofProbeTarget (target : ExactDocument.ProbePlan.Target) : ObservedTarget :=
  ofObservationTarget (ExactDocument.ProbeObservation.Target.ofProbeTarget target)

@[simp] theorem toObservationTarget_ofObservationTarget
    (target : ExactDocument.ProbeObservation.Target) :
    (ofObservationTarget target).toObservationTarget = target := by
  cases target
  simp [ofObservationTarget, toObservationTarget]

@[simp] theorem sourceBox_ofProbeTarget (target : ExactDocument.ProbePlan.Target) :
    (ofProbeTarget target).sourceBox = target.sourceBox := by
  simp [ofProbeTarget, ofObservationTarget, sourceBox]

@[simp] theorem backendStyle_ofProbeTarget (target : ExactDocument.ProbePlan.Target) :
    (ofProbeTarget target).backendStyle = target.backendStyle := by
  simp [ofProbeTarget, ofObservationTarget, backendStyle]

end ObservedTarget

/-- Harness-facing exact observation payload. -/
structure ObservationPayload where
  targets : List ObservedTarget
  deriving DecidableEq, Repr

namespace ObservationPayload

private theorem observedTarget_labels_ofTargets
    (targets : List ExactDocument.ProbeObservation.Target) :
    (targets.map ObservedTarget.ofObservationTarget).map ObservedTarget.className =
      targets.map ExactDocument.ProbeObservation.Target.className := by
  induction targets with
  | nil =>
      rfl
  | cons target targets ih =>
      have hHead : (ObservedTarget.ofObservationTarget target).className = target.className := by
        cases target
        simp [ObservedTarget.ofObservationTarget, ObservedTarget.className,
          ExactDocument.ProbeObservation.Target.className]
      simp [ih, hHead]

private theorem observedTarget_sourceBoxes_ofTargets
    (targets : List ExactDocument.ProbeObservation.Target) :
    (targets.map ObservedTarget.ofObservationTarget).map ObservedTarget.sourceBox =
      targets.map ExactDocument.ProbeObservation.Target.sourceBox := by
  induction targets with
  | nil =>
      rfl
  | cons target targets ih =>
      have hHead : (ObservedTarget.ofObservationTarget target).sourceBox = target.sourceBox := by
        cases target
        simp [ObservedTarget.ofObservationTarget, ObservedTarget.sourceBox,
          ExactDocument.ProbeObservation.Target.sourceBox]
      simp [ih, hHead]

private theorem observedTarget_backendStyles_ofTargets
    (targets : List ExactDocument.ProbeObservation.Target) :
    (targets.map ObservedTarget.ofObservationTarget).map ObservedTarget.backendStyle =
      targets.map ExactDocument.ProbeObservation.Target.backendStyle := by
  induction targets with
  | nil =>
      rfl
  | cons target targets ih =>
      have hHead : (ObservedTarget.ofObservationTarget target).backendStyle = target.backendStyle := by
        cases target
        simp [ObservedTarget.ofObservationTarget, ObservedTarget.backendStyle,
          ExactDocument.ProbeObservation.Target.backendStyle]
      simp [ih, hHead]

def nodeCount (payload : ObservationPayload) : Nat :=
  payload.targets.length

def labels (payload : ObservationPayload) : List ExactDocument.ClassName :=
  payload.targets.map ObservedTarget.className

def selectorTexts (payload : ObservationPayload) : List String :=
  payload.targets.map ObservedTarget.selectorText

def sourceBoxes (payload : ObservationPayload) : List Box :=
  payload.targets.map ObservedTarget.sourceBox

def backendStyles (payload : ObservationPayload) : List Style :=
  payload.targets.map ObservedTarget.backendStyle

def sizes (payload : ObservationPayload) : List Size :=
  payload.targets.map ObservedTarget.size

def ofObservation (document : ExactDocument.ProbeObservation.Document) : ObservationPayload :=
  { targets := document.targets.map ObservedTarget.ofObservationTarget }

def ofPlan (plan : ExactDocument.ProbePlan.Plan) : ObservationPayload :=
  ofObservation (ExactDocument.ProbeObservation.Document.ofPlan plan)

theorem labels_length (payload : ObservationPayload) :
    payload.labels.length = payload.nodeCount := by
  simp [labels, nodeCount]

theorem selectorTexts_length (payload : ObservationPayload) :
    payload.selectorTexts.length = payload.nodeCount := by
  simp [selectorTexts, nodeCount]

theorem ofObservation_labels (document : ExactDocument.ProbeObservation.Document) :
    (ofObservation document).labels = document.labels := by
  simpa [ofObservation, labels, ExactDocument.ProbeObservation.Document.labels] using
    observedTarget_labels_ofTargets document.targets

theorem ofObservation_sourceBoxes (document : ExactDocument.ProbeObservation.Document) :
    (ofObservation document).sourceBoxes = document.sourceBoxes := by
  simpa [ofObservation, sourceBoxes, ExactDocument.ProbeObservation.Document.sourceBoxes] using
    observedTarget_sourceBoxes_ofTargets document.targets

theorem ofObservation_backendStyles (document : ExactDocument.ProbeObservation.Document) :
    (ofObservation document).backendStyles = document.backendStyles := by
  simpa [ofObservation, backendStyles, ExactDocument.ProbeObservation.Document.backendStyles] using
    observedTarget_backendStyles_ofTargets document.targets

theorem ofObservation_nodeCount (document : ExactDocument.ProbeObservation.Document) :
    (ofObservation document).nodeCount = document.nodeCount := by
  simp [ofObservation, nodeCount, ExactDocument.ProbeObservation.Document.nodeCount]

theorem ofPlan_labels (plan : ExactDocument.ProbePlan.Plan) :
    (ofPlan plan).labels = plan.labels := by
  calc
    (ofPlan plan).labels = (ExactDocument.ProbeObservation.Document.ofPlan plan).labels := by
      simpa [ofPlan] using ofObservation_labels (ExactDocument.ProbeObservation.Document.ofPlan plan)
    _ = plan.labels := by
      exact ExactDocument.ProbeObservation.Document.ofPlan_labels plan

theorem ofPlan_sourceBoxes (plan : ExactDocument.ProbePlan.Plan) :
    (ofPlan plan).sourceBoxes = plan.boxes := by
  calc
    (ofPlan plan).sourceBoxes = (ExactDocument.ProbeObservation.Document.ofPlan plan).sourceBoxes := by
      simpa [ofPlan] using
        ofObservation_sourceBoxes (ExactDocument.ProbeObservation.Document.ofPlan plan)
    _ = plan.boxes := by
      exact ExactDocument.ProbeObservation.Document.ofPlan_sourceBoxes plan

theorem ofPlan_backendStyles (plan : ExactDocument.ProbePlan.Plan) :
    (ofPlan plan).backendStyles = plan.styles := by
  calc
    (ofPlan plan).backendStyles =
        (ExactDocument.ProbeObservation.Document.ofPlan plan).backendStyles := by
      simpa [ofPlan] using
        ofObservation_backendStyles (ExactDocument.ProbeObservation.Document.ofPlan plan)
    _ = plan.styles := by
      exact ExactDocument.ProbeObservation.Document.ofPlan_backendStyles plan

theorem ofPlan_nodeCount (plan : ExactDocument.ProbePlan.Plan) :
    (ofPlan plan).nodeCount = plan.nodeCount := by
  calc
    (ofPlan plan).nodeCount = (ExactDocument.ProbeObservation.Document.ofPlan plan).nodeCount := by
      simpa [ofPlan] using ofObservation_nodeCount (ExactDocument.ProbeObservation.Document.ofPlan plan)
    _ = plan.nodeCount := by
      exact ExactDocument.ProbeObservation.Document.ofPlan_nodeCount plan

end ObservationPayload

/-- Harness-facing exact comparison for one field. -/
inductive FieldComparison (α : Type u) where
  | same
  | different (expected : α) (observed : α)
  deriving DecidableEq, Repr

namespace FieldComparison

def isMatch : FieldComparison α → Bool
  | .same => true
  | .different _ _ => false

def ofValueComparison : ExactDocument.ProbeComparison.ValueComparison α → FieldComparison α
  | .same => .same
  | .different expected observed => .different expected observed

@[simp] theorem ofValueComparison_isMatch
    (comparison : ExactDocument.ProbeComparison.ValueComparison α) :
    (ofValueComparison comparison).isMatch = comparison.isMatch := by
  cases comparison <;> rfl

end FieldComparison

/-- Harness-facing exact box comparison. -/
structure BoxComparison where
  origin : FieldComparison Origin
  extent : FieldComparison ExactExtent
  deriving DecidableEq, Repr

namespace BoxComparison

def isMatch (comparison : BoxComparison) : Bool :=
  comparison.origin.isMatch && comparison.extent.isMatch

def ofComparison (comparison : ExactDocument.ProbeComparison.BoxComparison) : BoxComparison :=
  { origin := FieldComparison.ofValueComparison comparison.origin
  , extent := FieldComparison.ofValueComparison comparison.extent
  }

theorem ofComparison_isMatch (comparison : ExactDocument.ProbeComparison.BoxComparison) :
    (ofComparison comparison).isMatch = comparison.isMatch := by
  cases comparison
  simp [ofComparison, isMatch, ExactDocument.ProbeComparison.BoxComparison.isMatch,
    FieldComparison.ofValueComparison_isMatch]

end BoxComparison

/-- Harness-facing exact style comparison. -/
structure StyleComparison where
  boxSizing : FieldComparison BoxSizing
  size : FieldComparison Size
  padding : FieldComparison Padding
  display : FieldComparison Display
  flexItem : FieldComparison FlexItem
  deriving DecidableEq, Repr

namespace StyleComparison

def isMatch (comparison : StyleComparison) : Bool :=
  comparison.boxSizing.isMatch &&
    comparison.size.isMatch &&
    comparison.padding.isMatch &&
    comparison.display.isMatch &&
    comparison.flexItem.isMatch

def ofComparison (comparison : ExactDocument.ProbeComparison.StyleComparison) : StyleComparison :=
  { boxSizing := FieldComparison.ofValueComparison comparison.boxSizing
  , size := FieldComparison.ofValueComparison comparison.size
  , padding := FieldComparison.ofValueComparison comparison.padding
  , display := FieldComparison.ofValueComparison comparison.display
  , flexItem := FieldComparison.ofValueComparison comparison.flexItem
  }

theorem ofComparison_isMatch (comparison : ExactDocument.ProbeComparison.StyleComparison) :
    (ofComparison comparison).isMatch = comparison.isMatch := by
  cases comparison
  simp [ofComparison, isMatch, ExactDocument.ProbeComparison.StyleComparison.isMatch,
    FieldComparison.ofValueComparison_isMatch]

end StyleComparison

/-- Harness-facing exact target comparison. -/
structure TargetComparison where
  expected : ExpectedTarget
  observed : ObservedTarget
  selector : FieldComparison ExactDocument.ProbePlan.Selector
  box : BoxComparison
  style : StyleComparison
  deriving DecidableEq, Repr

namespace TargetComparison

def isMatch (comparison : TargetComparison) : Bool :=
  comparison.selector.isMatch && comparison.box.isMatch && comparison.style.isMatch

def ofComparison (comparison : ExactDocument.ProbeComparison.TargetComparison) : TargetComparison :=
  { expected := ExpectedTarget.ofProbeTarget comparison.expected
  , observed := ObservedTarget.ofObservationTarget comparison.observed
  , selector := FieldComparison.ofValueComparison comparison.selector
  , box := BoxComparison.ofComparison comparison.box
  , style := StyleComparison.ofComparison comparison.style
  }

theorem ofComparison_isMatch (comparison : ExactDocument.ProbeComparison.TargetComparison) :
    (ofComparison comparison).isMatch = comparison.isMatch := by
  cases comparison
  simp [ofComparison, isMatch, ExactDocument.ProbeComparison.TargetComparison.isMatch,
    FieldComparison.ofValueComparison_isMatch, BoxComparison.ofComparison_isMatch,
    StyleComparison.ofComparison_isMatch]

end TargetComparison

/-- Harness-facing exact target-result payload. -/
inductive TargetResult where
  | paired (comparison : TargetComparison)
  | missingObservation (expected : ExpectedTarget)
  | unexpectedObservation (observed : ObservedTarget)
  deriving DecidableEq, Repr

namespace TargetResult

def isMatch : TargetResult → Bool
  | .paired comparison => comparison.isMatch
  | .missingObservation _ => false
  | .unexpectedObservation _ => false

def ofResult : ExactDocument.ProbeComparison.TargetResult → TargetResult
  | .paired comparison => .paired (TargetComparison.ofComparison comparison)
  | .missingObservation expected => .missingObservation (ExpectedTarget.ofProbeTarget expected)
  | .unexpectedObservation observed => .unexpectedObservation (ObservedTarget.ofObservationTarget observed)

@[simp] theorem ofResult_isMatch (result : ExactDocument.ProbeComparison.TargetResult) :
    (ofResult result).isMatch = result.isMatch := by
  cases result <;> simp [ofResult, isMatch, ExactDocument.ProbeComparison.TargetResult.isMatch,
    TargetComparison.ofComparison_isMatch]

end TargetResult

/-- Harness-facing exact comparison payload. -/
structure ComparisonPayload where
  targetProfile : BlessedCssProfile
  sourceGuarantee : GuaranteeClass
  expectedCount : Nat
  observedCount : Nat
  results : List TargetResult
  deriving DecidableEq, Repr

namespace ComparisonPayload

private theorem results_allTargetsMatch
    (results : List ExactDocument.ProbeComparison.TargetResult) :
    (results.map TargetResult.ofResult).all TargetResult.isMatch =
      results.all ExactDocument.ProbeComparison.TargetResult.isMatch := by
  induction results with
  | nil =>
      rfl
  | cons result results ih =>
      simp [TargetResult.ofResult_isMatch, ih]

def resultCount (payload : ComparisonPayload) : Nat :=
  payload.results.length

def targetCountMatches (payload : ComparisonPayload) : Bool :=
  decide (payload.expectedCount = payload.observedCount)

def allTargetsMatch (payload : ComparisonPayload) : Bool :=
  payload.results.all TargetResult.isMatch

def matchesExactly (payload : ComparisonPayload) : Bool :=
  payload.targetCountMatches && payload.allTargetsMatch

def ofComparison (comparison : ExactDocument.ProbeComparison.DocumentComparison) : ComparisonPayload :=
  { targetProfile := comparison.targetProfile
  , sourceGuarantee := comparison.sourceGuarantee
  , expectedCount := comparison.expectedCount
  , observedCount := comparison.observedCount
  , results := comparison.results.map TargetResult.ofResult
  }

def ofPlan (plan : ExactDocument.ProbePlan.Plan) : ComparisonPayload :=
  ofComparison <|
    ExactDocument.ProbeComparison.DocumentComparison.compare
      plan (ExactDocument.ProbeObservation.Document.ofPlan plan)

theorem ofComparison_resultCount
    (comparison : ExactDocument.ProbeComparison.DocumentComparison) :
    (ofComparison comparison).resultCount = comparison.resultCount := by
  simp [ofComparison, resultCount, ExactDocument.ProbeComparison.DocumentComparison.resultCount]

theorem ofComparison_targetCountMatches
    (comparison : ExactDocument.ProbeComparison.DocumentComparison) :
    (ofComparison comparison).targetCountMatches = comparison.targetCountMatches :=
  rfl

theorem ofComparison_allTargetsMatch
    (comparison : ExactDocument.ProbeComparison.DocumentComparison) :
    (ofComparison comparison).allTargetsMatch = comparison.allTargetsMatch := by
  simpa [ofComparison, allTargetsMatch, ExactDocument.ProbeComparison.DocumentComparison.allTargetsMatch]
    using results_allTargetsMatch comparison.results

theorem ofComparison_matchesExactly
    (comparison : ExactDocument.ProbeComparison.DocumentComparison) :
    (ofComparison comparison).matchesExactly = comparison.matchesExactly := by
  simp [matchesExactly, ExactDocument.ProbeComparison.DocumentComparison.matchesExactly,
    ofComparison_targetCountMatches, ofComparison_allTargetsMatch]

theorem ofPlan_matchesExactly (plan : ExactDocument.ProbePlan.Plan) :
    (ofPlan plan).matchesExactly = true := by
  calc
    (ofPlan plan).matchesExactly =
        (ExactDocument.ProbeComparison.DocumentComparison.compare
          plan (ExactDocument.ProbeObservation.Document.ofPlan plan)).matchesExactly := by
      exact ofComparison_matchesExactly _
    _ = true := by
      exact ExactDocument.ProbeComparison.DocumentComparison.compare_ofPlan_matchesExactly plan

end ComparisonPayload

/-- Harness-facing bundle for one canonical exact fixture. -/
structure Bundle where
  fixture : FixtureRef
  expectations : ExpectationPayload
  probePlan : ProbePlanPayload
  observation : ObservationPayload
  comparison : ComparisonPayload
  deriving DecidableEq, Repr

namespace Bundle

def ofFixture (fixture : Fixture) : Bundle :=
  { fixture := FixtureRef.ofFixture fixture
  , expectations := ExpectationPayload.ofExpectation fixture.expectations
  , probePlan := ProbePlanPayload.ofPlan fixture.probePlan
  , observation := ObservationPayload.ofObservation fixture.observation
  , comparison := ComparisonPayload.ofComparison fixture.comparison
  }

theorem ofFixture_fixtureId (fixture : Fixture) :
    (ofFixture fixture).fixture.fixtureId = fixture.id := by
  rfl

theorem ofFixture_slug (fixture : Fixture) :
    (ofFixture fixture).fixture.slug = fixture.id.slug := by
  rfl

theorem ofFixture_expectationLabels_eq_probePlanLabels (fixture : Fixture) :
    (ofFixture fixture).expectations.labels = (ofFixture fixture).probePlan.labels := by
  calc
    (ofFixture fixture).expectations.labels = fixture.expectations.labels := by
      simpa [ofFixture] using ExpectationPayload.ofExpectation_labels fixture.expectations
    _ = fixture.probePlan.labels := by
      symm
      exact Fixture.probePlan_labels_eq_expectation_labels fixture
    _ = (ofFixture fixture).probePlan.labels := by
      symm
      simpa [ofFixture] using ProbePlanPayload.ofPlan_labels fixture.probePlan

theorem ofFixture_probePlanNodeCount_eq_expectationNodeCount (fixture : Fixture) :
    (ofFixture fixture).probePlan.nodeCount = (ofFixture fixture).expectations.nodeCount := by
  calc
    (ofFixture fixture).probePlan.nodeCount = fixture.probePlan.nodeCount := by
      simpa [ofFixture] using ProbePlanPayload.ofPlan_nodeCount fixture.probePlan
    _ = fixture.document.stylesheet.rules.length := by
      exact Fixture.probePlan_nodeCount_eq_documentRuleCount fixture
    _ = fixture.expectations.nodeCount := by
      symm
      exact Fixture.expectation_nodeCount_eq_documentRuleCount fixture
    _ = (ofFixture fixture).expectations.nodeCount := by
      symm
      simpa [ofFixture] using ExpectationPayload.ofExpectation_nodeCount fixture.expectations

theorem ofFixture_observationLabels_eq_probePlanLabels (fixture : Fixture) :
    (ofFixture fixture).observation.labels = (ofFixture fixture).probePlan.labels := by
  calc
    (ofFixture fixture).observation.labels = fixture.observation.labels := by
      simpa [ofFixture] using ObservationPayload.ofObservation_labels fixture.observation
    _ = fixture.probePlan.labels := by
      exact Fixture.observation_labels_eq_probePlan_labels fixture
    _ = (ofFixture fixture).probePlan.labels := by
      symm
      simpa [ofFixture] using ProbePlanPayload.ofPlan_labels fixture.probePlan

theorem ofFixture_comparison_matchesExactly (fixture : Fixture) :
    (ofFixture fixture).comparison.matchesExactly = true := by
  calc
    (ofFixture fixture).comparison.matchesExactly = fixture.comparison.matchesExactly := by
      simpa [ofFixture] using ComparisonPayload.ofComparison_matchesExactly fixture.comparison
    _ = true := by
      exact Fixture.comparison_matchesExactly fixture

theorem ofFixture_fileNames_length (fixture : Fixture) :
    (ofFixture fixture).fixture.fileNames.length = 3 := by
  simp [ofFixture, FixtureRef.fileNames_length]

end Bundle

def exactRowBundle : Bundle :=
  Bundle.ofFixture exactRowFixture

theorem exactRowBundle_labelSerials :
    ExactDocument.ClassName.serials exactRowBundle.probePlan.labels = [0, 1, 2, 3] := by
  calc
    ExactDocument.ClassName.serials exactRowBundle.probePlan.labels =
        ExactDocument.ClassName.serials exactRowFixture.probePlan.labels := by
      simp [exactRowBundle, Bundle.ofFixture, ProbePlanPayload.ofPlan_labels]
    _ = [0, 1, 2, 3] := by
      exact exactRowFixture_probePlanLabelSerials

theorem exactRowBundle_matchesExactly :
    exactRowBundle.comparison.matchesExactly = true := by
  simpa [exactRowBundle] using Bundle.ofFixture_comparison_matchesExactly exactRowFixture

def exactRowShiftedComparisonPayload : ComparisonPayload :=
  ComparisonPayload.ofComparison exactRowShiftedComparison

theorem exactRowShiftedComparisonPayload_matchesExactly :
    exactRowShiftedComparisonPayload.matchesExactly = false := by
  calc
    exactRowShiftedComparisonPayload.matchesExactly = exactRowShiftedComparison.matchesExactly := by
      simpa [exactRowShiftedComparisonPayload] using
        ComparisonPayload.ofComparison_matchesExactly exactRowShiftedComparison
    _ = false := by
      exact exactRowShiftedComparison_matchesExactly

end Interchange
end TypedLayout.Backend.ExactCss
