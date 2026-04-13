import TypedLayout.Backend.ExactCssHarnessProtocol

namespace TypedLayout.Backend.ExactCssBrowserTaskPlan

open TypedLayout.Core
open TypedLayout.Backend.ExactCss
open TypedLayout.Backend.ExactCssFixtures
open TypedLayout.Backend.ExactCssHarnessCase
open TypedLayout.Backend.ExactCssHarnessProtocol
open TypedLayout.Backend.ExactCss.Interchange

/-- Selected exact-fragment style field a future browser runner should read. -/
inductive StyleField where
  | boxSizing
  | size
  | padding
  | display
  | flexItem
  deriving DecidableEq, Repr

/-- Typed exact-fragment observation slice for one probe target.

The future runner should always collect the target's bounding box; this plan only
needs to name which typed style fields accompany that box observation. -/
structure ObservationPlan where
  styleFields : List StyleField
  deriving DecidableEq, Repr

namespace ObservationPlan

def exact1D : ObservationPlan :=
  { styleFields := [ .boxSizing, .size, .padding, .display, .flexItem ] }

def styleFieldCount (plan : ObservationPlan) : Nat :=
  plan.styleFields.length

theorem exact1D_styleFieldCount :
    exact1D.styleFieldCount = 5 := by
  native_decide

end ObservationPlan

/-- Task telling a future runner to load one rendered exact page. -/
structure LoadPageTask where
  renderedPage : ExactDocument.RenderedPage
  deriving DecidableEq, Repr

namespace LoadPageTask

def ofRequest (request : Request) : LoadPageTask :=
  { renderedPage := request.renderedPage }

@[simp] theorem ofRequest_renderedPage (request : Request) :
    (ofRequest request).renderedPage = request.renderedPage :=
  rfl

end LoadPageTask

/-- Ordered exact-fragment probe task for one generated selector.

The task carries the expected typed target and the typed observation slice the
future runner should collect for it. -/
structure ProbeTask where
  order : Nat
  target : ExpectedTarget
  observation : ObservationPlan
  deriving DecidableEq, Repr

namespace ProbeTask

def className (task : ProbeTask) : ExactDocument.ClassName :=
  task.target.className

def selector (task : ProbeTask) : ExactDocument.ProbePlan.Selector :=
  task.target.handle.toSelector

def selectorText (task : ProbeTask) : String :=
  task.target.selectorText

def kind (task : ProbeTask) : LayoutKind :=
  task.target.kind

def expectedBox (task : ProbeTask) : Box :=
  task.target.sourceBox

def expectedStyle (task : ProbeTask) : Style :=
  task.target.backendStyle

def ofExpectedTarget (order : Nat) (target : ExpectedTarget) : ProbeTask :=
  { order := order
  , target := target
  , observation := ObservationPlan.exact1D
  }

def ofTargetsFrom : Nat → List ExpectedTarget → List ProbeTask
  | _, [] => []
  | order, target :: targets =>
      ofExpectedTarget order target :: ofTargetsFrom (order + 1) targets

def ofTargets (targets : List ExpectedTarget) : List ProbeTask :=
  ofTargetsFrom 0 targets

@[simp] theorem ofExpectedTarget_className (order : Nat) (target : ExpectedTarget) :
    (ofExpectedTarget order target).className = target.className :=
  rfl

@[simp] theorem ofExpectedTarget_selector (order : Nat) (target : ExpectedTarget) :
    (ofExpectedTarget order target).selector = target.handle.toSelector :=
  rfl

@[simp] theorem ofExpectedTarget_selectorText (order : Nat) (target : ExpectedTarget) :
    (ofExpectedTarget order target).selectorText = target.selectorText :=
  rfl

@[simp] theorem ofExpectedTarget_expectedBox (order : Nat) (target : ExpectedTarget) :
    (ofExpectedTarget order target).expectedBox = target.sourceBox :=
  rfl

@[simp] theorem ofExpectedTarget_expectedStyle (order : Nat) (target : ExpectedTarget) :
    (ofExpectedTarget order target).expectedStyle = target.backendStyle :=
  rfl

theorem ofTargetsFrom_length (order : Nat) (targets : List ExpectedTarget) :
    (ofTargetsFrom order targets).length = targets.length := by
  induction targets generalizing order with
  | nil =>
      rfl
  | cons target targets ih =>
      simp [ofTargetsFrom, ih]

theorem ofTargets_length (targets : List ExpectedTarget) :
    (ofTargets targets).length = targets.length := by
  simpa [ofTargets] using ofTargetsFrom_length 0 targets

theorem ofTargetsFrom_classNames (order : Nat) (targets : List ExpectedTarget) :
    (ofTargetsFrom order targets).map className = targets.map ExpectedTarget.className := by
  induction targets generalizing order with
  | nil =>
      rfl
  | cons target targets ih =>
      simp [ofTargetsFrom, className, ofExpectedTarget, ih]

theorem ofTargets_classNames (targets : List ExpectedTarget) :
    (ofTargets targets).map className = targets.map ExpectedTarget.className := by
  simpa [ofTargets] using ofTargetsFrom_classNames 0 targets

theorem ofTargetsFrom_selectors (order : Nat) (targets : List ExpectedTarget) :
    (ofTargetsFrom order targets).map selector =
      targets.map (fun target => target.handle.toSelector) := by
  induction targets generalizing order with
  | nil =>
      rfl
  | cons target targets ih =>
      simp [ofTargetsFrom, selector, ofExpectedTarget, ih]

theorem ofTargets_selectors (targets : List ExpectedTarget) :
    (ofTargets targets).map selector =
      targets.map (fun target => target.handle.toSelector) := by
  simpa [ofTargets] using ofTargetsFrom_selectors 0 targets

theorem ofTargetsFrom_selectorTexts (order : Nat) (targets : List ExpectedTarget) :
    (ofTargetsFrom order targets).map selectorText =
      targets.map ExpectedTarget.selectorText := by
  induction targets generalizing order with
  | nil =>
      rfl
  | cons target targets ih =>
      simp [ofTargetsFrom, selectorText, ofExpectedTarget, ih]

theorem ofTargets_selectorTexts (targets : List ExpectedTarget) :
    (ofTargets targets).map selectorText = targets.map ExpectedTarget.selectorText := by
  simpa [ofTargets] using ofTargetsFrom_selectorTexts 0 targets

theorem ofTargetsFrom_expectedBoxes (order : Nat) (targets : List ExpectedTarget) :
    (ofTargetsFrom order targets).map expectedBox = targets.map ExpectedTarget.sourceBox := by
  induction targets generalizing order with
  | nil =>
      rfl
  | cons target targets ih =>
      simp [ofTargetsFrom, expectedBox, ofExpectedTarget, ih]

theorem ofTargets_expectedBoxes (targets : List ExpectedTarget) :
    (ofTargets targets).map expectedBox = targets.map ExpectedTarget.sourceBox := by
  simpa [ofTargets] using ofTargetsFrom_expectedBoxes 0 targets

theorem ofTargetsFrom_expectedStyles (order : Nat) (targets : List ExpectedTarget) :
    (ofTargetsFrom order targets).map expectedStyle =
      targets.map ExpectedTarget.backendStyle := by
  induction targets generalizing order with
  | nil =>
      rfl
  | cons target targets ih =>
      simp [ofTargetsFrom, expectedStyle, ofExpectedTarget, ih]

theorem ofTargets_expectedStyles (targets : List ExpectedTarget) :
    (ofTargets targets).map expectedStyle = targets.map ExpectedTarget.backendStyle := by
  simpa [ofTargets] using ofTargetsFrom_expectedStyles 0 targets

end ProbeTask

/-- Browser-facing exact-fragment task node. -/
inductive Task where
  | loadPage (task : LoadPageTask)
  | probe (task : ProbeTask)
  deriving DecidableEq, Repr

/-- Typed browser task plan derived from one exact harness request.

The plan is still pure: it names the rendered page a future runner should load,
the ordered generated selectors it should probe, and the exact typed observation
slice it should collect for each target. -/
structure Plan where
  fixture : FixtureRef
  targetProfile : BlessedCssProfile
  sourceGuarantee : GuaranteeClass
  loadPage : LoadPageTask
  probes : List ProbeTask
  deriving DecidableEq, Repr

namespace Plan

def fixtureId (plan : Plan) : FixtureId :=
  plan.fixture.fixtureId

def probeCount (plan : Plan) : Nat :=
  plan.probes.length

def taskCount (plan : Plan) : Nat :=
  plan.probeCount + 1

def labels (plan : Plan) : List ExactDocument.ClassName :=
  plan.probes.map ProbeTask.className

def selectors (plan : Plan) : List ExactDocument.ProbePlan.Selector :=
  plan.probes.map ProbeTask.selector

def selectorTexts (plan : Plan) : List String :=
  plan.probes.map ProbeTask.selectorText

def expectedBoxes (plan : Plan) : List Box :=
  plan.probes.map ProbeTask.expectedBox

def expectedStyles (plan : Plan) : List Style :=
  plan.probes.map ProbeTask.expectedStyle

def probeOrders (plan : Plan) : List Nat :=
  plan.probes.map ProbeTask.order

def tasks (plan : Plan) : List Task :=
  Task.loadPage plan.loadPage :: plan.probes.map Task.probe

theorem labels_length (plan : Plan) :
    plan.labels.length = plan.probeCount := by
  simp [labels, probeCount]

theorem selectors_length (plan : Plan) :
    plan.selectors.length = plan.probeCount := by
  simp [selectors, probeCount]

theorem selectorTexts_length (plan : Plan) :
    plan.selectorTexts.length = plan.probeCount := by
  simp [selectorTexts, probeCount]

theorem expectedBoxes_length (plan : Plan) :
    plan.expectedBoxes.length = plan.probeCount := by
  simp [expectedBoxes, probeCount]

theorem expectedStyles_length (plan : Plan) :
    plan.expectedStyles.length = plan.probeCount := by
  simp [expectedStyles, probeCount]

theorem tasks_length (plan : Plan) :
    plan.tasks.length = plan.taskCount := by
  simp [tasks, taskCount, probeCount]

def ofRequest (request : Request) : Plan :=
  { fixture := request.fixture
  , targetProfile := request.targetProfile
  , sourceGuarantee := request.sourceGuarantee
  , loadPage := LoadPageTask.ofRequest request
  , probes := ProbeTask.ofTargets request.probePlan.targets
  }

@[simp] theorem ofRequest_fixtureId (request : Request) :
    (ofRequest request).fixtureId = request.fixtureId := by
  rfl

@[simp] theorem ofRequest_targetProfile (request : Request) :
    (ofRequest request).targetProfile = request.targetProfile := by
  rfl

@[simp] theorem ofRequest_sourceGuarantee (request : Request) :
    (ofRequest request).sourceGuarantee = request.sourceGuarantee := by
  rfl

theorem ofRequest_probeCount (request : Request) :
    (ofRequest request).probeCount = request.nodeCount := by
  change (ProbeTask.ofTargets request.probePlan.targets).length = request.probePlan.targets.length
  exact ProbeTask.ofTargets_length request.probePlan.targets

theorem ofRequest_taskCount (request : Request) :
    (ofRequest request).taskCount = request.nodeCount + 1 := by
  rw [taskCount, ofRequest_probeCount]

theorem ofRequest_labels (request : Request) :
    (ofRequest request).labels = request.labels := by
  change (ProbeTask.ofTargets request.probePlan.targets).map ProbeTask.className =
    request.probePlan.targets.map ExpectedTarget.className
  exact ProbeTask.ofTargets_classNames request.probePlan.targets

theorem ofRequest_selectors (request : Request) :
    (ofRequest request).selectors =
      request.probePlan.targets.map (fun target => target.handle.toSelector) := by
  change (ProbeTask.ofTargets request.probePlan.targets).map ProbeTask.selector =
    request.probePlan.targets.map (fun target => target.handle.toSelector)
  exact ProbeTask.ofTargets_selectors request.probePlan.targets

theorem ofRequest_selectorTexts (request : Request) :
    (ofRequest request).selectorTexts = request.probePlan.selectorTexts := by
  change (ProbeTask.ofTargets request.probePlan.targets).map ProbeTask.selectorText =
    request.probePlan.targets.map ExpectedTarget.selectorText
  exact ProbeTask.ofTargets_selectorTexts request.probePlan.targets

theorem ofRequest_expectedBoxes (request : Request) :
    (ofRequest request).expectedBoxes = request.probePlan.boxes := by
  change (ProbeTask.ofTargets request.probePlan.targets).map ProbeTask.expectedBox =
    request.probePlan.targets.map ExpectedTarget.sourceBox
  exact ProbeTask.ofTargets_expectedBoxes request.probePlan.targets

theorem ofRequest_expectedStyles (request : Request) :
    (ofRequest request).expectedStyles = request.probePlan.styles := by
  change (ProbeTask.ofTargets request.probePlan.targets).map ProbeTask.expectedStyle =
    request.probePlan.targets.map ExpectedTarget.backendStyle
  exact ProbeTask.ofTargets_expectedStyles request.probePlan.targets

theorem ofRequest_tasks_length (request : Request) :
    (ofRequest request).tasks.length = request.nodeCount + 1 := by
  rw [tasks_length, ofRequest_taskCount]

def ofCase (case : Case) : Plan :=
  ofRequest (Request.ofCase case)

def ofFixtureId (fixtureId : FixtureId) : Plan :=
  ofCase (fixtureCase fixtureId)

def ofRequests (requests : List Request) : List Plan :=
  requests.map ofRequest

def ofCases (cases : List Case) : List Plan :=
  cases.map ofCase

theorem ofCase_fixtureId (case : Case) :
    (ofCase case).fixtureId = case.id := by
  simp [ofCase]

theorem ofCase_probeCount_eq_probePlanNodeCount (case : Case) :
    (ofCase case).probeCount = case.probePlan.nodeCount := by
  calc
    (ofCase case).probeCount = (Request.ofCase case).nodeCount := by
      exact ofRequest_probeCount (Request.ofCase case)
    _ = case.probePlan.nodeCount := by
      simpa [Request.ofCase, Request.nodeCount] using ProbePlanPayload.ofPlan_nodeCount case.probePlan

theorem ofCase_taskCount_eq_probePlanNodeCount_succ (case : Case) :
    (ofCase case).taskCount = case.probePlan.nodeCount + 1 := by
  rw [taskCount, ofCase_probeCount_eq_probePlanNodeCount]

theorem ofCase_labels_eq_probePlanLabels (case : Case) :
    (ofCase case).labels = case.probePlan.labels := by
  calc
    (ofCase case).labels = (Request.ofCase case).labels := by
      exact ofRequest_labels (Request.ofCase case)
    _ = case.probePlan.labels := by
      simpa [Request.ofCase, Request.labels] using ProbePlanPayload.ofPlan_labels case.probePlan

theorem ofCase_selectorTexts_eq_probePlanSelectorTexts (case : Case) :
    (ofCase case).selectorTexts = case.probePlan.selectorTexts := by
  calc
    (ofCase case).selectorTexts = (Request.ofCase case).probePlan.selectorTexts := by
      exact ofRequest_selectorTexts (Request.ofCase case)
    _ = case.probePlan.selectorTexts := by
      simpa [Request.ofCase] using ProbePlanPayload.ofPlan_selectorTexts case.probePlan

theorem ofCase_expectedBoxes_eq_probePlanBoxes (case : Case) :
    (ofCase case).expectedBoxes = case.probePlan.boxes := by
  calc
    (ofCase case).expectedBoxes = (Request.ofCase case).probePlan.boxes := by
      exact ofRequest_expectedBoxes (Request.ofCase case)
    _ = case.probePlan.boxes := by
      simpa [Request.ofCase] using ProbePlanPayload.ofPlan_boxes case.probePlan

theorem ofCase_expectedStyles_eq_probePlanStyles (case : Case) :
    (ofCase case).expectedStyles = case.probePlan.styles := by
  calc
    (ofCase case).expectedStyles = (Request.ofCase case).probePlan.styles := by
      exact ofRequest_expectedStyles (Request.ofCase case)
    _ = case.probePlan.styles := by
      simpa [Request.ofCase] using ProbePlanPayload.ofPlan_styles case.probePlan

def canonical : List Plan :=
  ofRequests canonicalRequests

def exactRowPlan : Plan :=
  ofCase exactRowCase

def paddedLeafPlan : Plan :=
  ofCase paddedLeafCase

def framedLeafPlan : Plan :=
  ofCase framedLeafCase

def nestedFrameRowPlan : Plan :=
  ofCase nestedFrameRowCase

theorem canonical_fixtureIds :
    canonical.map Plan.fixtureId = FixtureId.all := by
  calc
    canonical.map Plan.fixtureId = canonicalRequests.map (fun request => (ofRequest request).fixtureId) := by
      rfl
    _ = canonicalRequests.map Request.fixtureId := by
      simp
    _ = FixtureId.all := by
      exact TypedLayout.Backend.ExactCssHarnessProtocol.canonicalRequests_fixtureIds

theorem exactRowPlan_probeCount_eq_probePlanNodeCount :
    exactRowPlan.probeCount = exactRowCase.probePlan.nodeCount := by
  exact ofCase_probeCount_eq_probePlanNodeCount exactRowCase

theorem exactRowPlan_taskCount :
    exactRowPlan.taskCount = 5 := by
  native_decide

theorem exactRowPlan_labelSerials :
    ExactDocument.ClassName.serials exactRowPlan.labels = [0, 1, 2, 3] := by
  native_decide

theorem exactRowPlan_selectorTexts_eq_probePlanSelectorTexts :
    exactRowPlan.selectorTexts = exactRowCase.probePlan.selectorTexts := by
  exact ofCase_selectorTexts_eq_probePlanSelectorTexts exactRowCase

theorem paddedLeafPlan_taskCount :
    paddedLeafPlan.taskCount = 3 := by
  native_decide

theorem nestedFrameRowPlan_probeOrders :
    nestedFrameRowPlan.probeOrders = [0, 1, 2, 3, 4] := by
  native_decide

end Plan

end TypedLayout.Backend.ExactCssBrowserTaskPlan
