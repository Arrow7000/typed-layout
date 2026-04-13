import TypedLayout.Backend.ExactCssBrowserTaskPlan

namespace TypedLayout.Backend.ExactCss
namespace Interchange

namespace ProbePlanPayload

private theorem expectedTargets_toProbeTargets_ofProbeTargets
    (targets : List ExactDocument.ProbePlan.Target) :
    (targets.map ExpectedTarget.ofProbeTarget).map ExpectedTarget.toProbeTarget = targets := by
  induction targets with
  | nil =>
      rfl
  | cons target targets ih =>
      simp [ih]

/-- Recover the typed exact probe plan carried by a harness-facing probe payload. -/
def toPlan (payload : ProbePlanPayload) : ExactDocument.ProbePlan.Plan :=
  { targetProfile := payload.targetProfile
  , sourceGuarantee := payload.sourceGuarantee
  , root := payload.root.toProbeTarget
  , targets := payload.targets.map ExpectedTarget.toProbeTarget
  }

@[simp] theorem toPlan_targetProfile (payload : ProbePlanPayload) :
    payload.toPlan.targetProfile = payload.targetProfile :=
  rfl

@[simp] theorem toPlan_sourceGuarantee (payload : ProbePlanPayload) :
    payload.toPlan.sourceGuarantee = payload.sourceGuarantee :=
  rfl

theorem toPlan_labels (payload : ProbePlanPayload) :
    payload.toPlan.labels = payload.labels := by
  simp [toPlan, labels, ExactDocument.ProbePlan.Plan.labels, ExpectedTarget.toProbeTarget,
    ExpectedTarget.className, ExactDocument.ProbePlan.Target.className, TargetHandle.toSelector,
    ExactDocument.ProbePlan.Selector.className, List.map_map]

theorem toPlan_boxes (payload : ProbePlanPayload) :
    payload.toPlan.boxes = payload.boxes := by
  simp [toPlan, boxes, ExactDocument.ProbePlan.Plan.boxes, ExpectedTarget.toProbeTarget,
    List.map_map]

theorem toPlan_styles (payload : ProbePlanPayload) :
    payload.toPlan.styles = payload.styles := by
  simp [toPlan, styles, ExactDocument.ProbePlan.Plan.styles, ExpectedTarget.toProbeTarget,
    List.map_map]

theorem toPlan_nodeCount (payload : ProbePlanPayload) :
    payload.toPlan.nodeCount = payload.nodeCount := by
  simp [toPlan, nodeCount, ExactDocument.ProbePlan.Plan.nodeCount]

@[simp] theorem toPlan_ofPlan (plan : ExactDocument.ProbePlan.Plan) :
    (ofPlan plan).toPlan = plan := by
  cases plan with
  | mk targetProfile sourceGuarantee root targets =>
      simp [toPlan, ofPlan]
      simpa [List.map_map] using expectedTargets_toProbeTargets_ofProbeTargets targets

end ProbePlanPayload

namespace ObservationPayload

private theorem observedTargets_toObservationTargets_ofObservationTargets
    (targets : List ExactDocument.ProbeObservation.Target) :
    (targets.map ObservedTarget.ofObservationTarget).map ObservedTarget.toObservationTarget = targets := by
  induction targets with
  | nil =>
      rfl
  | cons target targets ih =>
      simp [ih]

/-- Recover the typed exact observation document carried by a harness observation payload. -/
def toObservation (payload : ObservationPayload) : ExactDocument.ProbeObservation.Document :=
  { targets := payload.targets.map ObservedTarget.toObservationTarget }

theorem toObservation_labels (payload : ObservationPayload) :
    payload.toObservation.labels = payload.labels := by
  simp [toObservation, labels, ExactDocument.ProbeObservation.Document.labels,
    ObservedTarget.toObservationTarget, ObservedTarget.className,
    ExactDocument.ProbeObservation.Target.className, TargetHandle.toSelector,
    ExactDocument.ProbePlan.Selector.className, List.map_map]

theorem toObservation_sourceBoxes (payload : ObservationPayload) :
    payload.toObservation.sourceBoxes = payload.sourceBoxes := by
  simp [toObservation, sourceBoxes, ExactDocument.ProbeObservation.Document.sourceBoxes,
    ObservedTarget.toObservationTarget, ObservedTarget.sourceBox,
    ExactDocument.ProbeObservation.Target.sourceBox, List.map_map]

theorem toObservation_backendStyles (payload : ObservationPayload) :
    payload.toObservation.backendStyles = payload.backendStyles := by
  simp [toObservation, backendStyles, ExactDocument.ProbeObservation.Document.backendStyles,
    ObservedTarget.toObservationTarget, ObservedTarget.backendStyle,
    ExactDocument.ProbeObservation.Target.backendStyle, List.map_map]

theorem toObservation_nodeCount (payload : ObservationPayload) :
    payload.toObservation.nodeCount = payload.nodeCount := by
  simp [toObservation, nodeCount, ExactDocument.ProbeObservation.Document.nodeCount]

@[simp] theorem toObservation_ofObservation
    (document : ExactDocument.ProbeObservation.Document) :
    (ofObservation document).toObservation = document := by
  cases document with
  | mk targets =>
      simp [toObservation, ofObservation]
      simpa [List.map_map] using
        observedTargets_toObservationTargets_ofObservationTargets targets

@[simp] theorem toObservation_ofPlan (plan : ExactDocument.ProbePlan.Plan) :
    (ofPlan plan).toObservation = ExactDocument.ProbeObservation.Document.ofPlan plan := by
  simp [ofPlan]

end ObservationPayload

end Interchange
end TypedLayout.Backend.ExactCss

namespace TypedLayout.Backend.ExactCssBrowserTaskResult

open TypedLayout.Core
open TypedLayout.Backend.ExactCss
open TypedLayout.Backend.ExactCssFixtures
open TypedLayout.Backend.ExactCssHarnessCase
open TypedLayout.Backend.ExactCssHarnessProtocol
open TypedLayout.Backend.ExactCssBrowserTaskPlan
open TypedLayout.Backend.ExactCss.Interchange

abbrev TaskPlan := TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan
abbrev TaskLoadPage := TypedLayout.Backend.ExactCssBrowserTaskPlan.LoadPageTask
abbrev TaskProbe := TypedLayout.Backend.ExactCssBrowserTaskPlan.ProbeTask

/-- Successful exact page-load result for a future browser runner.

The current exact fragment only models successful task execution; failure taxonomy
is intentionally left to later harness work. -/
structure LoadPageResult where
  renderedPage : ExactDocument.RenderedPage
  deriving DecidableEq, Repr

namespace LoadPageResult

def ofTask (task : TaskLoadPage) : LoadPageResult :=
  { renderedPage := task.renderedPage }

def ofRequest (request : Request) : LoadPageResult :=
  ofTask (TypedLayout.Backend.ExactCssBrowserTaskPlan.LoadPageTask.ofRequest request)

@[simp] theorem ofTask_renderedPage (task : TaskLoadPage) :
    (ofTask task).renderedPage = task.renderedPage :=
  rfl

@[simp] theorem ofRequest_renderedPage (request : Request) :
    (ofRequest request).renderedPage = request.renderedPage :=
  by simp [ofRequest]

end LoadPageResult

/-- Successful exact probe result for one ordered browser task.

The result records the probe order together with the observed selector, box, and
typed style slice collected for that slot. -/
structure ProbeResult where
  order : Nat
  selector : ExactDocument.ProbePlan.Selector
  box : ExactDocument.ProbeObservation.ObservedBox
  style : ExactDocument.ProbeObservation.ObservedStyle
  deriving DecidableEq, Repr

namespace ProbeResult

def className (result : ProbeResult) : ExactDocument.ClassName :=
  result.selector.className

def selectorText (result : ProbeResult) : String :=
  result.selector.text

def sourceBox (result : ProbeResult) : Box :=
  result.box.toSourceBox

def backendStyle (result : ProbeResult) : Style :=
  result.style.toBackendStyle

def toObservationTarget (result : ProbeResult) : ExactDocument.ProbeObservation.Target :=
  { selector := result.selector
  , box := result.box
  , style := result.style
  }

def ofTaskAndObservation
    (task : TaskProbe)
    (observed : ExactDocument.ProbeObservation.Target) : ProbeResult :=
  { order := task.order
  , selector := observed.selector
  , box := observed.box
  , style := observed.style
  }

@[simp] theorem toObservationTarget_selector (result : ProbeResult) :
    result.toObservationTarget.selector = result.selector :=
  rfl

@[simp] theorem toObservationTarget_box (result : ProbeResult) :
    result.toObservationTarget.box = result.box :=
  rfl

@[simp] theorem toObservationTarget_style (result : ProbeResult) :
    result.toObservationTarget.style = result.style :=
  rfl

@[simp] theorem toObservationTarget_className (result : ProbeResult) :
    result.toObservationTarget.className = result.className :=
  rfl

@[simp] theorem toObservationTarget_selectorText (result : ProbeResult) :
    result.toObservationTarget.selectorText = result.selectorText :=
  rfl

@[simp] theorem toObservationTarget_sourceBox (result : ProbeResult) :
    result.toObservationTarget.sourceBox = result.sourceBox :=
  rfl

@[simp] theorem toObservationTarget_backendStyle (result : ProbeResult) :
    result.toObservationTarget.backendStyle = result.backendStyle :=
  rfl

@[simp] theorem ofTaskAndObservation_order
    (task : TaskProbe)
    (observed : ExactDocument.ProbeObservation.Target) :
    (ofTaskAndObservation task observed).order = task.order :=
  rfl

@[simp] theorem ofTaskAndObservation_selector
    (task : TaskProbe)
    (observed : ExactDocument.ProbeObservation.Target) :
    (ofTaskAndObservation task observed).selector = observed.selector :=
  rfl

@[simp] theorem ofTaskAndObservation_box
    (task : TaskProbe)
    (observed : ExactDocument.ProbeObservation.Target) :
    (ofTaskAndObservation task observed).box = observed.box :=
  rfl

@[simp] theorem ofTaskAndObservation_style
    (task : TaskProbe)
    (observed : ExactDocument.ProbeObservation.Target) :
    (ofTaskAndObservation task observed).style = observed.style :=
  rfl

@[simp] theorem toObservationTarget_ofTaskAndObservation
    (task : TaskProbe)
    (observed : ExactDocument.ProbeObservation.Target) :
    (ofTaskAndObservation task observed).toObservationTarget = observed := by
  cases observed
  rfl

end ProbeResult

private def pairProbeResults :
    (tasks : List TaskProbe) →
    (observed : List ExactDocument.ProbeObservation.Target) →
    tasks.length = observed.length →
    List ProbeResult
  | [], [], _ => []
  | task :: tasks, observed :: observeds, hLength =>
      have hTail : tasks.length = observeds.length :=
        Nat.succ.inj hLength
      ProbeResult.ofTaskAndObservation task observed ::
        pairProbeResults tasks observeds hTail
  | [], _ :: _, hLength => by
      cases hLength
  | _ :: _, [], hLength => by
      cases hLength

private theorem pairProbeResults_length :
    ∀ (tasks : List TaskProbe)
      (observed : List ExactDocument.ProbeObservation.Target)
      (hLength : tasks.length = observed.length),
      (pairProbeResults tasks observed hLength).length = tasks.length
  | [], [], _ => rfl
  | task :: tasks, observed :: observeds, hLength =>
      have hTail : tasks.length = observeds.length :=
        Nat.succ.inj hLength
      by
        simp [pairProbeResults, pairProbeResults_length, hTail]
  | [], _ :: _, hLength => by
      cases hLength
  | _ :: _, [], hLength => by
      cases hLength

private theorem pairProbeResults_orders :
    ∀ (tasks : List TaskProbe)
      (observed : List ExactDocument.ProbeObservation.Target)
      (hLength : tasks.length = observed.length),
      (pairProbeResults tasks observed hLength).map ProbeResult.order =
        tasks.map (fun task => task.order)
  | [], [], _ => rfl
  | task :: tasks, observed :: observeds, hLength =>
      have hTail : tasks.length = observeds.length :=
        Nat.succ.inj hLength
      by
        simp [pairProbeResults, pairProbeResults_orders]
  | [], _ :: _, hLength => by
      cases hLength
  | _ :: _, [], hLength => by
      cases hLength

private theorem pairProbeResults_toObservationTargets :
    ∀ (tasks : List TaskProbe)
      (observed : List ExactDocument.ProbeObservation.Target)
      (hLength : tasks.length = observed.length),
      (pairProbeResults tasks observed hLength).map ProbeResult.toObservationTarget = observed
  | [], [], _ => rfl
  | task :: tasks, observed :: observeds, hLength =>
      have hTail : tasks.length = observeds.length :=
        Nat.succ.inj hLength
      by
        simp [pairProbeResults, pairProbeResults_toObservationTargets]
  | [], _ :: _, hLength => by
      cases hLength
  | _ :: _, [], hLength => by
      cases hLength

/-- Successful exact task-result bundle for one browser task plan.

This packages the loaded page result together with one probe result per planned
probe order, so the runner-facing layer stays aligned with the pure task plan. -/
structure PlanResult where
  plan : TaskPlan
  loadPage : LoadPageResult
  loadPage_renderedPage_eq : loadPage.renderedPage = plan.loadPage.renderedPage
  probes : List ProbeResult
  probeOrders_eq : probes.map ProbeResult.order = plan.probeOrders

namespace PlanResult

def fixture (result : PlanResult) : FixtureRef :=
  result.plan.fixture

def fixtureId (result : PlanResult) : FixtureId :=
  result.plan.fixtureId

def targetProfile (result : PlanResult) : BlessedCssProfile :=
  result.plan.targetProfile

def sourceGuarantee (result : PlanResult) : GuaranteeClass :=
  result.plan.sourceGuarantee

def renderedPage (result : PlanResult) : ExactDocument.RenderedPage :=
  result.loadPage.renderedPage

def probeCount (result : PlanResult) : Nat :=
  result.probes.length

def taskCount (result : PlanResult) : Nat :=
  result.probeCount + 1

def labels (result : PlanResult) : List ExactDocument.ClassName :=
  result.probes.map ProbeResult.className

def selectorTexts (result : PlanResult) : List String :=
  result.probes.map ProbeResult.selectorText

def sourceBoxes (result : PlanResult) : List Box :=
  result.probes.map ProbeResult.sourceBox

def backendStyles (result : PlanResult) : List Style :=
  result.probes.map ProbeResult.backendStyle

def orders (result : PlanResult) : List Nat :=
  result.probes.map ProbeResult.order

def toObservation (result : PlanResult) : ExactDocument.ProbeObservation.Document :=
  { targets := result.probes.map ProbeResult.toObservationTarget }

def toObservationPayload (result : PlanResult) : ObservationPayload :=
  ObservationPayload.ofObservation result.toObservation

theorem renderedPage_eq_planRenderedPage (result : PlanResult) :
    result.renderedPage = result.plan.loadPage.renderedPage :=
  result.loadPage_renderedPage_eq

theorem orders_eq_planProbeOrders (result : PlanResult) :
    result.orders = result.plan.probeOrders :=
  result.probeOrders_eq

theorem probeCount_eq_planProbeCount (result : PlanResult) :
    result.probeCount = result.plan.probeCount := by
  have hLengths := congrArg List.length result.probeOrders_eq
  simpa [orders, probeCount,
    TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.probeOrders,
    TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.probeCount] using hLengths

theorem taskCount_eq_planTaskCount (result : PlanResult) :
    result.taskCount = result.plan.taskCount := by
  simp [taskCount,
    TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.taskCount,
    probeCount_eq_planProbeCount]

theorem toObservation_labels (result : PlanResult) :
    result.toObservation.labels = result.labels := by
  simp [toObservation, labels, ExactDocument.ProbeObservation.Document.labels, List.map_map]

theorem toObservation_selectorTexts (result : PlanResult) :
    result.toObservation.selectorTexts = result.selectorTexts := by
  simp [toObservation, selectorTexts, ExactDocument.ProbeObservation.Document.selectorTexts,
    List.map_map]

theorem toObservation_sourceBoxes (result : PlanResult) :
    result.toObservation.sourceBoxes = result.sourceBoxes := by
  simp [toObservation, sourceBoxes, ExactDocument.ProbeObservation.Document.sourceBoxes,
    List.map_map]

theorem toObservation_backendStyles (result : PlanResult) :
    result.toObservation.backendStyles = result.backendStyles := by
  simp [toObservation, backendStyles, ExactDocument.ProbeObservation.Document.backendStyles,
    List.map_map]

theorem toObservation_nodeCount (result : PlanResult) :
    result.toObservation.nodeCount = result.probeCount := by
  simp [toObservation, ExactDocument.ProbeObservation.Document.nodeCount, probeCount]

theorem toObservationPayload_labels (result : PlanResult) :
    result.toObservationPayload.labels = result.labels := by
  calc
    result.toObservationPayload.labels = result.toObservation.labels := by
      simpa [toObservationPayload] using ObservationPayload.ofObservation_labels result.toObservation
    _ = result.labels := by
      exact result.toObservation_labels

theorem toObservationPayload_sourceBoxes (result : PlanResult) :
    result.toObservationPayload.sourceBoxes = result.sourceBoxes := by
  calc
    result.toObservationPayload.sourceBoxes = result.toObservation.sourceBoxes := by
      simpa [toObservationPayload] using
        ObservationPayload.ofObservation_sourceBoxes result.toObservation
    _ = result.sourceBoxes := by
      exact result.toObservation_sourceBoxes

theorem toObservationPayload_backendStyles (result : PlanResult) :
    result.toObservationPayload.backendStyles = result.backendStyles := by
  calc
    result.toObservationPayload.backendStyles = result.toObservation.backendStyles := by
      simpa [toObservationPayload] using
        ObservationPayload.ofObservation_backendStyles result.toObservation
    _ = result.backendStyles := by
      exact result.toObservation_backendStyles

theorem toObservationPayload_nodeCount (result : PlanResult) :
    result.toObservationPayload.nodeCount = result.probeCount := by
  calc
    result.toObservationPayload.nodeCount = result.toObservation.nodeCount := by
      simpa [toObservationPayload] using ObservationPayload.ofObservation_nodeCount result.toObservation
    _ = result.probeCount := by
      exact result.toObservation_nodeCount

def ofPlanAndObservation
    (plan : TaskPlan)
    (observation : ExactDocument.ProbeObservation.Document)
    (hLength : plan.probes.length = observation.targets.length) : PlanResult :=
  { plan := plan
  , loadPage := LoadPageResult.ofTask plan.loadPage
  , loadPage_renderedPage_eq := rfl
  , probes := pairProbeResults plan.probes observation.targets hLength
  , probeOrders_eq := by
      simpa [orders,
        TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.probeOrders] using
        pairProbeResults_orders plan.probes observation.targets hLength
  }

theorem ofPlanAndObservation_toObservation
    (plan : TaskPlan)
    (observation : ExactDocument.ProbeObservation.Document)
    (hLength : plan.probes.length = observation.targets.length) :
    (ofPlanAndObservation plan observation hLength).toObservation = observation := by
  cases observation
  simp [ofPlanAndObservation, toObservation, pairProbeResults_toObservationTargets]

theorem ofPlanAndObservation_probeCount_eq_planProbeCount
    (plan : TaskPlan)
    (observation : ExactDocument.ProbeObservation.Document)
    (hLength : plan.probes.length = observation.targets.length) :
    (ofPlanAndObservation plan observation hLength).probeCount = plan.probeCount := by
  exact (ofPlanAndObservation plan observation hLength).probeCount_eq_planProbeCount

theorem ofPlanAndObservation_orders_eq_planProbeOrders
    (plan : TaskPlan)
    (observation : ExactDocument.ProbeObservation.Document)
    (hLength : plan.probes.length = observation.targets.length) :
    (ofPlanAndObservation plan observation hLength).orders = plan.probeOrders := by
  exact (ofPlanAndObservation plan observation hLength).orders_eq_planProbeOrders

theorem ofPlanAndObservation_labels_eq_observationLabels
    (plan : TaskPlan)
    (observation : ExactDocument.ProbeObservation.Document)
    (hLength : plan.probes.length = observation.targets.length) :
    (ofPlanAndObservation plan observation hLength).labels = observation.labels := by
  calc
    (ofPlanAndObservation plan observation hLength).labels =
        (ofPlanAndObservation plan observation hLength).toObservation.labels := by
      symm
      exact (ofPlanAndObservation plan observation hLength).toObservation_labels
    _ = observation.labels := by
      rw [ofPlanAndObservation_toObservation plan observation hLength]

theorem ofPlanAndObservation_selectorTexts_eq_observationSelectorTexts
    (plan : TaskPlan)
    (observation : ExactDocument.ProbeObservation.Document)
    (hLength : plan.probes.length = observation.targets.length) :
    (ofPlanAndObservation plan observation hLength).selectorTexts = observation.selectorTexts := by
  calc
    (ofPlanAndObservation plan observation hLength).selectorTexts =
        (ofPlanAndObservation plan observation hLength).toObservation.selectorTexts := by
      symm
      exact (ofPlanAndObservation plan observation hLength).toObservation_selectorTexts
    _ = observation.selectorTexts := by
      rw [ofPlanAndObservation_toObservation plan observation hLength]

theorem ofPlanAndObservation_sourceBoxes_eq_observationSourceBoxes
    (plan : TaskPlan)
    (observation : ExactDocument.ProbeObservation.Document)
    (hLength : plan.probes.length = observation.targets.length) :
    (ofPlanAndObservation plan observation hLength).sourceBoxes = observation.sourceBoxes := by
  calc
    (ofPlanAndObservation plan observation hLength).sourceBoxes =
        (ofPlanAndObservation plan observation hLength).toObservation.sourceBoxes := by
      symm
      exact (ofPlanAndObservation plan observation hLength).toObservation_sourceBoxes
    _ = observation.sourceBoxes := by
      rw [ofPlanAndObservation_toObservation plan observation hLength]

theorem ofPlanAndObservation_backendStyles_eq_observationBackendStyles
    (plan : TaskPlan)
    (observation : ExactDocument.ProbeObservation.Document)
    (hLength : plan.probes.length = observation.targets.length) :
    (ofPlanAndObservation plan observation hLength).backendStyles = observation.backendStyles := by
  calc
    (ofPlanAndObservation plan observation hLength).backendStyles =
        (ofPlanAndObservation plan observation hLength).toObservation.backendStyles := by
      symm
      exact (ofPlanAndObservation plan observation hLength).toObservation_backendStyles
    _ = observation.backendStyles := by
      rw [ofPlanAndObservation_toObservation plan observation hLength]

def ofRequestAndObservation
    (request : Request)
    (observation : ExactDocument.ProbeObservation.Document)
    (hLength :
      (TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.ofRequest request).probes.length =
        observation.targets.length) : PlanResult :=
  ofPlanAndObservation
    (TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.ofRequest request)
    observation hLength

private theorem case_probeLength_eq_observationLength (case : Case) :
    (TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.ofCase case).probes.length =
      case.baselineObservation.targets.length := by
  have hPlan :
      (TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.ofCase case).probeCount =
        case.probePlan.nodeCount :=
    TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.ofCase_probeCount_eq_probePlanNodeCount case
  have hObservation : case.baselineObservation.nodeCount = case.probePlan.nodeCount := by
    simpa [Case.baselineObservation, Case.probePlan] using
      Fixture.observation_nodeCount_eq_probePlan_nodeCount case.fixture
  simpa [TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.probeCount,
    ExactDocument.ProbeObservation.Document.nodeCount] using
    hPlan.trans hObservation.symm

def ofCase (case : Case) : PlanResult :=
  ofPlanAndObservation
    (TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.ofCase case)
    case.baselineObservation
    (case_probeLength_eq_observationLength case)

def ofFixtureId (fixtureId : FixtureId) : PlanResult :=
  ofCase (fixtureCase fixtureId)

def ofCases (cases : List Case) : List PlanResult :=
  cases.map ofCase

def canonical : List PlanResult :=
  ofCases TypedLayout.Backend.ExactCssHarnessCase.canonical

def exactRowResult : PlanResult :=
  ofCase exactRowCase

def paddedLeafResult : PlanResult :=
  ofCase paddedLeafCase

def framedLeafResult : PlanResult :=
  ofCase framedLeafCase

def nestedFrameRowResult : PlanResult :=
  ofCase nestedFrameRowCase

@[simp] theorem ofCase_fixtureId (case : Case) :
    (ofCase case).fixtureId = case.id := by
  simpa [ofCase] using
    TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.ofCase_fixtureId case

theorem ofCase_probeCount_eq_probePlanNodeCount (case : Case) :
    (ofCase case).probeCount = case.probePlan.nodeCount := by
  calc
    (ofCase case).probeCount =
        (TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.ofCase case).probeCount := by
      exact (ofCase case).probeCount_eq_planProbeCount
    _ = case.probePlan.nodeCount := by
      exact
        TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.ofCase_probeCount_eq_probePlanNodeCount case

theorem ofCase_labels_eq_probePlanLabels (case : Case) :
    (ofCase case).labels = case.probePlan.labels := by
  calc
    (ofCase case).labels = case.baselineObservation.labels := by
      exact ofPlanAndObservation_labels_eq_observationLabels _ _ _
    _ = case.probePlan.labels := by
      exact case.observationLabels_eq_probePlanLabels

theorem ofCase_selectorTexts_eq_probePlanSelectorTexts (case : Case) :
    (ofCase case).selectorTexts = case.probePlan.selectorTexts := by
  have hObservation : case.baselineObservation.selectorTexts = case.probePlan.selectorTexts := by
    simpa [Case.baselineObservation, Case.probePlan] using
      ExactDocument.ProbeObservation.Document.ofPlan_selectorTexts case.fixture.probePlan
  calc
    (ofCase case).selectorTexts = case.baselineObservation.selectorTexts := by
      exact ofPlanAndObservation_selectorTexts_eq_observationSelectorTexts _ _ _
    _ = case.probePlan.selectorTexts := by
      exact hObservation

theorem ofCase_sourceBoxes_eq_probePlanBoxes (case : Case) :
    (ofCase case).sourceBoxes = case.probePlan.boxes := by
  calc
    (ofCase case).sourceBoxes = case.baselineObservation.sourceBoxes := by
      exact ofPlanAndObservation_sourceBoxes_eq_observationSourceBoxes _ _ _
    _ = case.probePlan.boxes := by
      simpa [Case.baselineObservation, Case.probePlan] using
        Fixture.observation_sourceBoxes_eq_probePlan_boxes case.fixture

theorem ofCase_backendStyles_eq_probePlanStyles (case : Case) :
    (ofCase case).backendStyles = case.probePlan.styles := by
  calc
    (ofCase case).backendStyles = case.baselineObservation.backendStyles := by
      exact ofPlanAndObservation_backendStyles_eq_observationBackendStyles _ _ _
    _ = case.probePlan.styles := by
      simpa [Case.baselineObservation, Case.probePlan] using
        Fixture.observation_backendStyles_eq_probePlan_styles case.fixture

theorem canonical_fixtureIds :
    canonical.map PlanResult.fixtureId = FixtureId.all := by
  calc
    canonical.map PlanResult.fixtureId =
        TypedLayout.Backend.ExactCssHarnessCase.canonical.map Case.id := by
      simp [canonical, ofCases]
    _ = FixtureId.all := by
      exact TypedLayout.Backend.ExactCssHarnessCase.canonical_ids

theorem exactRowResult_probeCount_eq_probePlanNodeCount :
    exactRowResult.probeCount = exactRowCase.probePlan.nodeCount := by
  exact ofCase_probeCount_eq_probePlanNodeCount exactRowCase

theorem exactRowResult_selectorTexts_eq_probePlanSelectorTexts :
    exactRowResult.selectorTexts = exactRowCase.probePlan.selectorTexts := by
  exact ofCase_selectorTexts_eq_probePlanSelectorTexts exactRowCase

theorem exactRowResult_sourceBoxes_eq_probePlanBoxes :
    exactRowResult.sourceBoxes = exactRowCase.probePlan.boxes := by
  exact ofCase_sourceBoxes_eq_probePlanBoxes exactRowCase

theorem nestedFrameRowResult_orders :
    nestedFrameRowResult.orders = [0, 1, 2, 3, 4] := by
  native_decide

end PlanResult

end TypedLayout.Backend.ExactCssBrowserTaskResult

namespace TypedLayout.Backend.ExactCssHarnessProtocol

open TypedLayout.Backend.ExactCss
open TypedLayout.Backend.ExactCssVerdict
open TypedLayout.Backend.ExactCss.Interchange

namespace Response

/-- Rebuild a typed exact harness response from a request plus a typed task result. -/
def ofTaskResult
    (request : Request)
    (result : TypedLayout.Backend.ExactCssBrowserTaskResult.PlanResult) : Response :=
  let observation := result.toObservationPayload
  let comparison := ComparisonPayload.ofComparison <|
    ExactDocument.ProbeComparison.DocumentComparison.compare
      request.probePlan.toPlan
      observation.toObservation
  { observation := observation
  , comparison := comparison
  , report :=
      { fixture := request.fixture
      , report := Report.ofComparisonPayload comparison
      }
  }

@[simp] theorem ofTaskResult_fixtureId
    (request : Request)
    (result : TypedLayout.Backend.ExactCssBrowserTaskResult.PlanResult) :
    (ofTaskResult request result).fixtureId = request.fixtureId := by
  rfl

@[simp] theorem ofTaskResult_observation
    (request : Request)
    (result : TypedLayout.Backend.ExactCssBrowserTaskResult.PlanResult) :
    (ofTaskResult request result).observation = result.toObservationPayload := by
  rfl

theorem ofTaskResult_comparison
    (request : Request)
    (result : TypedLayout.Backend.ExactCssBrowserTaskResult.PlanResult) :
    (ofTaskResult request result).comparison =
      ComparisonPayload.ofComparison
        (ExactDocument.ProbeComparison.DocumentComparison.compare
          request.probePlan.toPlan
          result.toObservation) := by
  simp [ofTaskResult, TypedLayout.Backend.ExactCssBrowserTaskResult.PlanResult.toObservationPayload]

theorem ofTaskResult_observationLabels_eq_resultLabels
    (request : Request)
    (result : TypedLayout.Backend.ExactCssBrowserTaskResult.PlanResult) :
    (ofTaskResult request result).observation.labels = result.labels := by
  simpa using result.toObservationPayload_labels

theorem ofTaskResult_comparisonTargetProfile_eq_requestTargetProfile
    (request : Request)
    (result : TypedLayout.Backend.ExactCssBrowserTaskResult.PlanResult) :
    (ofTaskResult request result).comparison.targetProfile = request.targetProfile := by
  rfl

theorem ofTaskResult_comparisonSourceGuarantee_eq_requestSourceGuarantee
    (request : Request)
    (result : TypedLayout.Backend.ExactCssBrowserTaskResult.PlanResult) :
    (ofTaskResult request result).comparison.sourceGuarantee = request.sourceGuarantee := by
  rfl

theorem ofTaskResult_comparisonExpectedCount_eq_requestNodeCount
    (request : Request)
    (result : TypedLayout.Backend.ExactCssBrowserTaskResult.PlanResult) :
    (ofTaskResult request result).comparison.expectedCount = request.nodeCount := by
  calc
    (ofTaskResult request result).comparison.expectedCount = request.probePlan.toPlan.nodeCount := by
      rw [ofTaskResult_comparison]
      exact ExactDocument.ProbeComparison.DocumentComparison.compare_expectedCount
        request.probePlan.toPlan result.toObservation
    _ = request.probePlan.nodeCount := by
      exact ProbePlanPayload.toPlan_nodeCount request.probePlan
    _ = request.nodeCount := by
      rfl

theorem ofTaskResult_comparisonObservedCount_eq_resultProbeCount
    (request : Request)
    (result : TypedLayout.Backend.ExactCssBrowserTaskResult.PlanResult) :
    (ofTaskResult request result).comparison.observedCount = result.probeCount := by
  calc
    (ofTaskResult request result).comparison.observedCount = result.toObservation.nodeCount := by
      rw [ofTaskResult_comparison]
      exact ExactDocument.ProbeComparison.DocumentComparison.compare_observedCount
        request.probePlan.toPlan result.toObservation
    _ = result.probeCount := by
      exact result.toObservation_nodeCount

def exactRowFromTaskResult : Response :=
  ofTaskResult exactRowRequest TypedLayout.Backend.ExactCssBrowserTaskResult.PlanResult.exactRowResult

theorem exactRowFromTaskResult_eq_exactRowResponse :
    exactRowFromTaskResult = exactRowResponse := by
  native_decide

theorem exactRowFromTaskResult_verdict :
    exactRowFromTaskResult.verdict = .exactMatch := by
  calc
    exactRowFromTaskResult.verdict = exactRowResponse.verdict := by
      rw [exactRowFromTaskResult_eq_exactRowResponse]
    _ = .exactMatch := by
      exact exactRowResponse_verdict

theorem exactRowFromTaskResult_observationLabels :
    exactRowFromTaskResult.observation.labels = exactRowRequest.labels := by
  calc
    exactRowFromTaskResult.observation.labels = exactRowResponse.observation.labels := by
      rw [exactRowFromTaskResult_eq_exactRowResponse]
    _ = TypedLayout.Backend.ExactCssHarnessCase.exactRowCase.probePlan.labels := by
      exact Response.ofCase_observationLabels_eq_probePlanLabels
        TypedLayout.Backend.ExactCssHarnessCase.exactRowCase
    _ = exactRowRequest.labels := by
      symm
      exact Request.ofCase_labels TypedLayout.Backend.ExactCssHarnessCase.exactRowCase

end Response

end TypedLayout.Backend.ExactCssHarnessProtocol
