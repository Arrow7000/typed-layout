import TypedLayout.Backend.ExactCssBrowserTaskResult

namespace TypedLayout.Backend.ExactCssBrowserTaskOutcome

open TypedLayout.Backend.ExactCss
open TypedLayout.Backend.ExactCssFixtures
open TypedLayout.Backend.ExactCssHarnessCase
open TypedLayout.Backend.ExactCssHarnessProtocol
open TypedLayout.Backend.ExactCssBrowserTaskPlan
open TypedLayout.Backend.ExactCssBrowserTaskResult
open TypedLayout.Backend.ExactCss.Interchange
open TypedLayout.Backend.ExactCssVerdict

abbrev TaskPlan := TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan
abbrev TaskLoadPage := TypedLayout.Backend.ExactCssBrowserTaskPlan.LoadPageTask
abbrev TaskProbe := TypedLayout.Backend.ExactCssBrowserTaskPlan.ProbeTask

/-- Coarse exact-fragment page-load failure kinds for a future browser runner. -/
inductive LoadPageFailure where
  | pageUnavailable
  | runnerFailure
  deriving DecidableEq, Repr

/-- Coarse exact-fragment probe failure kinds for a future browser runner.

The taxonomy intentionally stays close to the typed probe boundary: selector
targeting, box collection, style collection, or a generic runner-side failure. -/
inductive ProbeFailure where
  | targetUnavailable
  | boxUnavailable
  | styleUnavailable
  | runnerFailure
  deriving DecidableEq, Repr

/-- Typed outcome for one planned exact page-load task. -/
inductive LoadPageOutcome where
  | success (task : TaskLoadPage) (result : LoadPageResult)
  | failure (task : TaskLoadPage) (failure : LoadPageFailure)
  deriving DecidableEq, Repr

namespace LoadPageOutcome

def task : LoadPageOutcome → TaskLoadPage
  | .success task _ => task
  | .failure task _ => task

def renderedPage (outcome : LoadPageOutcome) : ExactDocument.RenderedPage :=
  outcome.task.renderedPage

def toResult? : LoadPageOutcome → Option LoadPageResult
  | .success _ result => some result
  | .failure _ _ => none

def ofResult (task : TaskLoadPage) (result : LoadPageResult) : LoadPageOutcome :=
  .success task result

def ofTask (task : TaskLoadPage) : LoadPageOutcome :=
  ofResult task (LoadPageResult.ofTask task)

def ofPlanResult (result : PlanResult) : LoadPageOutcome :=
  ofResult result.plan.loadPage result.loadPage

@[simp] theorem renderedPage_eq_taskRenderedPage (outcome : LoadPageOutcome) :
    outcome.renderedPage = outcome.task.renderedPage := by
  cases outcome <;> rfl

@[simp] theorem toResult?_ofResult (task : TaskLoadPage) (result : LoadPageResult) :
    (ofResult task result).toResult? = some result :=
  rfl

@[simp] theorem toResult?_failure (task : TaskLoadPage) (failure : LoadPageFailure) :
    (LoadPageOutcome.failure task failure).toResult? = none :=
  rfl

@[simp] theorem ofPlanResult_toResult? (result : PlanResult) :
    (ofPlanResult result).toResult? = some result.loadPage :=
  rfl

end LoadPageOutcome

/-- Typed outcome for one planned exact probe task. -/
inductive ProbeOutcome where
  | success (task : TaskProbe) (result : ProbeResult)
  | failure (task : TaskProbe) (failure : ProbeFailure)
  deriving DecidableEq, Repr

namespace ProbeOutcome

def task : ProbeOutcome → TaskProbe
  | .success task _ => task
  | .failure task _ => task

def plannedOrder (outcome : ProbeOutcome) : Nat :=
  outcome.task.order

def plannedSelector (outcome : ProbeOutcome) : ExactDocument.ProbePlan.Selector :=
  outcome.task.selector

def plannedClassName (outcome : ProbeOutcome) : ExactDocument.ClassName :=
  outcome.task.className

def selectorText (outcome : ProbeOutcome) : String :=
  outcome.task.selectorText

def expectedBox (outcome : ProbeOutcome) :=
  outcome.task.expectedBox

def expectedStyle (outcome : ProbeOutcome) :=
  outcome.task.expectedStyle

def toObservationTarget? : ProbeOutcome → Option ExactDocument.ProbeObservation.Target
  | .success _ result => some result.toObservationTarget
  | .failure _ _ => none

def toResult? : ProbeOutcome → Option ProbeResult
  | .success _ result => some result
  | .failure _ _ => none

def ofResult (task : TaskProbe) (result : ProbeResult) : ProbeOutcome :=
  .success task result

private def pairSuccessfulOfPlanResult :
    (tasks : List TaskProbe) →
    (results : List ProbeResult) →
    tasks.length = results.length →
    List ProbeOutcome
  | [], [], _ => []
  | task :: tasks, result :: results, hLength =>
      have hTail : tasks.length = results.length :=
        Nat.succ.inj hLength
      ProbeOutcome.success task result ::
        pairSuccessfulOfPlanResult tasks results hTail
  | [], _ :: _, hLength => by
      cases hLength
  | _ :: _, [], hLength => by
      cases hLength

private theorem pairSuccessfulOfPlanResult_length :
    ∀ (tasks : List TaskProbe)
      (results : List ProbeResult)
      (hLength : tasks.length = results.length),
      (pairSuccessfulOfPlanResult tasks results hLength).length = tasks.length
  | [], [], _ => rfl
  | task :: tasks, result :: results, hLength =>
      have hTail : tasks.length = results.length :=
        Nat.succ.inj hLength
      by
        simp [pairSuccessfulOfPlanResult, pairSuccessfulOfPlanResult_length, hTail]
  | [], _ :: _, hLength => by
      cases hLength
  | _ :: _, [], hLength => by
      cases hLength

private theorem pairSuccessfulOfPlanResult_plannedOrders :
    ∀ (tasks : List TaskProbe)
      (results : List ProbeResult)
      (hLength : tasks.length = results.length),
      (pairSuccessfulOfPlanResult tasks results hLength).map ProbeOutcome.plannedOrder =
        tasks.map (fun task => task.order)
  | [], [], _ => rfl
  | task :: tasks, result :: results, hLength =>
      have hTail : tasks.length = results.length :=
        Nat.succ.inj hLength
      by
        simp [pairSuccessfulOfPlanResult, pairSuccessfulOfPlanResult_plannedOrders,
          ProbeOutcome.plannedOrder, ProbeOutcome.task]
  | [], _ :: _, hLength => by
      cases hLength
  | _ :: _, [], hLength => by
      cases hLength

def ofPlanResult (result : PlanResult) : List ProbeOutcome :=
  let hLength : result.plan.probes.length = result.probes.length := by
    have hCount : result.plan.probeCount = result.probeCount :=
      result.probeCount_eq_planProbeCount.symm
    simpa [TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.probeCount,
      TypedLayout.Backend.ExactCssBrowserTaskResult.PlanResult.probeCount] using hCount
  pairSuccessfulOfPlanResult result.plan.probes result.probes hLength

@[simp] theorem plannedOrder_eq_taskOrder (outcome : ProbeOutcome) :
    outcome.plannedOrder = outcome.task.order := by
  cases outcome <;> rfl

@[simp] theorem toResult?_ofResult (task : TaskProbe) (result : ProbeResult) :
    (ofResult task result).toResult? = some result :=
  rfl

@[simp] theorem toObservationTarget?_ofResult (task : TaskProbe) (result : ProbeResult) :
    (ofResult task result).toObservationTarget? = some result.toObservationTarget :=
  rfl

@[simp] theorem toResult?_failure (task : TaskProbe) (failure : ProbeFailure) :
    (ProbeOutcome.failure task failure).toResult? = none :=
  rfl

theorem ofPlanResult_length (result : PlanResult) :
    (ofPlanResult result).length = result.probeCount := by
  have hLength : result.plan.probes.length = result.probes.length := by
    have hCount : result.plan.probeCount = result.probeCount :=
      result.probeCount_eq_planProbeCount.symm
    simpa [TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.probeCount,
      TypedLayout.Backend.ExactCssBrowserTaskResult.PlanResult.probeCount] using hCount
  calc
    (ofPlanResult result).length = result.plan.probes.length := by
      simp [ofPlanResult, hLength, pairSuccessfulOfPlanResult_length]
    _ = result.probeCount := by
      simp [TypedLayout.Backend.ExactCssBrowserTaskResult.PlanResult.probeCount, hLength]

theorem ofPlanResult_plannedOrders (result : PlanResult) :
    (ofPlanResult result).map ProbeOutcome.plannedOrder = result.plan.probeOrders := by
  simp [ofPlanResult, pairSuccessfulOfPlanResult_plannedOrders,
    TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.probeOrders]

end ProbeOutcome

/-- Typed identification of which exact browser task failed. -/
inductive TaskFailure where
  | loadPage (task : TaskLoadPage) (failure : LoadPageFailure)
  | probe (task : TaskProbe) (failure : ProbeFailure)
  deriving DecidableEq, Repr

namespace TaskFailure

inductive Kind where
  | loadPage
  | probe
  deriving DecidableEq, Repr

def kind : TaskFailure → Kind
  | .loadPage _ _ => .loadPage
  | .probe _ _ => .probe

def toLoadPageOutcome? : TaskFailure → Option LoadPageOutcome
  | .loadPage task failure => some (.failure task failure)
  | .probe _ _ => none

def toProbeOutcome? : TaskFailure → Option ProbeOutcome
  | .loadPage _ _ => none
  | .probe task failure => some (.failure task failure)

@[simp] theorem kind_loadPage (task : TaskLoadPage) (failure : LoadPageFailure) :
    (TaskFailure.loadPage task failure).kind = .loadPage :=
  rfl

@[simp] theorem kind_probe (task : TaskProbe) (failure : ProbeFailure) :
    (TaskFailure.probe task failure).kind = .probe :=
  rfl

end TaskFailure

/-- Broader exact-fragment outcome for one planned browser-task bundle.

The current success-only `PlanResult` stays the success case; failures are kept
typed and intentionally coarse so runner policy does not become canonical yet. -/
inductive PlanOutcome where
  | success (result : PlanResult)
  | failure (plan : TaskPlan) (failure : TaskFailure)

namespace PlanOutcome

def plan : PlanOutcome → TaskPlan
  | .success result => result.plan
  | .failure plan _ => plan

def fixture (outcome : PlanOutcome) : FixtureRef :=
  outcome.plan.fixture

def fixtureId (outcome : PlanOutcome) : FixtureId :=
  outcome.plan.fixtureId

def targetProfile (outcome : PlanOutcome) :=
  outcome.plan.targetProfile

def sourceGuarantee (outcome : PlanOutcome) :=
  outcome.plan.sourceGuarantee

def failure? : PlanOutcome → Option TaskFailure
  | .success _ => none
  | PlanOutcome.failure _ failedTask => some failedTask

def toResult? : PlanOutcome → Option PlanResult
  | .success result => some result
  | .failure _ _ => none

def toObservation? (outcome : PlanOutcome) : Option ExactDocument.ProbeObservation.Document :=
  outcome.toResult?.map PlanResult.toObservation

def toObservationPayload? (outcome : PlanOutcome) : Option ObservationPayload :=
  outcome.toResult?.map PlanResult.toObservationPayload

def toResponse? (request : Request) (outcome : PlanOutcome) : Option Response :=
  outcome.toResult?.map (Response.ofTaskResult request)

def toComparison? (request : Request) (outcome : PlanOutcome) : Option ComparisonPayload :=
  (outcome.toResponse? request).map Response.comparison

def toReport? (request : Request) (outcome : PlanOutcome) : Option FixtureReport :=
  (outcome.toResponse? request).map Response.report

def ofPlanResult (result : PlanResult) : PlanOutcome :=
  .success result

@[simp] theorem toResult?_ofPlanResult (result : PlanResult) :
    (ofPlanResult result).toResult? = some result :=
  rfl

@[simp] theorem toResult?_failure (plan : TaskPlan) (failure : TaskFailure) :
    (PlanOutcome.failure plan failure).toResult? = none :=
  rfl

@[simp] theorem toObservation?_ofPlanResult (result : PlanResult) :
    (ofPlanResult result).toObservation? = some result.toObservation :=
  rfl

@[simp] theorem toObservationPayload?_ofPlanResult (result : PlanResult) :
    (ofPlanResult result).toObservationPayload? = some result.toObservationPayload :=
  rfl

@[simp] theorem toResponse?_ofPlanResult (request : Request) (result : PlanResult) :
    (ofPlanResult result).toResponse? request = some (Response.ofTaskResult request result) :=
  rfl

@[simp] theorem toResponse?_failure (request : Request) (plan : TaskPlan) (failure : TaskFailure) :
    (PlanOutcome.failure plan failure).toResponse? request = none :=
  rfl

@[simp] theorem toComparison?_ofPlanResult (request : Request) (result : PlanResult) :
    (ofPlanResult result).toComparison? request = some (Response.ofTaskResult request result).comparison :=
  rfl

@[simp] theorem toReport?_ofPlanResult (request : Request) (result : PlanResult) :
    (ofPlanResult result).toReport? request = some (Response.ofTaskResult request result).report :=
  rfl

end PlanOutcome

def exactRowOutcome : PlanOutcome :=
  PlanOutcome.ofPlanResult PlanResult.exactRowResult

def exactRowLoadFailure : PlanOutcome :=
  .failure TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.exactRowPlan
    (.loadPage TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.exactRowPlan.loadPage .pageUnavailable)

theorem exactRowOutcome_toResponse? :
    exactRowOutcome.toResponse? exactRowRequest = some exactRowResponse := by
  change some Response.exactRowFromTaskResult = some exactRowResponse
  rw [Response.exactRowFromTaskResult_eq_exactRowResponse]

theorem exactRowLoadFailure_toResponse? :
    exactRowLoadFailure.toResponse? exactRowRequest = none := by
  rfl

theorem exactRowLoadFailure_kind :
    exactRowLoadFailure.failure? =
      some (.loadPage TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.exactRowPlan.loadPage .pageUnavailable) := by
  rfl

theorem exactRowProbeOutcomes_plannedOrders :
    (ProbeOutcome.ofPlanResult PlanResult.exactRowResult).map ProbeOutcome.plannedOrder =
      TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.exactRowPlan.probeOrders := by
  simpa [PlanResult.exactRowResult] using
    ProbeOutcome.ofPlanResult_plannedOrders PlanResult.exactRowResult

end TypedLayout.Backend.ExactCssBrowserTaskOutcome
