import TypedLayout.Backend.ExactCssBrowserTaskOutcome

namespace TypedLayout.Backend.ExactCssHarnessExecutionOutcome

open TypedLayout.Backend.ExactCss
open TypedLayout.Backend.ExactCssFixtures
open TypedLayout.Backend.ExactCssHarnessCase
open TypedLayout.Backend.ExactCssHarnessProtocol
open TypedLayout.Backend.ExactCssVerdict
open TypedLayout.Backend.ExactCssBrowserTaskPlan
open TypedLayout.Backend.ExactCssBrowserTaskResult
open TypedLayout.Backend.ExactCssBrowserTaskOutcome

abbrev HarnessCaseReport := TypedLayout.Backend.ExactCssHarnessRun.CaseReport
abbrev HarnessCorpus := TypedLayout.Backend.ExactCssHarnessRun.Corpus
abbrev HarnessRunData := TypedLayout.Backend.ExactCssHarnessRun.Run
abbrev TaskPlan := TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan
abbrev TaskResult := TypedLayout.Backend.ExactCssBrowserTaskResult.PlanResult
abbrev TaskOutcome := TypedLayout.Backend.ExactCssBrowserTaskOutcome.PlanOutcome

/-- Harness-facing execution outcome for one exact harness case.

This stays directly over the browser task-outcome layer: successful executions keep
the exact `PlanResult`, while failures keep the coarse task failure together with
the case-aligned plan. -/
inductive CaseOutcome where
  | success (case : Case) (result : TaskResult) (fixtureId_eq : result.fixtureId = case.id)
  | failure (case : Case) (plan : TaskPlan) (failure : TaskFailure)
      (fixtureId_eq : plan.fixtureId = case.id)

namespace CaseOutcome

def case : CaseOutcome → Case
  | .success case _ _ => case
  | .failure case _ _ _ => case

def id (entry : CaseOutcome) : FixtureId :=
  entry.case.id

def request (entry : CaseOutcome) : Request :=
  Request.ofCase entry.case

def plan : CaseOutcome → TaskPlan
  | .success _ result _ => result.plan
  | .failure _ plan _ _ => plan

def toPlanOutcome : CaseOutcome → TaskOutcome
  | .success _ result _ => .success result
  | .failure _ plan failedTask _ =>
      TypedLayout.Backend.ExactCssBrowserTaskOutcome.PlanOutcome.failure plan failedTask

def result? : CaseOutcome → Option TaskResult
  | .success _ result _ => some result
  | .failure _ _ _ _ => none

def failure? : CaseOutcome → Option TaskFailure
  | .success _ _ _ => none
  | .failure _ _ failedTask _ => some failedTask

def response? : CaseOutcome → Option Response
  | .success case result _ => some (Response.ofTaskResult (Request.ofCase case) result)
  | .failure _ _ _ _ => none

def report? (entry : CaseOutcome) : Option FixtureReport :=
  entry.response?.map Response.report

def verdict? (entry : CaseOutcome) : Option Verdict :=
  entry.response?.map Response.verdict

def failureKind? : CaseOutcome → Option TaskFailure.Kind
  | .success _ _ _ => none
  | .failure _ _ failedTask _ => some failedTask.kind

def reportedIssueCount (entry : CaseOutcome) : Nat :=
  match entry.response? with
  | some response => response.issueCount
  | none => 0

def ofPlanResult (case : Case) (result : TaskResult) (fixtureId_eq : result.fixtureId = case.id) :
    CaseOutcome :=
  .success case result fixtureId_eq

def ofPlanFailure
    (case : Case)
    (plan : TaskPlan)
    (failedTask : TaskFailure)
    (fixtureId_eq : plan.fixtureId = case.id) : CaseOutcome :=
  .failure case plan failedTask fixtureId_eq

def ofPlanOutcome (case : Case) (outcome : TaskOutcome) (fixtureId_eq : outcome.fixtureId = case.id) :
    CaseOutcome :=
  match outcome with
  | .success result =>
      ofPlanResult case result (by
        simpa [TypedLayout.Backend.ExactCssBrowserTaskOutcome.PlanOutcome.fixtureId,
          TypedLayout.Backend.ExactCssBrowserTaskOutcome.PlanOutcome.plan,
          TypedLayout.Backend.ExactCssBrowserTaskResult.PlanResult.fixtureId] using fixtureId_eq)
  | .failure plan failedTask =>
      ofPlanFailure case plan failedTask (by
        simpa [TypedLayout.Backend.ExactCssBrowserTaskOutcome.PlanOutcome.fixtureId,
          TypedLayout.Backend.ExactCssBrowserTaskOutcome.PlanOutcome.plan,
          TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.fixtureId] using fixtureId_eq)

def ofCase (case : Case) : CaseOutcome :=
  ofPlanResult case (PlanResult.ofCase case) (PlanResult.ofCase_fixtureId case)

def ofRunEntry (entry : HarnessCaseReport) : CaseOutcome :=
  ofCase entry.case

@[simp] theorem request_fixtureId (entry : CaseOutcome) :
    entry.request.fixtureId = entry.id := by
  simp [request, id, case]

@[simp] theorem toPlanOutcome_fixtureId (entry : CaseOutcome) :
    entry.toPlanOutcome.fixtureId = entry.id := by
  cases entry with
  | success case result fixtureId_eq =>
      simpa [id, CaseOutcome.case, toPlanOutcome,
        TypedLayout.Backend.ExactCssBrowserTaskOutcome.PlanOutcome.fixtureId,
        TypedLayout.Backend.ExactCssBrowserTaskOutcome.PlanOutcome.plan,
        TypedLayout.Backend.ExactCssBrowserTaskResult.PlanResult.fixtureId] using fixtureId_eq
  | failure case plan failedTask fixtureId_eq =>
      simpa [id, CaseOutcome.case, toPlanOutcome,
        TypedLayout.Backend.ExactCssBrowserTaskOutcome.PlanOutcome.fixtureId,
        TypedLayout.Backend.ExactCssBrowserTaskOutcome.PlanOutcome.plan,
        TypedLayout.Backend.ExactCssBrowserTaskPlan.Plan.fixtureId] using fixtureId_eq

@[simp] theorem ofPlanOutcome_toPlanOutcome
    (case : Case)
    (outcome : TaskOutcome)
    (fixtureId_eq : outcome.fixtureId = case.id) :
    (ofPlanOutcome case outcome fixtureId_eq).toPlanOutcome = outcome := by
  cases outcome <;> simp [ofPlanOutcome, ofPlanFailure, ofPlanResult, toPlanOutcome]

@[simp] theorem ofCase_id (case : Case) :
    (ofCase case).id = case.id :=
  rfl

@[simp] theorem ofRunEntry_id (entry : HarnessCaseReport) :
    (ofRunEntry entry).id = entry.id := by
  simp [ofRunEntry, TypedLayout.Backend.ExactCssHarnessRun.CaseReport.id]

@[simp] theorem ofPlanFailure_failure?
    (case : Case)
    (plan : TaskPlan)
    (failedTask : TaskFailure)
    (fixtureId_eq : plan.fixtureId = case.id) :
    (ofPlanFailure case plan failedTask fixtureId_eq).failure? = some failedTask := by
  simp [ofPlanFailure, failure?]

@[simp] theorem ofPlanFailure_response?
    (case : Case)
    (plan : TaskPlan)
    (failedTask : TaskFailure)
    (fixtureId_eq : plan.fixtureId = case.id) :
    (ofPlanFailure case plan failedTask fixtureId_eq).response? = none := by
  simp [ofPlanFailure, response?]

@[simp] theorem ofCase_failure? (case : Case) :
    (ofCase case).failure? = none := by
  simp [ofCase, ofPlanResult, failure?]

@[simp] theorem ofCase_response? (case : Case) :
    (ofCase case).response? = some (Response.ofTaskResult (Request.ofCase case) (PlanResult.ofCase case)) := by
  simp [ofCase, ofPlanResult, response?]

end CaseOutcome

/-- Small typed execution summary for an exact harness corpus. -/
structure CorpusSummary where
  caseCount : Nat
  fixtureIds : List FixtureId
  deriving DecidableEq, Repr

def corpusSummary (corpus : HarnessCorpus) : CorpusSummary :=
  { caseCount := corpus.caseCount
  , fixtureIds := corpus.ids
  }

@[simp] theorem corpusSummary_caseCount (corpus : HarnessCorpus) :
    (corpusSummary corpus).caseCount = corpus.caseCount :=
  rfl

@[simp] theorem corpusSummary_fixtureIds (corpus : HarnessCorpus) :
    (corpusSummary corpus).fixtureIds = corpus.ids :=
  rfl

theorem canonicalCorpusSummary :
    corpusSummary TypedLayout.Backend.ExactCssHarnessRun.Corpus.canonical =
      { caseCount := 4
      , fixtureIds := [ .exactRow, .paddedLeaf, .framedLeaf, .nestedFrameRow ]
      } := by
  native_decide

/-- Pure ordered harness execution run made from per-case execution outcomes. -/
structure Run where
  entries : List CaseOutcome

namespace Run

/-- Small typed summary for a harness execution run. -/
structure Summary where
  caseCount : Nat
  fixtureIds : List FixtureId
  successIds : List FixtureId
  failureIds : List FixtureId
  exactMatchIds : List FixtureId
  mismatchIds : List FixtureId
  failureKinds : List TaskFailure.Kind
  successCount : Nat
  failureCount : Nat
  exactMatchCount : Nat
  mismatchCount : Nat
  totalIssueCount : Nat
  deriving DecidableEq, Repr

def ofCases (cases : List Case) : Run :=
  { entries := cases.map CaseOutcome.ofCase }

def ofCorpus (corpus : HarnessCorpus) : Run :=
  ofCases corpus.cases

def ofHarnessRun (run : HarnessRunData) : Run :=
  { entries := run.entries.map CaseOutcome.ofRunEntry }

def cases (run : Run) : List Case :=
  run.entries.map CaseOutcome.case

def requests (run : Run) : List Request :=
  run.entries.map CaseOutcome.request

def responses (run : Run) : List Response :=
  run.entries.filterMap CaseOutcome.response?

def reports (run : Run) : List FixtureReport :=
  run.responses.map Response.report

def caseCount (run : Run) : Nat :=
  run.entries.length

def fixtureIds (run : Run) : List FixtureId :=
  run.entries.map CaseOutcome.id

def successIds (run : Run) : List FixtureId :=
  run.responses.map Response.fixtureId

def failureIds (run : Run) : List FixtureId :=
  run.entries.filterMap fun entry =>
    match entry.failure? with
    | some _ => some entry.id
    | none => none

def exactMatchIds (run : Run) : List FixtureId :=
  run.responses.filterMap fun response =>
    match response.verdict with
    | .exactMatch => some response.fixtureId
    | .mismatch => none

def mismatchIds (run : Run) : List FixtureId :=
  run.responses.filterMap fun response =>
    match response.verdict with
    | .exactMatch => none
    | .mismatch => some response.fixtureId

def failureKinds (run : Run) : List TaskFailure.Kind :=
  run.entries.filterMap CaseOutcome.failureKind?

def successCount (run : Run) : Nat :=
  run.responses.length

def failureCount (run : Run) : Nat :=
  run.failureIds.length

def exactMatchCount (run : Run) : Nat :=
  run.exactMatchIds.length

def mismatchCount (run : Run) : Nat :=
  run.mismatchIds.length

def totalIssueCount (run : Run) : Nat :=
  run.responses.foldl (fun total response => total + response.issueCount) 0

def summary (run : Run) : Summary :=
  { caseCount := run.caseCount
  , fixtureIds := run.fixtureIds
  , successIds := run.successIds
  , failureIds := run.failureIds
  , exactMatchIds := run.exactMatchIds
  , mismatchIds := run.mismatchIds
  , failureKinds := run.failureKinds
  , successCount := run.successCount
  , failureCount := run.failureCount
  , exactMatchCount := run.exactMatchCount
  , mismatchCount := run.mismatchCount
  , totalIssueCount := run.totalIssueCount
  }

theorem ofCorpus_caseCount (corpus : HarnessCorpus) :
    (ofCorpus corpus).caseCount = corpus.caseCount := by
  simp [ofCorpus, ofCases, caseCount, TypedLayout.Backend.ExactCssHarnessRun.Corpus.caseCount]

theorem ofCorpus_fixtureIds (corpus : HarnessCorpus) :
    (ofCorpus corpus).fixtureIds = corpus.ids := by
  simp [ofCorpus, ofCases, fixtureIds, TypedLayout.Backend.ExactCssHarnessRun.Corpus.ids]

theorem ofHarnessRun_fixtureIds (run : HarnessRunData) :
    (ofHarnessRun run).fixtureIds = run.fixtureIds := by
  simp [ofHarnessRun, fixtureIds, TypedLayout.Backend.ExactCssHarnessRun.Run.fixtureIds]

theorem reports_length_eq_successCount (run : Run) :
    run.reports.length = run.successCount := by
  simp [reports, successCount, responses]

/-- Canonical baseline execution run recovered from the existing harness run layer. -/
def canonicalBaseline : Run :=
  ofHarnessRun TypedLayout.Backend.ExactCssHarnessRun.Run.canonicalBaseline

def exactRowBaselineOutcome : CaseOutcome :=
  CaseOutcome.ofRunEntry TypedLayout.Backend.ExactCssHarnessRun.Run.exactRowBaselineReport

def exactRowLoadFailureOutcome : CaseOutcome :=
  CaseOutcome.ofPlanOutcome exactRowCase exactRowLoadFailure rfl

def mixedFailureRun : Run :=
  { entries := [ exactRowLoadFailureOutcome, CaseOutcome.ofCase paddedLeafCase ] }

theorem exactRowBaselineOutcome_response? :
    exactRowBaselineOutcome.response? = some exactRowResponse := by
  native_decide

theorem exactRowLoadFailureOutcome_response? :
    exactRowLoadFailureOutcome.response? = none := by
  native_decide

theorem exactRowLoadFailureOutcome_failureKind? :
    exactRowLoadFailureOutcome.failureKind? = some .loadPage := by
  native_decide

theorem canonicalBaseline_summary :
    canonicalBaseline.summary =
      { caseCount := 4
      , fixtureIds := [ .exactRow, .paddedLeaf, .framedLeaf, .nestedFrameRow ]
      , successIds := [ .exactRow, .paddedLeaf, .framedLeaf, .nestedFrameRow ]
      , failureIds := []
      , exactMatchIds := [ .exactRow, .paddedLeaf, .framedLeaf, .nestedFrameRow ]
      , mismatchIds := []
      , failureKinds := []
      , successCount := 4
      , failureCount := 0
      , exactMatchCount := 4
      , mismatchCount := 0
      , totalIssueCount := 0
      } := by
  native_decide

theorem mixedFailureRun_summary :
    mixedFailureRun.summary =
      { caseCount := 2
      , fixtureIds := [ .exactRow, .paddedLeaf ]
      , successIds := [ .paddedLeaf ]
      , failureIds := [ .exactRow ]
      , exactMatchIds := [ .paddedLeaf ]
      , mismatchIds := []
      , failureKinds := [ .loadPage ]
      , successCount := 1
      , failureCount := 1
      , exactMatchCount := 1
      , mismatchCount := 0
      , totalIssueCount := 0
      } := by
  native_decide

end Run

end TypedLayout.Backend.ExactCssHarnessExecutionOutcome
