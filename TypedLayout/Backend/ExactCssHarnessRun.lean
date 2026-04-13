import TypedLayout.Backend.ExactCssVerdict

namespace TypedLayout.Backend.ExactCssHarnessRun

open TypedLayout.Backend.ExactCss
open TypedLayout.Backend.ExactCssFixtures
open TypedLayout.Backend.ExactCssHarnessCase
open TypedLayout.Backend.ExactCssVerdict

/-- Typed baseline report paired with one exact harness case.

The proof field keeps the case/report linkage honest at the fixture-id level while
still allowing the run layer to remain a pure typed data model. -/
structure CaseReport where
  case : Case
  report : FixtureReport
  fixtureId_eq : report.fixtureId = case.id

namespace CaseReport

def ofCase (case : Case) : CaseReport :=
  { case := case
  , report := FixtureReport.ofCase case
  , fixtureId_eq := FixtureReport.ofCase_fixtureId case
  }

def id (entry : CaseReport) : FixtureId :=
  entry.case.id

def verdict (entry : CaseReport) : Verdict :=
  entry.report.verdict

def counts (entry : CaseReport) : Counts :=
  entry.report.counts

def issueCount (entry : CaseReport) : Nat :=
  entry.report.report.issueCount

def issueLabels (entry : CaseReport) : List ExactDocument.ClassName :=
  entry.report.issueLabels

@[simp] theorem ofCase_id (case : Case) :
    (ofCase case).id = case.id :=
  rfl

@[simp] theorem ofCase_fixtureId (case : Case) :
    (ofCase case).report.fixtureId = case.id := by
  simpa [ofCase] using FixtureReport.ofCase_fixtureId case

@[simp] theorem report_fixtureId (entry : CaseReport) :
    entry.report.fixtureId = entry.id := by
  simpa [id] using entry.fixtureId_eq

end CaseReport

/-- Ordered typed exact harness corpus. -/
structure Corpus where
  cases : List Case

/-- Pure ordered exact harness run consisting of typed case reports. -/
structure Run where
  entries : List CaseReport

namespace Corpus

/-- Small typed summary for a harness corpus. -/
structure Summary where
  caseCount : Nat
  fixtureIds : List FixtureId
  deriving DecidableEq, Repr

def ids (corpus : Corpus) : List FixtureId :=
  corpus.cases.map Case.id

def caseCount (corpus : Corpus) : Nat :=
  corpus.cases.length

def baselineCaseReports (corpus : Corpus) : List CaseReport :=
  corpus.cases.map CaseReport.ofCase

def summary (corpus : Corpus) : Summary :=
  { caseCount := corpus.caseCount
  , fixtureIds := corpus.ids
  }

theorem ids_length_eq_caseCount (corpus : Corpus) :
    corpus.ids.length = corpus.caseCount := by
  simp [ids, caseCount]

theorem baselineCaseReports_length_eq_caseCount (corpus : Corpus) :
    corpus.baselineCaseReports.length = corpus.caseCount := by
  simp [baselineCaseReports, caseCount]

/-- Canonical exact harness corpus aligned with the canonical exact harness cases. -/
def canonical : Corpus :=
  { cases := TypedLayout.Backend.ExactCssHarnessCase.canonical }

theorem canonical_ids :
    canonical.ids = FixtureId.all := by
  simpa [canonical, ids] using TypedLayout.Backend.ExactCssHarnessCase.canonical_ids

theorem canonical_ids_nodup :
    canonical.ids.Nodup := by
  simpa [canonical_ids] using FixtureId.all_nodup

theorem canonical_summary :
    canonical.summary =
      { caseCount := 4
      , fixtureIds := [ .exactRow, .paddedLeaf, .framedLeaf, .nestedFrameRow ]
      } := by
  native_decide

end Corpus

namespace Run

/-- Small typed summary for an exact harness run. -/
structure Summary where
  caseCount : Nat
  fixtureIds : List FixtureId
  verdicts : List Verdict
  exactMatchIds : List FixtureId
  mismatchIds : List FixtureId
  exactMatchCount : Nat
  mismatchCount : Nat
  totalIssueCount : Nat
  deriving DecidableEq, Repr

def ofCorpus (corpus : Corpus) : Run :=
  { entries := corpus.baselineCaseReports }

def cases (run : Run) : List Case :=
  run.entries.map CaseReport.case

def reports (run : Run) : List FixtureReport :=
  run.entries.map CaseReport.report

def corpus (run : Run) : Corpus :=
  { cases := run.cases }

def caseCount (run : Run) : Nat :=
  run.entries.length

def fixtureIds (run : Run) : List FixtureId :=
  run.entries.map CaseReport.id

def reportFixtureIds (run : Run) : List FixtureId :=
  run.entries.map (fun entry => entry.report.fixtureId)

def verdicts (run : Run) : List Verdict :=
  run.entries.map CaseReport.verdict

def exactMatchIds (run : Run) : List FixtureId :=
  run.entries.filterMap fun entry =>
    match entry.verdict with
    | .exactMatch => some entry.id
    | .mismatch => none

def mismatchIds (run : Run) : List FixtureId :=
  run.entries.filterMap fun entry =>
    match entry.verdict with
    | .exactMatch => none
    | .mismatch => some entry.id

def exactMatchCount (run : Run) : Nat :=
  run.exactMatchIds.length

def mismatchCount (run : Run) : Nat :=
  run.mismatchIds.length

def totalIssueCount (run : Run) : Nat :=
  run.entries.foldl (fun total entry => total + entry.issueCount) 0

def summary (run : Run) : Summary :=
  { caseCount := run.caseCount
  , fixtureIds := run.fixtureIds
  , verdicts := run.verdicts
  , exactMatchIds := run.exactMatchIds
  , mismatchIds := run.mismatchIds
  , exactMatchCount := run.exactMatchCount
  , mismatchCount := run.mismatchCount
  , totalIssueCount := run.totalIssueCount
  }

theorem ofCorpus_caseCount (corpus : Corpus) :
    (ofCorpus corpus).caseCount = corpus.caseCount := by
  simp [ofCorpus, caseCount, Corpus.caseCount, Corpus.baselineCaseReports]

theorem ofCorpus_fixtureIds (corpus : Corpus) :
    (ofCorpus corpus).fixtureIds = corpus.ids := by
  simp [ofCorpus, fixtureIds, Corpus.ids, Corpus.baselineCaseReports, CaseReport.id,
    Case.id, CaseReport.ofCase]

theorem reportFixtureIds_eq_fixtureIds (run : Run) :
    run.reportFixtureIds = run.fixtureIds := by
  simp [reportFixtureIds, fixtureIds]

theorem corpus_ids_eq_fixtureIds (run : Run) :
    run.corpus.ids = run.fixtureIds := by
  simp [corpus, cases, Corpus.ids, fixtureIds, CaseReport.id]

theorem reports_length_eq_caseCount (run : Run) :
    run.reports.length = run.caseCount := by
  simp [reports, caseCount]

/-- Canonical baseline run for the canonical exact harness corpus. -/
def canonicalBaseline : Run :=
  ofCorpus Corpus.canonical

def canonicalReports : List CaseReport :=
  canonicalBaseline.entries

def canonicalVerdicts : List Verdict :=
  canonicalBaseline.verdicts

theorem canonicalBaseline_fixtureIds :
    canonicalBaseline.fixtureIds = FixtureId.all := by
  simpa [canonicalBaseline] using ofCorpus_fixtureIds Corpus.canonical

theorem canonicalBaseline_reportFixtureIds :
    canonicalBaseline.reportFixtureIds = FixtureId.all := by
  rw [reportFixtureIds_eq_fixtureIds]
  exact canonicalBaseline_fixtureIds

theorem canonicalBaseline_corpus_ids :
    canonicalBaseline.corpus.ids = FixtureId.all := by
  rw [corpus_ids_eq_fixtureIds]
  exact canonicalBaseline_fixtureIds

theorem canonicalVerdicts_allExactMatch :
    canonicalVerdicts =
      [ .exactMatch
      , .exactMatch
      , .exactMatch
      , .exactMatch
      ] := by
  native_decide

theorem canonicalBaseline_summary :
    canonicalBaseline.summary =
      { caseCount := 4
      , fixtureIds := [ .exactRow, .paddedLeaf, .framedLeaf, .nestedFrameRow ]
      , verdicts := [ .exactMatch, .exactMatch, .exactMatch, .exactMatch ]
      , exactMatchIds := [ .exactRow, .paddedLeaf, .framedLeaf, .nestedFrameRow ]
      , mismatchIds := []
      , exactMatchCount := 4
      , mismatchCount := 0
      , totalIssueCount := 0
      } := by
  native_decide

theorem canonicalBaseline_mismatchIds :
    canonicalBaseline.mismatchIds = [] := by
  native_decide

theorem canonicalBaseline_totalIssueCount :
    canonicalBaseline.totalIssueCount = 0 := by
  native_decide

def exactRowBaselineReport : CaseReport :=
  CaseReport.ofCase exactRowCase

def nestedFrameRowBaselineReport : CaseReport :=
  CaseReport.ofCase nestedFrameRowCase

theorem exactRowBaselineReport_verdict :
    exactRowBaselineReport.verdict = .exactMatch := by
  native_decide

theorem nestedFrameRowBaselineReport_fixtureId :
    nestedFrameRowBaselineReport.id = .nestedFrameRow := by
  rfl

end Run

end TypedLayout.Backend.ExactCssHarnessRun
