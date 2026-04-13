import TypedLayout.Backend.ExactCssHarnessCase

namespace TypedLayout.Backend.ExactCssVerdict

open TypedLayout.Core
open TypedLayout.Backend.ExactCss
open TypedLayout.Backend.ExactCssFixtures
open TypedLayout.Backend.ExactCssHarnessCase
open TypedLayout.Backend.ExactCss.Interchange

/-- Top-level exact-fragment verdict for a document comparison/report. -/
inductive Verdict where
  | exactMatch
  | mismatch
  deriving DecidableEq, Repr

namespace Verdict

def ofMatchesExactly : Bool → Verdict
  | true => .exactMatch
  | false => .mismatch

@[simp] theorem ofMatchesExactly_true :
    ofMatchesExactly true = .exactMatch :=
  rfl

@[simp] theorem ofMatchesExactly_false :
    ofMatchesExactly false = .mismatch :=
  rfl

end Verdict

/-- Count summary derived from exact comparison results. -/
structure Counts where
  expected : Nat
  observed : Nat
  paired : Nat
  matched : Nat
  mismatched : Nat
  missing : Nat
  unexpected : Nat
  deriving DecidableEq, Repr

namespace Counts

private structure Running where
  paired : Nat
  matched : Nat
  mismatched : Nat
  missing : Nat
  unexpected : Nat
  deriving DecidableEq, Repr

private def empty : Running :=
  { paired := 0
  , matched := 0
  , mismatched := 0
  , missing := 0
  , unexpected := 0
  }

private def step (running : Running) : TargetResult → Running
  | .paired comparison =>
      if comparison.isMatch then
        { running with
          paired := running.paired + 1
        , matched := running.matched + 1
        }
      else
        { running with
          paired := running.paired + 1
        , mismatched := running.mismatched + 1
        }
  | .missingObservation _ =>
      { running with missing := running.missing + 1 }
  | .unexpectedObservation _ =>
      { running with unexpected := running.unexpected + 1 }

private def ofResults (results : List TargetResult) : Running :=
  results.foldl step empty

def issueCount (counts : Counts) : Nat :=
  counts.mismatched + counts.missing + counts.unexpected

def ofComparisonPayload (payload : ComparisonPayload) : Counts :=
  let running := ofResults payload.results
  { expected := payload.expectedCount
  , observed := payload.observedCount
  , paired := running.paired
  , matched := running.matched
  , mismatched := running.mismatched
  , missing := running.missing
  , unexpected := running.unexpected
  }

def ofComparison (comparison : ExactDocument.ProbeComparison.DocumentComparison) : Counts :=
  ofComparisonPayload (ComparisonPayload.ofComparison comparison)

theorem ofComparisonPayload_expected (payload : ComparisonPayload) :
    (ofComparisonPayload payload).expected = payload.expectedCount :=
  rfl

theorem ofComparisonPayload_observed (payload : ComparisonPayload) :
    (ofComparisonPayload payload).observed = payload.observedCount :=
  rfl

end Counts

/-- Non-matching target-level issue retained in typed form for harness-facing reports. -/
inductive TargetIssue where
  | pairedMismatch (comparison : TargetComparison)
  | missingObservation (expected : ExpectedTarget)
  | unexpectedObservation (observed : ObservedTarget)
  deriving DecidableEq, Repr

namespace TargetIssue

inductive Kind where
  | pairedMismatch
  | missingObservation
  | unexpectedObservation
  deriving DecidableEq, Repr

def kind : TargetIssue → Kind
  | .pairedMismatch _ => .pairedMismatch
  | .missingObservation _ => .missingObservation
  | .unexpectedObservation _ => .unexpectedObservation

def expectedHandle? : TargetIssue → Option TargetHandle
  | .pairedMismatch comparison => some comparison.expected.handle
  | .missingObservation expected => some expected.handle
  | .unexpectedObservation _ => none

def observedHandle? : TargetIssue → Option TargetHandle
  | .pairedMismatch comparison => some comparison.observed.handle
  | .missingObservation _ => none
  | .unexpectedObservation observed => some observed.handle

def primaryHandle : TargetIssue → TargetHandle
  | .pairedMismatch comparison => comparison.expected.handle
  | .missingObservation expected => expected.handle
  | .unexpectedObservation observed => observed.handle

def label (issue : TargetIssue) : ExactDocument.ClassName :=
  issue.primaryHandle.className

def selectorText (issue : TargetIssue) : String :=
  issue.primaryHandle.selectorText

def ofTargetResult : TargetResult → Option TargetIssue
  | .paired comparison =>
      if comparison.isMatch then
        none
      else
        some (.pairedMismatch comparison)
  | .missingObservation expected => some (.missingObservation expected)
  | .unexpectedObservation observed => some (.unexpectedObservation observed)

def ofResults (results : List TargetResult) : List TargetIssue :=
  results.filterMap ofTargetResult

end TargetIssue

/-- Harness-facing typed verdict/report derived from an exact comparison payload. -/
structure Report where
  targetProfile : BlessedCssProfile
  sourceGuarantee : GuaranteeClass
  verdict : Verdict
  counts : Counts
  issues : List TargetIssue
  deriving DecidableEq, Repr

namespace Report

def issueCount (report : Report) : Nat :=
  report.issues.length

def issueLabels (report : Report) : List ExactDocument.ClassName :=
  report.issues.map TargetIssue.label

def issueSelectorTexts (report : Report) : List String :=
  report.issues.map TargetIssue.selectorText

def pairedMismatches (report : Report) : List TargetComparison :=
  report.issues.filterMap fun issue =>
    match issue with
    | .pairedMismatch comparison => some comparison
    | _ => none

def missingObservations (report : Report) : List ExpectedTarget :=
  report.issues.filterMap fun issue =>
    match issue with
    | .missingObservation expected => some expected
    | _ => none

def unexpectedObservations (report : Report) : List ObservedTarget :=
  report.issues.filterMap fun issue =>
    match issue with
    | .unexpectedObservation observed => some observed
    | _ => none

def ofComparisonPayload (payload : ComparisonPayload) : Report :=
  { targetProfile := payload.targetProfile
  , sourceGuarantee := payload.sourceGuarantee
  , verdict := Verdict.ofMatchesExactly payload.matchesExactly
  , counts := Counts.ofComparisonPayload payload
  , issues := TargetIssue.ofResults payload.results
  }

def ofComparison (comparison : ExactDocument.ProbeComparison.DocumentComparison) : Report :=
  ofComparisonPayload (ComparisonPayload.ofComparison comparison)

def ofBundle (bundle : Bundle) : Report :=
  ofComparisonPayload bundle.comparison

theorem ofComparisonPayload_verdict (payload : ComparisonPayload) :
    (ofComparisonPayload payload).verdict = Verdict.ofMatchesExactly payload.matchesExactly := by
  simp [ofComparisonPayload]

theorem ofComparison_verdict
    (comparison : ExactDocument.ProbeComparison.DocumentComparison) :
    (ofComparison comparison).verdict = Verdict.ofMatchesExactly comparison.matchesExactly := by
  calc
    (ofComparison comparison).verdict =
        Verdict.ofMatchesExactly (ComparisonPayload.ofComparison comparison).matchesExactly := by
      simp [ofComparison, ofComparisonPayload]
    _ = Verdict.ofMatchesExactly comparison.matchesExactly := by
      rw [ComparisonPayload.ofComparison_matchesExactly]

end Report

/-- Report paired with stable exact-fixture linkage. -/
structure FixtureReport where
  fixture : FixtureRef
  report : Report
  deriving DecidableEq, Repr

namespace FixtureReport

def fixtureId (report : FixtureReport) : FixtureId :=
  report.fixture.fixtureId

def verdict (report : FixtureReport) : Verdict :=
  report.report.verdict

def counts (report : FixtureReport) : Counts :=
  report.report.counts

def issueLabels (report : FixtureReport) : List ExactDocument.ClassName :=
  report.report.issueLabels

def issueSelectorTexts (report : FixtureReport) : List String :=
  report.report.issueSelectorTexts

def pairedMismatches (report : FixtureReport) : List TargetComparison :=
  report.report.pairedMismatches

def missingObservations (report : FixtureReport) : List ExpectedTarget :=
  report.report.missingObservations

def unexpectedObservations (report : FixtureReport) : List ObservedTarget :=
  report.report.unexpectedObservations

def ofFixtureComparison
    (fixture : Fixture)
    (comparison : ExactDocument.ProbeComparison.DocumentComparison) : FixtureReport :=
  { fixture := FixtureRef.ofFixture fixture
  , report := Report.ofComparison comparison
  }

def ofFixture (fixture : Fixture) : FixtureReport :=
  ofFixtureComparison fixture fixture.comparison

def ofBundle (bundle : Bundle) : FixtureReport :=
  { fixture := bundle.fixture
  , report := Report.ofBundle bundle
  }

def ofCase (case : Case) : FixtureReport :=
  ofBundle case.interchangeBundle

theorem ofCase_fixtureId (case : Case) :
    (ofCase case).fixtureId = case.id := by
  simpa [ofCase, ofBundle, fixtureId] using Case.interchangeBundle_fixtureId case

end FixtureReport

/-- Canonical verdict reports for the canonical exact harness-case corpus. -/
def canonical : List FixtureReport :=
  TypedLayout.Backend.ExactCssHarnessCase.canonical.map FixtureReport.ofCase

def exactRowCaseReport : FixtureReport :=
  FixtureReport.ofCase exactRowCase

def exactRowShiftedFixtureReport : FixtureReport :=
  FixtureReport.ofFixtureComparison exactRowFixture exactRowShiftedComparison

theorem exactRowCaseReport_fixtureId :
    exactRowCaseReport.fixtureId = .exactRow := by
  simpa [exactRowCaseReport] using FixtureReport.ofCase_fixtureId exactRowCase

theorem exactRowCaseReport_verdict :
    exactRowCaseReport.verdict = .exactMatch := by
  native_decide

theorem exactRowCaseReport_counts :
    exactRowCaseReport.counts =
      { expected := 4
      , observed := 4
      , paired := 4
      , matched := 4
      , mismatched := 0
      , missing := 0
      , unexpected := 0
      } := by
  native_decide

theorem exactRowCaseReport_issueLabels :
    ExactDocument.ClassName.serials exactRowCaseReport.issueLabels = [] := by
  native_decide

theorem exactRowShiftedFixtureReport_verdict :
    exactRowShiftedFixtureReport.verdict = .mismatch := by
  native_decide

theorem exactRowShiftedFixtureReport_counts :
    exactRowShiftedFixtureReport.counts =
      { expected := 4
      , observed := 4
      , paired := 4
      , matched := 3
      , mismatched := 1
      , missing := 0
      , unexpected := 0
      } := by
  native_decide

theorem exactRowShiftedFixtureReport_issueLabels :
    ExactDocument.ClassName.serials exactRowShiftedFixtureReport.issueLabels = [1] := by
  native_decide

namespace _root_.TypedLayout.Backend.ExactCssHarnessCase.Case

def verdictReport (case : Case) : TypedLayout.Backend.ExactCssVerdict.FixtureReport :=
  TypedLayout.Backend.ExactCssVerdict.FixtureReport.ofCase case

theorem verdictReport_fixtureId (case : Case) :
    (verdictReport case).fixtureId = case.id := by
  exact TypedLayout.Backend.ExactCssVerdict.FixtureReport.ofCase_fixtureId case

end _root_.TypedLayout.Backend.ExactCssHarnessCase.Case

end TypedLayout.Backend.ExactCssVerdict
