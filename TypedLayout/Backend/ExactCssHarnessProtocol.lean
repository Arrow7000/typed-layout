import TypedLayout.Backend.ExactCssHarnessRun

namespace TypedLayout.Backend.ExactCssHarnessProtocol

open TypedLayout.Core
open TypedLayout.Backend.ExactCss
open TypedLayout.Backend.ExactCssFixtures
open TypedLayout.Backend.ExactCssHarnessCase
open TypedLayout.Backend.ExactCssVerdict
open TypedLayout.Backend.ExactCssHarnessRun
open TypedLayout.Backend.ExactCss.Interchange

/-- Typed exact-fragment harness request for one canonical case.

The request keeps the future harness boundary typed: stable fixture linkage,
rendered standalone page output, source-side expectations, and the typed probe plan
all travel together without introducing IO or ad-hoc request strings. -/
structure Request where
  fixture : FixtureRef
  renderedPage : ExactDocument.RenderedPage
  expectations : ExpectationPayload
  probePlan : ProbePlanPayload
  deriving DecidableEq, Repr

namespace Request

def fixtureId (request : Request) : FixtureId :=
  request.fixture.fixtureId

def targetProfile (request : Request) : BlessedCssProfile :=
  request.probePlan.targetProfile

def sourceGuarantee (request : Request) : GuaranteeClass :=
  request.probePlan.sourceGuarantee

def nodeCount (request : Request) : Nat :=
  request.probePlan.nodeCount

def labels (request : Request) : List ExactDocument.ClassName :=
  request.probePlan.labels

def ofCase (case : Case) : Request :=
  { fixture := case.fixtureRef
  , renderedPage := case.renderedPage
  , expectations := ExpectationPayload.ofExpectation case.expectations
  , probePlan := ProbePlanPayload.ofPlan case.probePlan
  }

def ofRunEntry (entry : CaseReport) : Request :=
  ofCase entry.case

@[simp] theorem ofCase_fixtureId (case : Case) :
    (ofCase case).fixtureId = case.id := by
  simpa [ofCase, fixtureId] using Case.fixtureRef_fixtureId case

@[simp] theorem ofCase_targetProfile (case : Case) :
    (ofCase case).targetProfile = case.probePlan.targetProfile :=
  rfl

@[simp] theorem ofCase_sourceGuarantee (case : Case) :
    (ofCase case).sourceGuarantee = case.probePlan.sourceGuarantee := by
  rfl

theorem ofCase_labels (case : Case) :
    (ofCase case).labels = case.probePlan.labels := by
  simpa [ofCase, labels] using ProbePlanPayload.ofPlan_labels case.probePlan

theorem ofCase_nodeCount (case : Case) :
    (ofCase case).nodeCount = case.probePlan.nodeCount := by
  simpa [ofCase, nodeCount] using ProbePlanPayload.ofPlan_nodeCount case.probePlan

theorem ofCase_expectationLabels_eq_labels (case : Case) :
    (ofCase case).expectations.labels = (ofCase case).labels := by
  calc
    (ofCase case).expectations.labels = case.expectations.labels := by
      simpa [ofCase] using ExpectationPayload.ofExpectation_labels case.expectations
    _ = case.probePlan.labels := by
      exact case.expectationLabels_eq_probePlanLabels
    _ = (ofCase case).labels := by
      symm
      exact ofCase_labels case

theorem ofCase_expectationNodeCount_eq_nodeCount (case : Case) :
    (ofCase case).expectations.nodeCount = (ofCase case).nodeCount := by
  have hLengths := congrArg List.length (ofCase_expectationLabels_eq_labels case)
  simpa [labels, nodeCount, ExpectationPayload.labels_length, ProbePlanPayload.labels_length]
    using hLengths

@[simp] theorem ofRunEntry_fixtureId (entry : CaseReport) :
    (ofRunEntry entry).fixtureId = entry.id := by
  rfl

end Request

/-- Typed exact-fragment harness response for one canonical case.

The response keeps the harness result typed as an observed document, a typed exact
comparison payload, and a fixture-linked verdict/report bundle. -/
structure Response where
  observation : ObservationPayload
  comparison : ComparisonPayload
  report : FixtureReport
  deriving DecidableEq, Repr

namespace Response

def fixture (response : Response) : FixtureRef :=
  response.report.fixture

def fixtureId (response : Response) : FixtureId :=
  response.report.fixtureId

def verdict (response : Response) : Verdict :=
  response.report.verdict

def counts (response : Response) : Counts :=
  response.report.counts

def issueCount (response : Response) : Nat :=
  response.report.report.issueCount

def ofCase (case : Case) : Response :=
  { observation := ObservationPayload.ofObservation case.baselineObservation
  , comparison := ComparisonPayload.ofComparison case.baselineComparison
  , report := FixtureReport.ofCase case
  }

def ofRunEntry (entry : CaseReport) : Response :=
  ofCase entry.case

@[simp] theorem ofCase_fixtureId (case : Case) :
    (ofCase case).fixtureId = case.id := by
  simpa [ofCase, fixtureId] using FixtureReport.ofCase_fixtureId case

theorem ofCase_observationLabels_eq_probePlanLabels (case : Case) :
    (ofCase case).observation.labels = case.probePlan.labels := by
  calc
    (ofCase case).observation.labels = case.baselineObservation.labels := by
      simpa [ofCase] using ObservationPayload.ofObservation_labels case.baselineObservation
    _ = case.probePlan.labels := by
      exact case.observationLabels_eq_probePlanLabels

theorem ofCase_comparisonTargetProfile_eq_probePlanTargetProfile (case : Case) :
    (ofCase case).comparison.targetProfile = case.probePlan.targetProfile :=
  rfl

theorem ofCase_comparisonSourceGuarantee_eq_probePlanSourceGuarantee (case : Case) :
    (ofCase case).comparison.sourceGuarantee = case.probePlan.sourceGuarantee := by
  simpa [ofCase, Case.baselineComparison] using
    ExactDocument.ProbeComparison.DocumentComparison.compare_sourceGuarantee
      case.probePlan case.baselineObservation

theorem ofCase_comparisonExpectedCount_eq_probePlanNodeCount (case : Case) :
    (ofCase case).comparison.expectedCount = case.probePlan.nodeCount := by
  simpa [ofCase, Case.baselineComparison] using
    ExactDocument.ProbeComparison.DocumentComparison.compare_expectedCount
      case.probePlan case.baselineObservation

theorem ofCase_comparisonObservedCount_eq_observationNodeCount (case : Case) :
    (ofCase case).comparison.observedCount = (ofCase case).observation.nodeCount := by
  calc
    (ofCase case).comparison.observedCount = case.baselineObservation.nodeCount := by
      simpa [ofCase, Case.baselineComparison] using
        ExactDocument.ProbeComparison.DocumentComparison.compare_observedCount
          case.probePlan case.baselineObservation
    _ = (ofCase case).observation.nodeCount := by
      symm
      simpa [ofCase] using ObservationPayload.ofObservation_nodeCount case.baselineObservation

theorem ofCase_matchesExactly (case : Case) :
    (ofCase case).comparison.matchesExactly = true := by
  calc
    (ofCase case).comparison.matchesExactly = case.baselineComparison.matchesExactly := by
      simpa [ofCase] using ComparisonPayload.ofComparison_matchesExactly case.baselineComparison
    _ = true := by
      exact case.baselineComparison_matchesExactly

theorem ofCase_verdict_eq_matchesExactly (case : Case) :
    (ofCase case).verdict = Verdict.ofMatchesExactly (ofCase case).comparison.matchesExactly := by
  calc
    (ofCase case).verdict = Verdict.ofMatchesExactly true := by
      simp [verdict, ofCase, FixtureReport.ofCase, FixtureReport.ofBundle, FixtureReport.verdict,
        Report.ofBundle, Report.ofComparisonPayload, Case.interchangeComparison_matchesExactly]
    _ = Verdict.ofMatchesExactly (ofCase case).comparison.matchesExactly := by
      rw [ofCase_matchesExactly case]

theorem ofCase_counts_eq_comparisonCounts (case : Case) :
    (ofCase case).counts = Counts.ofComparisonPayload (ofCase case).comparison := by
  rfl

@[simp] theorem ofRunEntry_fixtureId (entry : CaseReport) :
    (ofRunEntry entry).fixtureId = entry.id := by
  rfl

end Response

/-- Coherent typed exact request/response handoff for one canonical case.

This records the small protocol invariants that the current exact harness corpus
already satisfies before any external harness or browser automation exists. -/
structure Handoff where
  request : Request
  response : Response
  fixtureId_eq : response.fixtureId = request.fixtureId
  requestExpectationLabels_eqRequestLabels :
    request.expectations.labels = request.labels
  requestExpectationNodeCount_eqRequestNodeCount :
    request.expectations.nodeCount = request.nodeCount
  responseObservationLabels_eqRequestLabels :
    response.observation.labels = request.labels
  responseComparisonTargetProfile_eqRequestTargetProfile :
    response.comparison.targetProfile = request.targetProfile
  responseComparisonSourceGuarantee_eqRequestSourceGuarantee :
    response.comparison.sourceGuarantee = request.sourceGuarantee
  responseComparisonExpectedCount_eqRequestNodeCount :
    response.comparison.expectedCount = request.nodeCount
  responseComparisonObservedCount_eqObservationNodeCount :
    response.comparison.observedCount = response.observation.nodeCount
  responseVerdict_eqComparisonMatches :
    response.verdict = Verdict.ofMatchesExactly response.comparison.matchesExactly
  responseCounts_eqComparisonCounts :
    response.counts = Counts.ofComparisonPayload response.comparison

namespace Handoff

def fixtureId (handoff : Handoff) : FixtureId :=
  handoff.request.fixtureId

def verdict (handoff : Handoff) : Verdict :=
  handoff.response.verdict

def matchesExactly (handoff : Handoff) : Bool :=
  handoff.response.comparison.matchesExactly

def issueCount (handoff : Handoff) : Nat :=
  handoff.response.issueCount

def ofCase (case : Case) : Handoff :=
  { request := Request.ofCase case
  , response := Response.ofCase case
  , fixtureId_eq := by
      rw [Response.ofCase_fixtureId, Request.ofCase_fixtureId]
  , requestExpectationLabels_eqRequestLabels :=
      Request.ofCase_expectationLabels_eq_labels case
  , requestExpectationNodeCount_eqRequestNodeCount :=
      Request.ofCase_expectationNodeCount_eq_nodeCount case
  , responseObservationLabels_eqRequestLabels := by
      calc
        (Response.ofCase case).observation.labels = case.probePlan.labels := by
          exact Response.ofCase_observationLabels_eq_probePlanLabels case
        _ = (Request.ofCase case).labels := by
          symm
          exact Request.ofCase_labels case
  , responseComparisonTargetProfile_eqRequestTargetProfile := by
      calc
        (Response.ofCase case).comparison.targetProfile = case.probePlan.targetProfile := by
          exact Response.ofCase_comparisonTargetProfile_eq_probePlanTargetProfile case
        _ = (Request.ofCase case).targetProfile := by
          symm
          exact Request.ofCase_targetProfile case
  , responseComparisonSourceGuarantee_eqRequestSourceGuarantee := by
      calc
        (Response.ofCase case).comparison.sourceGuarantee = case.probePlan.sourceGuarantee := by
          exact Response.ofCase_comparisonSourceGuarantee_eq_probePlanSourceGuarantee case
        _ = (Request.ofCase case).sourceGuarantee := by
          symm
          exact Request.ofCase_sourceGuarantee case
  , responseComparisonExpectedCount_eqRequestNodeCount := by
      calc
        (Response.ofCase case).comparison.expectedCount = case.probePlan.nodeCount := by
          exact Response.ofCase_comparisonExpectedCount_eq_probePlanNodeCount case
        _ = (Request.ofCase case).nodeCount := by
          symm
          exact Request.ofCase_nodeCount case
  , responseComparisonObservedCount_eqObservationNodeCount :=
      Response.ofCase_comparisonObservedCount_eq_observationNodeCount case
  , responseVerdict_eqComparisonMatches :=
      Response.ofCase_verdict_eq_matchesExactly case
  , responseCounts_eqComparisonCounts :=
      Response.ofCase_counts_eq_comparisonCounts case
  }

def ofRunEntry (entry : CaseReport) : Handoff :=
  ofCase entry.case

theorem verdict_eq_matchesExactly (handoff : Handoff) :
    handoff.verdict = Verdict.ofMatchesExactly handoff.matchesExactly :=
  handoff.responseVerdict_eqComparisonMatches

theorem counts_eq_comparisonCounts (handoff : Handoff) :
    handoff.response.counts = Counts.ofComparisonPayload handoff.response.comparison :=
  handoff.responseCounts_eqComparisonCounts

@[simp] theorem ofCase_fixtureId (case : Case) :
    (ofCase case).fixtureId = case.id :=
  rfl

@[simp] theorem ofRunEntry_fixtureId (entry : CaseReport) :
    (ofRunEntry entry).fixtureId = entry.id := by
  rfl

end Handoff

def requestsOfCases (cases : List Case) : List Request :=
  cases.map Request.ofCase

def requestsOfCorpus (corpus : Corpus) : List Request :=
  requestsOfCases corpus.cases

def responsesOfEntries (entries : List CaseReport) : List Response :=
  entries.map Response.ofRunEntry

def responsesOfRun (run : Run) : List Response :=
  responsesOfEntries run.entries

def handoffsOfCases (cases : List Case) : List Handoff :=
  cases.map Handoff.ofCase

def handoffsOfRun (run : Run) : List Handoff :=
  run.entries.map Handoff.ofRunEntry

theorem requestsOfCorpus_length_eq_caseCount (corpus : Corpus) :
    (requestsOfCorpus corpus).length = corpus.caseCount := by
  simp [requestsOfCorpus, requestsOfCases, Corpus.caseCount]

theorem requestsOfCorpus_fixtureIds (corpus : Corpus) :
    (requestsOfCorpus corpus).map Request.fixtureId = corpus.ids := by
  simp [requestsOfCorpus, requestsOfCases, Corpus.ids]

theorem responsesOfRun_length_eq_caseCount (run : Run) :
    (responsesOfRun run).length = run.caseCount := by
  simp [responsesOfRun, responsesOfEntries, Run.caseCount]

theorem responsesOfRun_fixtureIds (run : Run) :
    (responsesOfRun run).map Response.fixtureId = run.fixtureIds := by
  simp [responsesOfRun, responsesOfEntries, Run.fixtureIds]

theorem handoffsOfRun_length_eq_caseCount (run : Run) :
    (handoffsOfRun run).length = run.caseCount := by
  simp [handoffsOfRun, Run.caseCount]

theorem handoffsOfRun_fixtureIds (run : Run) :
    (handoffsOfRun run).map Handoff.fixtureId = run.fixtureIds := by
  simp [handoffsOfRun, Run.fixtureIds]

/-- Canonical request list aligned with the canonical exact harness corpus. -/
def canonicalRequests : List Request :=
  requestsOfCorpus Corpus.canonical

/-- Canonical response list aligned with the canonical exact baseline run. -/
def canonicalResponses : List Response :=
  responsesOfRun Run.canonicalBaseline

/-- Canonical coherent request/response handoffs for the current exact corpus. -/
def canonicalHandoffs : List Handoff :=
  handoffsOfRun Run.canonicalBaseline

def exactRowRequest : Request :=
  Request.ofCase exactRowCase

def exactRowResponse : Response :=
  Response.ofCase exactRowCase

def exactRowHandoff : Handoff :=
  Handoff.ofCase exactRowCase

theorem canonicalRequests_fixtureIds :
    canonicalRequests.map Request.fixtureId = FixtureId.all := by
  simpa [canonicalRequests] using requestsOfCorpus_fixtureIds Corpus.canonical

theorem canonicalResponses_fixtureIds :
    canonicalResponses.map Response.fixtureId = FixtureId.all := by
  simpa [canonicalResponses] using responsesOfRun_fixtureIds Run.canonicalBaseline

theorem canonicalHandoffs_fixtureIds :
    canonicalHandoffs.map Handoff.fixtureId = FixtureId.all := by
  simpa [canonicalHandoffs] using handoffsOfRun_fixtureIds Run.canonicalBaseline

theorem exactRowRequest_fixtureId :
    exactRowRequest.fixtureId = .exactRow := by
  rfl

theorem exactRowResponse_verdict :
    exactRowResponse.verdict = .exactMatch := by
  calc
    exactRowResponse.verdict = Verdict.ofMatchesExactly exactRowResponse.comparison.matchesExactly := by
      simpa [exactRowResponse] using Response.ofCase_verdict_eq_matchesExactly exactRowCase
    _ = .exactMatch := by
      simp [exactRowResponse, Response.ofCase_matchesExactly exactRowCase]

theorem exactRowHandoff_matchesExactly :
    exactRowHandoff.matchesExactly = true := by
  simpa [exactRowHandoff, Handoff.matchesExactly, exactRowResponse] using
    Response.ofCase_matchesExactly exactRowCase

end TypedLayout.Backend.ExactCssHarnessProtocol
