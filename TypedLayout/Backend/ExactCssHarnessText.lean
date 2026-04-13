import TypedLayout.Backend.ExactCssHarnessProtocol

open TypedLayout.Core
open TypedLayout.Backend.ExactCss
open TypedLayout.Backend.ExactCssFixtures
open TypedLayout.Backend.ExactCssHarnessCase
open TypedLayout.Backend.ExactCssVerdict
open TypedLayout.Backend.ExactCssHarnessRun
open TypedLayout.Backend.ExactCssHarnessProtocol
open TypedLayout.Backend.ExactCss.Interchange
open TypedLayout.Backend.ExactCss.Interchange.Text

namespace TypedLayout.Backend.ExactCss
namespace ExactDocument
namespace RenderedPage

/-- Render a standalone exact page to deterministic outer-boundary text. -/
def render (page : RenderedPage) : String :=
  object [("html", string page.html)]

end RenderedPage
end ExactDocument
end TypedLayout.Backend.ExactCss

namespace TypedLayout.Backend.ExactCssVerdict

namespace Verdict

/-- Render a typed exact-fragment verdict to deterministic outer-boundary text. -/
def render : Verdict → String
  | .exactMatch => tagged "exactMatch"
  | .mismatch => tagged "mismatch"

end Verdict

namespace Counts

/-- Render typed exact-fragment comparison counts to deterministic outer-boundary text. -/
def render (counts : Counts) : String :=
  object
    [ ("expected", nat counts.expected)
    , ("observed", nat counts.observed)
    , ("paired", nat counts.paired)
    , ("matched", nat counts.matched)
    , ("mismatched", nat counts.mismatched)
    , ("missing", nat counts.missing)
    , ("unexpected", nat counts.unexpected)
    , ("issueCount", nat counts.issueCount)
    ]

end Counts

namespace TargetIssue

/-- Render a typed exact-fragment target issue to deterministic outer-boundary text. -/
def render : TargetIssue → String
  | issue@(.pairedMismatch comparison) =>
      tagged "pairedMismatch"
        [ ("label", renderClassName issue.label)
        , ("selectorText", string issue.selectorText)
        , ("comparison", comparison.render)
        ]
  | issue@(.missingObservation expected) =>
      tagged "missingObservation"
        [ ("label", renderClassName issue.label)
        , ("selectorText", string issue.selectorText)
        , ("expected", expected.render)
        ]
  | issue@(.unexpectedObservation observed) =>
      tagged "unexpectedObservation"
        [ ("label", renderClassName issue.label)
        , ("selectorText", string issue.selectorText)
        , ("observed", observed.render)
        ]

end TargetIssue

namespace Report

/-- Render a typed exact-fragment verdict report to deterministic outer-boundary text. -/
def render (report : Report) : String :=
  object
    [ ("targetProfile", renderBlessedCssProfile report.targetProfile)
    , ("sourceGuarantee", renderGuaranteeClass report.sourceGuarantee)
    , ("verdict", report.verdict.render)
    , ("counts", report.counts.render)
    , ("issues", array (report.issues.map TargetIssue.render))
    ]

end Report

namespace FixtureReport

/-- Render a fixture-linked exact-fragment verdict report to deterministic text. -/
def render (report : FixtureReport) : String :=
  object
    [ ("fixture", report.fixture.render)
    , ("report", report.report.render)
    ]

end FixtureReport

end TypedLayout.Backend.ExactCssVerdict

private def renderFixtureIds (fixtureIds : List FixtureId) : String :=
  array (fixtureIds.map renderFixtureId)

private def renderVerdicts (verdicts : List Verdict) : String :=
  array (verdicts.map Verdict.render)

namespace TypedLayout.Backend.ExactCssHarnessProtocol

namespace Request

/-- Render a typed exact harness request to deterministic outer-boundary text. -/
def render (request : Request) : String :=
  object
    [ ("fixture", request.fixture.render)
    , ("renderedPage", request.renderedPage.render)
    , ("expectations", request.expectations.render)
    , ("probePlan", request.probePlan.render)
    ]

/-- Render an ordered request list to deterministic outer-boundary text. -/
def renderList (requests : List Request) : String :=
  array (requests.map render)

/-- Deterministic outer-boundary text for the canonical exact request list. -/
def renderCanonical : String :=
  renderList canonicalRequests

theorem exactRow_render_ne_empty :
    TypedLayout.Backend.ExactCssHarnessProtocol.exactRowRequest.render ≠ "" := by
  native_decide

theorem renderCanonical_ne_empty :
    renderCanonical ≠ "" := by
  native_decide

end Request

namespace Response

/-- Render a typed exact harness response to deterministic outer-boundary text. -/
def render (response : Response) : String :=
  object
    [ ("observation", response.observation.render)
    , ("comparison", response.comparison.render)
    , ("report", response.report.render)
    ]

/-- Render an ordered response list to deterministic outer-boundary text. -/
def renderList (responses : List Response) : String :=
  array (responses.map render)

/-- Deterministic outer-boundary text for the canonical exact response list. -/
def renderCanonical : String :=
  renderList canonicalResponses

theorem exactRow_render_ne_empty :
    TypedLayout.Backend.ExactCssHarnessProtocol.exactRowResponse.render ≠ "" := by
  native_decide

theorem renderCanonical_ne_empty :
    renderCanonical ≠ "" := by
  native_decide

end Response

namespace Handoff

/-- Render a coherent exact request/response handoff to deterministic text. -/
def render (handoff : Handoff) : String :=
  object
    [ ("fixtureId", renderFixtureId handoff.fixtureId)
    , ("verdict", handoff.verdict.render)
    , ("matchesExactly", bool handoff.matchesExactly)
    , ("issueCount", nat handoff.issueCount)
    , ("request", handoff.request.render)
    , ("response", handoff.response.render)
    ]

/-- Render an ordered handoff list to deterministic outer-boundary text. -/
def renderList (handoffs : List Handoff) : String :=
  array (handoffs.map render)

/-- Deterministic outer-boundary text for the canonical exact handoff list. -/
def renderCanonical : String :=
  renderList canonicalHandoffs

theorem exactRow_render_ne_empty :
    TypedLayout.Backend.ExactCssHarnessProtocol.exactRowHandoff.render ≠ "" := by
  native_decide

theorem renderCanonical_ne_empty :
    renderCanonical ≠ "" := by
  native_decide

end Handoff

end TypedLayout.Backend.ExactCssHarnessProtocol

namespace TypedLayout.Backend.ExactCssHarnessRun

namespace Corpus
namespace Summary

/-- Render a typed exact harness corpus summary to deterministic outer-boundary text. -/
def render (summary : Corpus.Summary) : String :=
  object
    [ ("caseCount", nat summary.caseCount)
    , ("fixtureIds", renderFixtureIds summary.fixtureIds)
    ]

end Summary

/-- Render the summary of a typed exact harness corpus to deterministic text. -/
def renderSummary (corpus : Corpus) : String :=
  corpus.summary.render

/-- Deterministic outer-boundary text for the canonical exact corpus summary. -/
def renderCanonicalSummary : String :=
  canonical.renderSummary

theorem renderCanonicalSummary_eq_expected :
    renderCanonicalSummary =
      "{\"caseCount\":4,\"fixtureIds\":[\"exactRow\",\"paddedLeaf\",\"framedLeaf\",\"nestedFrameRow\"]}" := by
  native_decide

end Corpus

namespace Run
namespace Summary

/-- Render a typed exact harness run summary to deterministic outer-boundary text. -/
def render (summary : TypedLayout.Backend.ExactCssHarnessRun.Run.Summary) : String :=
  object
    [ ("caseCount", nat summary.caseCount)
    , ("fixtureIds", renderFixtureIds summary.fixtureIds)
    , ("verdicts", renderVerdicts summary.verdicts)
    , ("exactMatchIds", renderFixtureIds summary.exactMatchIds)
    , ("mismatchIds", renderFixtureIds summary.mismatchIds)
    , ("exactMatchCount", nat summary.exactMatchCount)
    , ("mismatchCount", nat summary.mismatchCount)
    , ("totalIssueCount", nat summary.totalIssueCount)
    ]

end Summary

/-- Render the summary of a typed exact harness run to deterministic text. -/
def renderSummary (run : Run) : String :=
  run.summary.render

/-- Deterministic outer-boundary text for the canonical exact run summary. -/
def renderCanonicalSummary : String :=
  canonicalBaseline.renderSummary

/-- Render a canonical exact run as a deterministic harness transcript. -/
def renderTranscript (run : Run) : String :=
  object
    [ ("corpusSummary", run.corpus.renderSummary)
    , ("runSummary", run.renderSummary)
    , ("handoffs", Handoff.renderList (handoffsOfRun run))
    ]

/-- Deterministic outer-boundary text for the canonical exact run transcript. -/
def renderCanonicalTranscript : String :=
  canonicalBaseline.renderTranscript

theorem renderCanonicalSummary_eq_expected :
    renderCanonicalSummary =
      "{\"caseCount\":4,\"fixtureIds\":[\"exactRow\",\"paddedLeaf\",\"framedLeaf\",\"nestedFrameRow\"],\"verdicts\":[{\"tag\":\"exactMatch\"},{\"tag\":\"exactMatch\"},{\"tag\":\"exactMatch\"},{\"tag\":\"exactMatch\"}],\"exactMatchIds\":[\"exactRow\",\"paddedLeaf\",\"framedLeaf\",\"nestedFrameRow\"],\"mismatchIds\":[],\"exactMatchCount\":4,\"mismatchCount\":0,\"totalIssueCount\":0}" := by
  native_decide

theorem renderCanonicalTranscript_ne_empty :
    renderCanonicalTranscript ≠ "" := by
  native_decide

end Run

end TypedLayout.Backend.ExactCssHarnessRun
