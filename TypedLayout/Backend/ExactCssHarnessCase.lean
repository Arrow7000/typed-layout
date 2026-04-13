import TypedLayout.Backend.ExactCssInterchangeText

namespace TypedLayout.Backend.ExactCssHarnessCase

open TypedLayout.Backend.ExactCss
open TypedLayout.Backend.ExactCssFixtures
open TypedLayout.Backend.ExactCssManifest
open TypedLayout.Backend.ExactCss.Interchange

/-- Typed harness-case bundle for one exact fixture.

The case keeps a canonical exact fixture as the single source of truth and derives
every harness-facing view from there: export identity, rendered standalone page,
exact expectations/probe data, seeded baseline observation/comparison, and the
outer-boundary interchange bundle/text. -/
structure Case where
  fixture : Fixture

namespace Case

def ofFixture (fixture : Fixture) : Case :=
  { fixture := fixture }

def ofFixtureId (fixtureId : FixtureId) : Case :=
  ofFixture (TypedLayout.Backend.ExactCssFixtures.fixture fixtureId)

def ofRenderedFixtureExport (entry : RenderedFixtureExport) : Case :=
  ofFixture entry.fixture

def ofManifestEntry (entry : RenderedFixtureExport) : Case :=
  ofRenderedFixtureExport entry

def id (case : Case) : FixtureId :=
  case.fixture.id

def renderedExport (case : Case) : RenderedFixtureExport :=
  RenderedFixtureExport.ofFixture case.fixture

def names (case : Case) : ExportNames :=
  case.renderedExport.names

def renderedPage (case : Case) : ExactDocument.RenderedPage :=
  case.renderedExport.renderedPage

def renderPage (case : Case) : String :=
  case.renderedExport.renderPage

def expectations (case : Case) : ExactDocument.Fidelity.DocumentExpectation :=
  case.fixture.expectations

def probePlan (case : Case) : ExactDocument.ProbePlan.Plan :=
  case.fixture.probePlan

def baselineObservation (case : Case) : ExactDocument.ProbeObservation.Document :=
  case.fixture.observation

def baselineComparison (case : Case) : ExactDocument.ProbeComparison.DocumentComparison :=
  case.fixture.comparison

def fixtureRef (case : Case) : FixtureRef :=
  FixtureRef.ofRenderedFixtureExport case.renderedExport

def interchangeBundle (case : Case) : Bundle :=
  Bundle.ofFixture case.fixture

def interchangeText (case : Case) : String :=
  case.interchangeBundle.render

theorem ofFixture_id (fixture : Fixture) :
    (ofFixture fixture).id = fixture.id :=
  rfl

theorem ofFixtureId_id (fixtureId : FixtureId) :
    (ofFixtureId fixtureId).id = fixtureId := by
  cases fixtureId <;> rfl

theorem ofRenderedFixtureExport_id (entry : RenderedFixtureExport) :
    (ofRenderedFixtureExport entry).id = entry.id :=
  rfl

theorem renderedExport_id (case : Case) :
    case.renderedExport.id = case.id := by
  simpa [renderedExport, id] using RenderedFixtureExport.ofFixture_id case.fixture

theorem names_eq_exportNames (case : Case) :
    case.names = case.id.exportNames := by
  simpa [names, renderedExport, id] using
    RenderedFixtureExport.ofFixture_names case.fixture

theorem names_slug (case : Case) :
    case.names.slug = case.id.slug := by
  rw [case.names_eq_exportNames]
  exact TypedLayout.Backend.ExactCssFixtures.FixtureId.exportNames_slug case.id

theorem renderedPage_eq_fixture_renderedPage (case : Case) :
    case.renderedPage = case.fixture.renderedPage := by
  simpa [renderedPage, renderedExport] using
    RenderedFixtureExport.ofFixture_renderedPage case.fixture

theorem renderPage_eq_fixture_renderPage (case : Case) :
    case.renderPage = case.fixture.renderPage := by
  simpa [renderPage, renderedExport] using
    RenderedFixtureExport.ofFixture_renderPage case.fixture

theorem expectationLabels_eq_probePlanLabels (case : Case) :
    case.expectations.labels = case.probePlan.labels := by
  simpa [expectations, probePlan] using
    (Fixture.probePlan_labels_eq_expectation_labels case.fixture).symm

theorem observationLabels_eq_probePlanLabels (case : Case) :
    case.baselineObservation.labels = case.probePlan.labels := by
  simpa [baselineObservation, probePlan] using
    Fixture.observation_labels_eq_probePlan_labels case.fixture

theorem baselineComparison_matchesExactly (case : Case) :
    case.baselineComparison.matchesExactly = true := by
  simpa [baselineComparison] using Fixture.comparison_matchesExactly case.fixture

theorem fixtureRef_fixtureId (case : Case) :
    case.fixtureRef.fixtureId = case.id := by
  simpa [fixtureRef, renderedExport, id] using
    FixtureRef.ofRenderedFixtureExport_fixtureId case.renderedExport

theorem interchangeBundle_fixtureId (case : Case) :
    case.interchangeBundle.fixture.fixtureId = case.id := by
  simpa [interchangeBundle, id] using Bundle.ofFixture_fixtureId case.fixture

theorem interchangeBundle_slug_eq_names_slug (case : Case) :
    case.interchangeBundle.fixture.slug = case.names.slug := by
  calc
    case.interchangeBundle.fixture.slug = case.id.slug := by
      simpa [interchangeBundle, id] using Bundle.ofFixture_slug case.fixture
    _ = case.names.slug := by
      symm
      exact case.names_slug

theorem interchangeExpectationLabels_eqProbePlanLabels (case : Case) :
    case.interchangeBundle.expectations.labels = case.interchangeBundle.probePlan.labels := by
  simpa [interchangeBundle] using
    Bundle.ofFixture_expectationLabels_eq_probePlanLabels case.fixture

theorem interchangeObservationLabels_eqProbePlanLabels (case : Case) :
    case.interchangeBundle.observation.labels = case.interchangeBundle.probePlan.labels := by
  simpa [interchangeBundle] using
    Bundle.ofFixture_observationLabels_eq_probePlanLabels case.fixture

theorem interchangeComparison_matchesExactly (case : Case) :
    case.interchangeBundle.comparison.matchesExactly = true := by
  simpa [interchangeBundle] using
    Bundle.ofFixture_comparison_matchesExactly case.fixture

end Case

/-- Canonical harness case for a canonical exact fixture id. -/
def fixtureCase : FixtureId → Case
  | fixtureId => Case.ofFixtureId fixtureId

/-- Canonical harness-case corpus aligned with the canonical exact export manifest. -/
def canonical : List Case :=
  TypedLayout.Backend.ExactCssManifest.canonical.entries.map Case.ofManifestEntry

def exactRowCase : Case :=
  fixtureCase .exactRow

def paddedLeafCase : Case :=
  fixtureCase .paddedLeaf

def framedLeafCase : Case :=
  fixtureCase .framedLeaf

def nestedFrameRowCase : Case :=
  fixtureCase .nestedFrameRow

def interchangeBundles (cases : List Case) : List Bundle :=
  cases.map Case.interchangeBundle

def renderInterchange (cases : List Case) : String :=
  Bundle.renderList (interchangeBundles cases)

def renderCanonical : String :=
  renderInterchange canonical

theorem canonical_ids :
    canonical.map Case.id = FixtureId.all := by
  simpa [canonical, TypedLayout.Backend.ExactCssManifest.canonical,
    Case.ofManifestEntry, Case.ofRenderedFixtureExport, Case.ofFixture, Case.id] using
    TypedLayout.Backend.ExactCssManifest.all_ids

theorem canonical_interchangeBundles :
    interchangeBundles canonical = Bundle.canonical := by
  native_decide

theorem renderCanonical_eq_interchange_renderCanonical :
    renderCanonical = Bundle.renderCanonical := by
  rw [renderCanonical, renderInterchange, canonical_interchangeBundles, Bundle.renderCanonical]

theorem renderCanonical_ne_empty :
    renderCanonical ≠ "" := by
  simpa [renderCanonical_eq_interchange_renderCanonical] using Bundle.renderCanonical_ne_empty

theorem exactRowCase_renderPage :
    exactRowCase.renderPage = exactRowFixture.renderPage := by
  exact Case.renderPage_eq_fixture_renderPage exactRowCase

theorem exactRowCase_standalonePageHtmlFile :
    exactRowCase.names.standalonePageHtmlFile = "exact-row.page.html" := by
  native_decide

theorem exactRowCase_matchesExactly :
    exactRowCase.baselineComparison.matchesExactly = true := by
  exact Case.baselineComparison_matchesExactly exactRowCase

theorem exactRowCase_interchangeMatchesExactly :
    exactRowCase.interchangeBundle.comparison.matchesExactly = true := by
  exact Case.interchangeComparison_matchesExactly exactRowCase

end TypedLayout.Backend.ExactCssHarnessCase
