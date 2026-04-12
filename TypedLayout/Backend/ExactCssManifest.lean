import TypedLayout.Backend.ExactCssFixtures

namespace TypedLayout.Backend.ExactCssManifest

/-- Stable string/file-name projection reserved for the exact export boundary. -/
structure ExportNames where
  slug : String
  documentHtmlFile : String
  stylesheetCssFile : String
  standalonePageHtmlFile : String
  deriving DecidableEq, Repr

end TypedLayout.Backend.ExactCssManifest

namespace TypedLayout.Backend.ExactCssFixtures.FixtureId

open TypedLayout.Backend.ExactCssManifest

/-- Stable textual slug used when exact fixtures are projected to export names. -/
def slug : FixtureId → String
  | .exactRow => "exact-row"
  | .paddedLeaf => "padded-leaf"
  | .framedLeaf => "framed-leaf"
  | .nestedFrameRow => "nested-frame-row"

/-- Stable export-boundary file names for canonical exact fixtures. -/
def exportNames (id : FixtureId) : ExportNames :=
  let slug := id.slug
  { slug := slug
  , documentHtmlFile := slug ++ ".document.html"
  , stylesheetCssFile := slug ++ ".styles.css"
  , standalonePageHtmlFile := slug ++ ".page.html"
  }

theorem exportNames_slug (id : FixtureId) :
    id.exportNames.slug = id.slug :=
  rfl

theorem all_slugs :
    all.map slug =
      [ "exact-row"
      , "padded-leaf"
      , "framed-leaf"
      , "nested-frame-row"
      ] := by
  native_decide

theorem all_slugs_nodup :
    (all.map slug).Nodup := by
  native_decide

theorem all_standalonePageHtmlFiles :
    all.map (fun id => id.exportNames.standalonePageHtmlFile) =
      [ "exact-row.page.html"
      , "padded-leaf.page.html"
      , "framed-leaf.page.html"
      , "nested-frame-row.page.html"
      ] := by
  native_decide

theorem all_documentHtmlFiles_nodup :
    (all.map (fun id => id.exportNames.documentHtmlFile)).Nodup := by
  native_decide

end TypedLayout.Backend.ExactCssFixtures.FixtureId

namespace TypedLayout.Backend.ExactCssManifest

open TypedLayout.Backend.ExactCss
open TypedLayout.Backend.ExactCssFixtures

/-- Typed export bundle carrying a canonical fixture together with its rendered
output projections. -/
structure RenderedFixtureExport where
  fixture : Fixture
  names : ExportNames
  renderedDocument : ExactDocument.RenderedDocument
  renderedPage : ExactDocument.RenderedPage

namespace RenderedFixtureExport

/-- Package a canonical exact fixture into the typed export bundle. -/
def ofFixture (fixture : Fixture) : RenderedFixtureExport :=
  { fixture := fixture
  , names := fixture.id.exportNames
  , renderedDocument := fixture.renderedDocument
  , renderedPage := fixture.renderedPage
  }

def id (entry : RenderedFixtureExport) : FixtureId :=
  entry.fixture.id

def artifact (entry : RenderedFixtureExport) : Artifact :=
  entry.fixture.artifact

def renderHtml (entry : RenderedFixtureExport) : String :=
  entry.renderedDocument.html

def renderCss (entry : RenderedFixtureExport) : String :=
  entry.renderedDocument.css

def renderPage (entry : RenderedFixtureExport) : String :=
  entry.renderedPage.html

theorem ofFixture_id (fixture : Fixture) :
    (ofFixture fixture).id = fixture.id :=
  rfl

theorem ofFixture_names (fixture : Fixture) :
    (ofFixture fixture).names = fixture.id.exportNames :=
  rfl

theorem ofFixture_renderedDocument (fixture : Fixture) :
    (ofFixture fixture).renderedDocument = fixture.renderedDocument :=
  rfl

theorem ofFixture_renderedPage (fixture : Fixture) :
    (ofFixture fixture).renderedPage = fixture.renderedPage :=
  rfl

theorem ofFixture_renderedDocument_exact (fixture : Fixture) :
    fixture.renderedDocumentResult = .exact (ofFixture fixture).renderedDocument := by
  simpa [ofFixture] using fixture.renderedDocumentResult_exact

theorem ofFixture_renderedPage_exact (fixture : Fixture) :
    fixture.renderedPageResult = .exact (ofFixture fixture).renderedPage := by
  simpa [ofFixture] using fixture.renderedPageResult_exact

theorem ofFixture_sourceGuarantee_exact (fixture : Fixture) :
    (ofFixture fixture).artifact.sourceGuarantee = .exact := by
  simpa [artifact, ofFixture] using fixture.sourceGuarantee_exact

theorem ofFixture_outputBounds_within_inputBounds (fixture : Fixture) :
    (ofFixture fixture).artifact.inputBounds.containsBounds
      (ofFixture fixture).artifact.outputBounds := by
  simpa [artifact, ofFixture] using fixture.outputBounds_within_inputBounds

theorem ofFixture_renderHtml (fixture : Fixture) :
    (ofFixture fixture).renderHtml = fixture.renderHtml :=
  rfl

theorem ofFixture_renderCss (fixture : Fixture) :
    (ofFixture fixture).renderCss = fixture.renderCss :=
  rfl

theorem ofFixture_renderPage (fixture : Fixture) :
    (ofFixture fixture).renderPage = fixture.renderPage :=
  rfl

end RenderedFixtureExport

/-- Typed manifest of exact rendered fixture exports. -/
structure Manifest where
  entries : List RenderedFixtureExport

namespace Manifest

def ids (manifest : Manifest) : List FixtureId :=
  manifest.entries.map RenderedFixtureExport.id

def slugs (manifest : Manifest) : List String :=
  manifest.entries.map (fun entry => entry.names.slug)

def documentHtmlFiles (manifest : Manifest) : List String :=
  manifest.entries.map (fun entry => entry.names.documentHtmlFile)

def stylesheetCssFiles (manifest : Manifest) : List String :=
  manifest.entries.map (fun entry => entry.names.stylesheetCssFile)

def standalonePageHtmlFiles (manifest : Manifest) : List String :=
  manifest.entries.map (fun entry => entry.names.standalonePageHtmlFile)

def renderedDocuments (manifest : Manifest) : List ExactDocument.RenderedDocument :=
  manifest.entries.map RenderedFixtureExport.renderedDocument

def renderedPages (manifest : Manifest) : List ExactDocument.RenderedPage :=
  manifest.entries.map RenderedFixtureExport.renderedPage

theorem ids_length_eq_entries_length (manifest : Manifest) :
    manifest.ids.length = manifest.entries.length := by
  simp [ids]

theorem slugs_length_eq_entries_length (manifest : Manifest) :
    manifest.slugs.length = manifest.entries.length := by
  simp [slugs]

theorem renderedPages_length_eq_entries_length (manifest : Manifest) :
    manifest.renderedPages.length = manifest.entries.length := by
  simp [renderedPages]

end Manifest

/-- Export bundle for a canonical exact fixture id. -/
def fixtureExport : FixtureId → RenderedFixtureExport
  | id => RenderedFixtureExport.ofFixture (fixture id)

/-- Export bundles for the current canonical exact fixture corpus. -/
def all : List RenderedFixtureExport :=
  TypedLayout.Backend.ExactCssFixtures.FixtureId.all.map fixtureExport

/-- Manifest view of the current canonical exact fixture corpus. -/
def canonical : Manifest :=
  { entries := all }

def exactRowExport : RenderedFixtureExport :=
  fixtureExport .exactRow

def paddedLeafExport : RenderedFixtureExport :=
  fixtureExport .paddedLeaf

def framedLeafExport : RenderedFixtureExport :=
  fixtureExport .framedLeaf

def nestedFrameRowExport : RenderedFixtureExport :=
  fixtureExport .nestedFrameRow

theorem all_ids :
    all.map RenderedFixtureExport.id =
      TypedLayout.Backend.ExactCssFixtures.FixtureId.all := by
  native_decide

theorem canonical_ids :
    canonical.ids = TypedLayout.Backend.ExactCssFixtures.FixtureId.all := by
  exact all_ids

theorem canonical_slugs :
    canonical.slugs =
      TypedLayout.Backend.ExactCssFixtures.FixtureId.all.map
        TypedLayout.Backend.ExactCssFixtures.FixtureId.slug := by
  native_decide

theorem canonical_standalonePageHtmlFiles :
    canonical.standalonePageHtmlFiles =
      [ "exact-row.page.html"
      , "padded-leaf.page.html"
      , "framed-leaf.page.html"
      , "nested-frame-row.page.html"
      ] := by
  native_decide

theorem canonical_documentHtmlFiles_nodup :
    canonical.documentHtmlFiles.Nodup := by
  native_decide

theorem exactRowExport_standalonePageHtmlFile :
    exactRowExport.names.standalonePageHtmlFile = "exact-row.page.html" := by
  native_decide

theorem exactRowExport_renderPage :
    exactRowExport.renderPage = exactRowFixture.renderPage := by
  simpa [exactRowExport, fixtureExport] using
    RenderedFixtureExport.ofFixture_renderPage exactRowFixture

theorem nestedFrameRowExport_renderedPage_exact :
    nestedFrameRowFixture.renderedPageResult = .exact nestedFrameRowExport.renderedPage := by
  simpa [nestedFrameRowExport, fixtureExport] using
    RenderedFixtureExport.ofFixture_renderedPage_exact nestedFrameRowFixture

end TypedLayout.Backend.ExactCssManifest
