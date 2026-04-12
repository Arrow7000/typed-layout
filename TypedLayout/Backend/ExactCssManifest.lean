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

/-- Typed output file categories exposed at the exact export boundary. -/
inductive OutputFileKind where
  | documentHtml
  | stylesheetCss
  | standalonePageHtml
  deriving DecidableEq, Repr

namespace OutputFileKind

/-- Project an output-file category to its stable export-boundary file name. -/
def fileName (names : ExportNames) : OutputFileKind → String
  | .documentHtml => names.documentHtmlFile
  | .stylesheetCss => names.stylesheetCssFile
  | .standalonePageHtml => names.standalonePageHtmlFile

end OutputFileKind

/-- Typed output payloads carried by the exact export boundary before any IO. -/
inductive OutputPayload where
  | documentHtml (document : ExactDocument.RenderedDocument)
  | stylesheetCss (document : ExactDocument.RenderedDocument)
  | standalonePageHtml (page : ExactDocument.RenderedPage)
  deriving DecidableEq, Repr

namespace OutputPayload

def kind : OutputPayload → OutputFileKind
  | .documentHtml _ => .documentHtml
  | .stylesheetCss _ => .stylesheetCss
  | .standalonePageHtml _ => .standalonePageHtml

def contents : OutputPayload → String
  | .documentHtml document => document.html
  | .stylesheetCss document => document.css
  | .standalonePageHtml page => page.html

theorem documentHtml_contents (document : ExactDocument.RenderedDocument) :
    (OutputPayload.documentHtml document).contents = document.html :=
  rfl

theorem stylesheetCss_contents (document : ExactDocument.RenderedDocument) :
    (OutputPayload.stylesheetCss document).contents = document.css :=
  rfl

theorem standalonePageHtml_contents (page : ExactDocument.RenderedPage) :
    (OutputPayload.standalonePageHtml page).contents = page.html :=
  rfl

end OutputPayload

/-- Intended output file and payload at the exact export boundary. -/
structure OutputFile where
  fixtureId : FixtureId
  names : ExportNames
  payload : OutputPayload
  deriving DecidableEq, Repr

namespace OutputFile

def kind (file : OutputFile) : OutputFileKind :=
  file.payload.kind

def fileName (file : OutputFile) : String :=
  file.kind.fileName file.names

def contents (file : OutputFile) : String :=
  file.payload.contents

def documentHtml (entry : RenderedFixtureExport) : OutputFile :=
  { fixtureId := entry.id
  , names := entry.names
  , payload := .documentHtml entry.renderedDocument
  }

def stylesheetCss (entry : RenderedFixtureExport) : OutputFile :=
  { fixtureId := entry.id
  , names := entry.names
  , payload := .stylesheetCss entry.renderedDocument
  }

def standalonePageHtml (entry : RenderedFixtureExport) : OutputFile :=
  { fixtureId := entry.id
  , names := entry.names
  , payload := .standalonePageHtml entry.renderedPage
  }

theorem documentHtml_fixtureId (entry : RenderedFixtureExport) :
    (documentHtml entry).fixtureId = entry.id :=
  rfl

theorem documentHtml_fileName (entry : RenderedFixtureExport) :
    (documentHtml entry).fileName = entry.names.documentHtmlFile :=
  rfl

theorem documentHtml_contents (entry : RenderedFixtureExport) :
    (documentHtml entry).contents = entry.renderedDocument.html :=
  rfl

theorem stylesheetCss_fileName (entry : RenderedFixtureExport) :
    (stylesheetCss entry).fileName = entry.names.stylesheetCssFile :=
  rfl

theorem stylesheetCss_contents (entry : RenderedFixtureExport) :
    (stylesheetCss entry).contents = entry.renderedDocument.css :=
  rfl

theorem standalonePageHtml_fileName (entry : RenderedFixtureExport) :
    (standalonePageHtml entry).fileName = entry.names.standalonePageHtmlFile :=
  rfl

theorem standalonePageHtml_contents (entry : RenderedFixtureExport) :
    (standalonePageHtml entry).contents = entry.renderedPage.html :=
  rfl

end OutputFile

namespace RenderedFixtureExport

/-- Expand a rendered fixture export to its intended output files. -/
def outputFiles (entry : RenderedFixtureExport) : List OutputFile :=
  [ OutputFile.documentHtml entry
  , OutputFile.stylesheetCss entry
  , OutputFile.standalonePageHtml entry
  ]

theorem outputFiles_length (entry : RenderedFixtureExport) :
    entry.outputFiles.length = 3 := by
  rfl

theorem outputFiles_fileNames (entry : RenderedFixtureExport) :
    entry.outputFiles.map OutputFile.fileName =
      [ entry.names.documentHtmlFile
      , entry.names.stylesheetCssFile
      , entry.names.standalonePageHtmlFile
      ] := by
  rfl

theorem outputFiles_contents (entry : RenderedFixtureExport) :
    entry.outputFiles.map OutputFile.contents =
      [ entry.renderedDocument.html
      , entry.renderedDocument.css
      , entry.renderedPage.html
      ] := by
  rfl

end RenderedFixtureExport

/-- Pure export plan listing intended exact-fragment output files and contents. -/
structure ExportPlan where
  files : List OutputFile
  deriving DecidableEq, Repr

namespace ExportPlan

private def ofEntries : List RenderedFixtureExport → List OutputFile
  | [] => []
  | entry :: entries => entry.outputFiles ++ ofEntries entries

def fileNames (plan : ExportPlan) : List String :=
  plan.files.map OutputFile.fileName

def contents (plan : ExportPlan) : List String :=
  plan.files.map OutputFile.contents

def ofManifest (manifest : Manifest) : ExportPlan :=
  { files := ofEntries manifest.entries }

private theorem ofEntries_length (entries : List RenderedFixtureExport) :
    (ofEntries entries).length = entries.length * 3 := by
  induction entries with
  | nil =>
      simp [ofEntries]
  | cons entry entries ih =>
      simp [ofEntries, ih, Nat.succ_mul]
      rw [RenderedFixtureExport.outputFiles_length]
      omega

theorem fileNames_length_eq_files_length (plan : ExportPlan) :
    plan.fileNames.length = plan.files.length := by
  simp [fileNames]

theorem contents_length_eq_files_length (plan : ExportPlan) :
    plan.contents.length = plan.files.length := by
  simp [contents]

theorem ofManifest_files_length (manifest : Manifest) :
    (ofManifest manifest).files.length = manifest.entries.length * 3 := by
  simp [ofManifest, ofEntries_length]

end ExportPlan

namespace Manifest

/-- Expand a manifest to a pure file plan without performing any writes. -/
def exportPlan (manifest : Manifest) : ExportPlan :=
  ExportPlan.ofManifest manifest

theorem exportPlan_files_length (manifest : Manifest) :
    manifest.exportPlan.files.length = manifest.entries.length * 3 := by
  simpa [exportPlan] using ExportPlan.ofManifest_files_length manifest

theorem exportPlan_fileNames_length (manifest : Manifest) :
    manifest.exportPlan.fileNames.length = manifest.entries.length * 3 := by
  rw [ExportPlan.fileNames_length_eq_files_length]
  exact manifest.exportPlan_files_length

theorem exportPlan_contents_length (manifest : Manifest) :
    manifest.exportPlan.contents.length = manifest.entries.length * 3 := by
  rw [ExportPlan.contents_length_eq_files_length]
  exact manifest.exportPlan_files_length

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

/-- Pure file plan for the current canonical exact fixture corpus. -/
def canonicalExportPlan : ExportPlan :=
  canonical.exportPlan

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

theorem canonicalExportPlan_files_length :
    canonicalExportPlan.files.length = 12 := by
  native_decide

theorem canonicalExportPlan_fileNames :
    canonicalExportPlan.fileNames =
      [ "exact-row.document.html"
      , "exact-row.styles.css"
      , "exact-row.page.html"
      , "padded-leaf.document.html"
      , "padded-leaf.styles.css"
      , "padded-leaf.page.html"
      , "framed-leaf.document.html"
      , "framed-leaf.styles.css"
      , "framed-leaf.page.html"
      , "nested-frame-row.document.html"
      , "nested-frame-row.styles.css"
      , "nested-frame-row.page.html"
      ] := by
  native_decide

theorem exactRowExport_standalonePageHtmlFile :
    exactRowExport.names.standalonePageHtmlFile = "exact-row.page.html" := by
  native_decide

theorem exactRowExport_outputFiles_fileNames :
    exactRowExport.outputFiles.map OutputFile.fileName =
      [ "exact-row.document.html"
      , "exact-row.styles.css"
      , "exact-row.page.html"
      ] := by
  native_decide

theorem exactRowExport_outputFiles_contents :
    exactRowExport.outputFiles.map OutputFile.contents =
      [ exactRowExport.renderHtml
      , exactRowExport.renderCss
      , exactRowExport.renderPage
      ] := by
  rfl

theorem exactRowExport_renderPage :
    exactRowExport.renderPage = exactRowFixture.renderPage := by
  simpa [exactRowExport, fixtureExport] using
    RenderedFixtureExport.ofFixture_renderPage exactRowFixture

theorem nestedFrameRowExport_renderedPage_exact :
    nestedFrameRowFixture.renderedPageResult = .exact nestedFrameRowExport.renderedPage := by
  simpa [nestedFrameRowExport, fixtureExport] using
    RenderedFixtureExport.ofFixture_renderedPage_exact nestedFrameRowFixture

end TypedLayout.Backend.ExactCssManifest
