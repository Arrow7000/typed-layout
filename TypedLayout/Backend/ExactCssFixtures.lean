import TypedLayout.Backend.ExactCssRender
import TypedLayout.Core.Examples

namespace TypedLayout.Backend.ExactCssFixtures

open TypedLayout.Core
open TypedLayout.Backend.ExactCss
open TypedLayout.Core.Examples

/-- Canonical identifiers for the current exact backend fixture corpus. -/
inductive FixtureId where
  | exactRow
  | paddedLeaf
  | framedLeaf
  | nestedFrameRow
  deriving DecidableEq, Repr

namespace FixtureId

/-- Canonical exact-fragment backend fixtures currently carried by the repository. -/
def all : List FixtureId :=
  [ .exactRow
  , .paddedLeaf
  , .framedLeaf
  , .nestedFrameRow
  ]

theorem all_nodup : all.Nodup := by
  native_decide

end FixtureId

/-- Canonical backend fixture for the current exact fragment.

The fixture stores the source-side input pair together with the exact backend
artifact witness produced by the public exact-check helper. This keeps the corpus
typed through the artifact/document/rendered-page pipeline without introducing a
stringly registry layer. -/
structure Fixture where
  id : FixtureId
  available : AvailableSpace
  layout : Layout
  artifact : Artifact
  artifactExact : checkArtifact available layout = .exact artifact

namespace Fixture

def artifactResult (fixture : Fixture) : CheckResult Artifact :=
  checkArtifact fixture.available fixture.layout

def document (fixture : Fixture) : ExactDocument.Document :=
  fixture.artifact.document

def renderedDocument (fixture : Fixture) : ExactDocument.RenderedDocument :=
  fixture.artifact.renderedDocument

def renderedPage (fixture : Fixture) : ExactDocument.RenderedPage :=
  fixture.artifact.renderedPage

def renderHtml (fixture : Fixture) : String :=
  fixture.artifact.renderHtml

def renderCss (fixture : Fixture) : String :=
  fixture.artifact.renderCss

def renderPage (fixture : Fixture) : String :=
  fixture.artifact.renderPage

def renderedDocumentResult (fixture : Fixture) : CheckResult ExactDocument.RenderedDocument :=
  checkRenderedDocument fixture.available fixture.layout

def renderedPageResult (fixture : Fixture) : CheckResult ExactDocument.RenderedPage :=
  checkRenderedPage fixture.available fixture.layout

def renderHtmlResult (fixture : Fixture) : CheckResult String :=
  checkRenderHtml fixture.available fixture.layout

def renderCssResult (fixture : Fixture) : CheckResult String :=
  checkRenderCss fixture.available fixture.layout

def renderPageResult (fixture : Fixture) : CheckResult String :=
  checkRenderPage fixture.available fixture.layout

theorem artifactResult_exact (fixture : Fixture) :
    fixture.artifactResult = .exact fixture.artifact :=
  fixture.artifactExact

theorem targetProfile_exact1D_v1 (fixture : Fixture) :
    fixture.artifact.targetProfile = .exact1D_v1 :=
  checkArtifact_exact_targetProfile fixture.artifactExact

theorem sourceGuarantee_exact (fixture : Fixture) :
    fixture.artifact.sourceGuarantee = .exact :=
  checkArtifact_exact_sourceGuarantee fixture.artifactExact

theorem outputBounds_within_inputBounds (fixture : Fixture) :
    fixture.artifact.inputBounds.containsBounds fixture.artifact.outputBounds :=
  checkArtifact_exact_outputBounds_within_inputBounds fixture.artifactExact

theorem renderedDocumentResult_exact (fixture : Fixture) :
    fixture.renderedDocumentResult = .exact fixture.renderedDocument := by
  simp [renderedDocumentResult, renderedDocument, checkRenderedDocument,
    CheckResult.map, fixture.artifactExact]

theorem renderedPageResult_exact (fixture : Fixture) :
    fixture.renderedPageResult = .exact fixture.renderedPage := by
  simp [renderedPageResult, renderedPage, checkRenderedPage,
    CheckResult.map, fixture.artifactExact]

theorem renderHtmlResult_exact (fixture : Fixture) :
    fixture.renderHtmlResult = .exact fixture.renderHtml := by
  simp [renderHtmlResult, renderHtml, checkRenderHtml,
    CheckResult.map, fixture.artifactExact]

theorem renderCssResult_exact (fixture : Fixture) :
    fixture.renderCssResult = .exact fixture.renderCss := by
  simp [renderCssResult, renderCss, checkRenderCss,
    CheckResult.map, fixture.artifactExact]

theorem renderPageResult_exact (fixture : Fixture) :
    fixture.renderPageResult = .exact fixture.renderPage := by
  simp [renderPageResult, renderPage, checkRenderPage,
    CheckResult.map, fixture.artifactExact]

end Fixture

def fixture : FixtureId → Fixture
  | .exactRow =>
      { id := .exactRow
      , available := exactRowAvailable
      , layout := exactRowLayout
      , artifact := Artifact.ofCertifiedWithin exactRowCertified
      , artifactExact := by
          native_decide
      }
  | .paddedLeaf =>
      { id := .paddedLeaf
      , available := paddedLeafAvailable
      , layout := paddedLeafLayout
      , artifact := Artifact.ofCertifiedWithin paddedLeafCertified
      , artifactExact := by
          native_decide
      }
  | .framedLeaf =>
      { id := .framedLeaf
      , available := framedLeafAvailable
      , layout := framedLeafLayout
      , artifact := Artifact.ofCertifiedWithin framedLeafCertified
      , artifactExact := by
          native_decide
      }
  | .nestedFrameRow =>
      { id := .nestedFrameRow
      , available := nestedFrameRowAvailable
      , layout := nestedFrameRowLayout
      , artifact := Artifact.ofCertifiedWithin nestedFrameRowCertified
      , artifactExact := by
          native_decide
      }

/-- The current canonical exact backend fixture corpus. -/
def all : List Fixture :=
  FixtureId.all.map fixture

def exactRowFixture : Fixture :=
  fixture .exactRow

def paddedLeafFixture : Fixture :=
  fixture .paddedLeaf

def framedLeafFixture : Fixture :=
  fixture .framedLeaf

def nestedFrameRowFixture : Fixture :=
  fixture .nestedFrameRow

theorem all_ids :
    all.map Fixture.id = FixtureId.all := by
  native_decide

theorem exactRowFixture_targetProfile :
    exactRowFixture.artifact.targetProfile = .exact1D_v1 := by
  exact Fixture.targetProfile_exact1D_v1 exactRowFixture

theorem paddedLeafFixture_renderCssResult_exact :
    paddedLeafFixture.renderCssResult = .exact paddedLeafFixture.renderCss := by
  exact Fixture.renderCssResult_exact paddedLeafFixture

theorem framedLeafFixture_renderedPageResult_exact :
    framedLeafFixture.renderedPageResult = .exact framedLeafFixture.renderedPage := by
  exact Fixture.renderedPageResult_exact framedLeafFixture

theorem nestedFrameRowFixture_outputBounds_within_inputBounds :
    nestedFrameRowFixture.artifact.inputBounds.containsBounds
      nestedFrameRowFixture.artifact.outputBounds := by
  exact Fixture.outputBounds_within_inputBounds nestedFrameRowFixture

end TypedLayout.Backend.ExactCssFixtures
