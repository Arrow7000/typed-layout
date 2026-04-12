import TypedLayout.Backend.ExactCssProjection
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

The fixture stores the source-side input pair together with the end-to-end exact
projection witness produced by the public exact-check helper. This keeps the
corpus typed through certification, contract synthesis, backend lowering,
document projection, and rendered output recovery without introducing a stringly
registry layer. -/
structure Fixture where
  id : FixtureId
  available : AvailableSpace
  layout : Layout
  projection : ExactProjection available layout

namespace Fixture

def checked (fixture : Fixture) : CheckedWithin fixture.available :=
  fixture.projection.checked

def certified (fixture : Fixture) : CertifiedWithin fixture.available :=
  fixture.projection.certified

def summary (fixture : Fixture) : ExactLayoutSummary :=
  fixture.projection.summary

def contract (fixture : Fixture) : ExactLayoutContract :=
  fixture.projection.contract

def artifact (fixture : Fixture) : Artifact :=
  fixture.projection.artifact

def artifactResult (fixture : Fixture) : CheckResult Artifact :=
  fixture.projection.artifactResult

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
  fixture.projection.renderedDocumentResult

def renderedPageResult (fixture : Fixture) : CheckResult ExactDocument.RenderedPage :=
  fixture.projection.renderedPageResult

def renderHtmlResult (fixture : Fixture) : CheckResult String :=
  fixture.projection.renderHtmlResult

def renderCssResult (fixture : Fixture) : CheckResult String :=
  fixture.projection.renderCssResult

def renderPageResult (fixture : Fixture) : CheckResult String :=
  fixture.projection.renderPageResult

theorem artifactResult_exact (fixture : Fixture) :
    fixture.artifactResult = .exact fixture.artifact :=
  fixture.projection.artifactResult_exact

theorem targetProfile_exact1D_v1 (fixture : Fixture) :
    fixture.artifact.targetProfile = .exact1D_v1 :=
  fixture.projection.artifact_targetProfile_exact1D_v1

theorem sourceGuarantee_exact (fixture : Fixture) :
    fixture.artifact.sourceGuarantee = .exact :=
  fixture.projection.artifact_sourceGuarantee_exact

theorem outputBounds_within_inputBounds (fixture : Fixture) :
    fixture.artifact.inputBounds.containsBounds fixture.artifact.outputBounds :=
  fixture.projection.artifact_outputBounds_within_inputBounds

theorem contract_guarantee_exact (fixture : Fixture) :
    fixture.contract.guarantee = .exact :=
  fixture.projection.contract_guarantee

theorem artifact_sourceGuarantee_eq_contract_guarantee (fixture : Fixture) :
    fixture.artifact.sourceGuarantee = fixture.contract.guarantee :=
  fixture.projection.artifact_sourceGuarantee_eq_contract_guarantee

theorem renderedDocument_eq_document_render (fixture : Fixture) :
    fixture.renderedDocument = fixture.document.render :=
  fixture.projection.renderedDocument_eq_document_render

theorem renderedPage_eq_document_renderPage (fixture : Fixture) :
    fixture.renderedPage = fixture.document.renderPage :=
  fixture.projection.renderedPage_eq_document_renderPage

theorem renderedDocumentResult_exact (fixture : Fixture) :
    fixture.renderedDocumentResult = .exact fixture.renderedDocument := by
  exact fixture.projection.renderedDocumentResult_exact

theorem renderedPageResult_exact (fixture : Fixture) :
    fixture.renderedPageResult = .exact fixture.renderedPage := by
  exact fixture.projection.renderedPageResult_exact

theorem renderHtmlResult_exact (fixture : Fixture) :
    fixture.renderHtmlResult = .exact fixture.renderHtml := by
  exact fixture.projection.renderHtmlResult_exact

theorem renderCssResult_exact (fixture : Fixture) :
    fixture.renderCssResult = .exact fixture.renderCss := by
  exact fixture.projection.renderCssResult_exact

theorem renderPageResult_exact (fixture : Fixture) :
    fixture.renderPageResult = .exact fixture.renderPage := by
  exact fixture.projection.renderPageResult_exact

theorem document_ruleClassNamesNodup (fixture : Fixture) :
    fixture.document.ruleClassNamesNodup := by
  simpa [document, Fixture.document] using
    ExactDocument.Document.ofArtifact_ruleClassNamesNodup fixture.artifact

theorem document_classReferencesCoveredByStylesheet (fixture : Fixture) :
    fixture.document.classReferencesCoveredByStylesheet := by
  simpa [document, Fixture.document] using
    ExactDocument.Document.ofArtifact_classReferencesCoveredByStylesheet fixture.artifact

theorem document_singleRootBody (fixture : Fixture) :
    fixture.document.singleRootBody := by
  simpa [document, Fixture.document] using
    ExactDocument.Document.ofArtifact_singleRootBody fixture.artifact

end Fixture

def fixture : FixtureId → Fixture
  | .exactRow =>
      { id := .exactRow
      , available := exactRowAvailable
      , layout := exactRowLayout
      , projection :=
          match h : check exactRowAvailable exactRowLayout with
          | .exact checked => ExactProjection.ofCheck h
          | .incompatible error =>
              False.elim <| by
                have hExact := exactRowCheckGuarantee
                simp [CheckResult.isExact, h] at hExact
      }
  | .paddedLeaf =>
      { id := .paddedLeaf
      , available := paddedLeafAvailable
      , layout := paddedLeafLayout
      , projection :=
          match h : check paddedLeafAvailable paddedLeafLayout with
          | .exact checked => ExactProjection.ofCheck h
          | .incompatible error =>
              False.elim <| by
                have hExact := paddedLeafCheckGuarantee
                simp [CheckResult.isExact, h] at hExact
      }
  | .framedLeaf =>
      { id := .framedLeaf
      , available := framedLeafAvailable
      , layout := framedLeafLayout
      , projection :=
          match h : check framedLeafAvailable framedLeafLayout with
          | .exact checked => ExactProjection.ofCheck h
          | .incompatible error =>
              False.elim <| by
                have hExact : (check framedLeafAvailable framedLeafLayout).isExact = true := by
                  simpa [framedLeafAvailable] using framedLeafCheckGuarantee
                simp [CheckResult.isExact, h] at hExact
      }
  | .nestedFrameRow =>
      { id := .nestedFrameRow
      , available := nestedFrameRowAvailable
      , layout := nestedFrameRowLayout
      , projection :=
          match h : check nestedFrameRowAvailable nestedFrameRowLayout with
          | .exact checked => ExactProjection.ofCheck h
          | .incompatible error =>
              False.elim <| by
                have hExact := nestedFrameRowCheckExactAtAvailable
                simp [CheckResult.isExact, h] at hExact
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

theorem exactRowFixture_contract_guarantee :
    exactRowFixture.contract.guarantee = .exact := by
  exact Fixture.contract_guarantee_exact exactRowFixture

theorem exactRowFixture_artifact_sourceGuarantee_eq_contract_guarantee :
    exactRowFixture.artifact.sourceGuarantee = exactRowFixture.contract.guarantee := by
  exact Fixture.artifact_sourceGuarantee_eq_contract_guarantee exactRowFixture

theorem exactRowFixture_document_ruleClassNamesNodup :
    exactRowFixture.document.ruleClassNamesNodup := by
  exact Fixture.document_ruleClassNamesNodup exactRowFixture

theorem paddedLeafFixture_renderCssResult_exact :
    paddedLeafFixture.renderCssResult = .exact paddedLeafFixture.renderCss := by
  exact Fixture.renderCssResult_exact paddedLeafFixture

theorem framedLeafFixture_renderedPageResult_exact :
    framedLeafFixture.renderedPageResult = .exact framedLeafFixture.renderedPage := by
  exact Fixture.renderedPageResult_exact framedLeafFixture

theorem framedLeafFixture_document_singleRootBody :
    framedLeafFixture.document.singleRootBody := by
  exact Fixture.document_singleRootBody framedLeafFixture

theorem framedLeafFixture_renderedPage_eq_document_renderPage :
    framedLeafFixture.renderedPage = framedLeafFixture.document.renderPage := by
  exact Fixture.renderedPage_eq_document_renderPage framedLeafFixture

theorem nestedFrameRowFixture_outputBounds_within_inputBounds :
    nestedFrameRowFixture.artifact.inputBounds.containsBounds
      nestedFrameRowFixture.artifact.outputBounds := by
  exact Fixture.outputBounds_within_inputBounds nestedFrameRowFixture

theorem nestedFrameRowFixture_document_classReferencesCoveredByStylesheet :
    nestedFrameRowFixture.document.classReferencesCoveredByStylesheet := by
  exact Fixture.document_classReferencesCoveredByStylesheet nestedFrameRowFixture

end TypedLayout.Backend.ExactCssFixtures
