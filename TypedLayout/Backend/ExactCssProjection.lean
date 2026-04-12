import TypedLayout.Backend.ExactCssRender

namespace TypedLayout.Backend.ExactCss

open TypedLayout.Core

/--
End-to-end wrapper for a successful exact check of a specific source layout.

The wrapper keeps the successful `CheckedWithin` witness tied to the original
source-side `check` result, and derives the richer exact pipeline views from
there: certification, summary/contract, backend artifact, typed document, and
rendered outputs.
-/
structure ExactProjection (available : AvailableSpace) (source : Layout) where
  checked : CheckedWithin available
  exact : check available source = .exact checked

namespace ExactProjection

def ofCheckedWithin
    {available : AvailableSpace}
    {source : Layout}
    (checked : CheckedWithin available)
    (exact : check available source = .exact checked) : ExactProjection available source :=
  { checked := checked
  , exact := exact
  }

def ofCheck
    {available : AvailableSpace}
    {source : Layout}
    {checked : CheckedWithin available}
    (exact : check available source = .exact checked) : ExactProjection available source :=
  ofCheckedWithin checked exact

def ofCheckWithin
    {available : AvailableSpace}
    {source : Layout}
    {checked : CheckedWithin available}
    (exact : checkWithin available source = .exact checked) : ExactProjection available source :=
  { checked := checked
  , exact := by
      simpa [check] using exact
  }

def ofCertifiedWithin
    {available : AvailableSpace}
    {source : Layout}
    (certified : CertifiedWithin available)
    (exact : check available source = .exact certified.checked) : ExactProjection available source :=
  ofCheck exact

def certified
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : CertifiedWithin available :=
  CertifiedWithin.ofCheck projection.exact

def layout
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : CheckedLayout :=
  projection.checked.layout

def extent
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : ExactExtent :=
  projection.layout.extent

def summary
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : ExactLayoutSummary :=
  projection.certified.summary

def contract
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : ExactLayoutContract :=
  projection.certified.contract

def artifact
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : Artifact :=
  Artifact.ofCertifiedWithin projection.certified

def document
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : ExactDocument.Document :=
  projection.artifact.document

def renderedDocument
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : ExactDocument.RenderedDocument :=
  projection.artifact.renderedDocument

def renderedPage
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : ExactDocument.RenderedPage :=
  projection.artifact.renderedPage

def renderHtml
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : String :=
  projection.artifact.renderHtml

def renderCss
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : String :=
  projection.artifact.renderCss

def renderPage
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : String :=
  projection.artifact.renderPage

def artifactResult
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : CheckResult Artifact :=
  .exact projection.artifact

def renderedDocumentResult
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : CheckResult ExactDocument.RenderedDocument :=
  .exact projection.renderedDocument

def renderedPageResult
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : CheckResult ExactDocument.RenderedPage :=
  .exact projection.renderedPage

def renderHtmlResult
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : CheckResult String :=
  .exact projection.renderHtml

def renderCssResult
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : CheckResult String :=
  .exact projection.renderCss

def renderPageResult
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) : CheckResult String :=
  .exact projection.renderPage

theorem check_exact
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    check available source = .exact projection.checked :=
  projection.exact

theorem checkWithin_exact
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    checkWithin available source = .exact projection.checked := by
  simpa [check] using projection.exact

theorem certified_checked
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.certified.checked = projection.checked :=
  rfl

theorem summary_guarantee
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.summary.guarantee = .exact := by
  simpa [summary, certified] using
    CertifiedWithin.summary_guarantee projection.certified

theorem contract_guarantee
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.contract.guarantee = .exact := by
  simpa [contract, certified] using
    CertifiedWithin.contract_guarantee projection.certified

theorem contract_output_extent
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.contract.output.extent = projection.extent := by
  simpa [contract, certified, extent, layout] using
    ExactLayoutContract.ofCertifiedWithin_output_extent projection.certified

theorem contract_localInvariants_eq_summary
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.contract.localInvariants = projection.summary.localInvariants :=
  rfl

theorem artifact_targetProfile_exact1D_v1
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.artifact.targetProfile = .exact1D_v1 := by
  exact Artifact.ofCertifiedWithin_targetProfile projection.certified

theorem artifact_sourceGuarantee_exact
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.artifact.sourceGuarantee = .exact := by
  simpa [artifact, certified] using
    Artifact.ofCertifiedWithin_sourceGuarantee_exact projection.certified

theorem artifact_outputBounds_within_inputBounds
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.artifact.inputBounds.containsBounds projection.artifact.outputBounds := by
  simpa [artifact, certified] using
    Artifact.ofCertifiedWithin_outputBounds_within_inputBounds projection.certified

theorem artifact_eq_ofCheckedWithin
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.artifact = Artifact.ofCheckedWithin projection.checked := by
  simpa [certified] using
    Artifact.ofCertifiedWithin_eq_ofCheckedWithin projection.certified

theorem artifact_sourceGuarantee_eq_contract_guarantee
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.artifact.sourceGuarantee = projection.contract.guarantee := by
  simpa [contract, certified] using
    Artifact.ofCertifiedWithin_sourceGuarantee projection.certified

theorem artifact_outputBounds_eq_contract_outputBounds
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.artifact.outputBounds = projection.contract.output.bounds := by
  simpa [contract, certified] using
    Artifact.ofCertifiedWithin_outputBounds projection.certified

theorem artifact_root_kind_eq_layout_kind
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.artifact.root.kind = projection.layout.kind := by
  simpa [artifact, certified, layout] using
    Artifact.ofCertifiedWithin_root_kind projection.certified

theorem document_eq_artifact_document
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.document = projection.artifact.document :=
  rfl

theorem renderedDocument_eq_document_render
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.renderedDocument = projection.document.render := by
  simpa [renderedDocument, document] using
    Artifact.renderedDocument_eq_document_render projection.artifact

theorem renderedPage_eq_document_renderPage
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.renderedPage = projection.document.renderPage := by
  simpa [renderedPage, document] using
    Artifact.renderedPage_eq_document_renderPage projection.artifact

theorem renderHtml_eq_renderedDocument_html
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.renderHtml = projection.renderedDocument.html :=
  rfl

theorem renderCss_eq_renderedDocument_css
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.renderCss = projection.renderedDocument.css :=
  rfl

theorem renderPage_eq_renderedPage_html
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.renderPage = projection.renderedPage.html :=
  rfl

theorem artifactResult_exact
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.artifactResult = .exact projection.artifact :=
  rfl

theorem renderedDocumentResult_exact
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.renderedDocumentResult = .exact projection.renderedDocument :=
  rfl

theorem renderedPageResult_exact
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.renderedPageResult = .exact projection.renderedPage :=
  rfl

theorem renderHtmlResult_exact
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.renderHtmlResult = .exact projection.renderHtml :=
  rfl

theorem renderCssResult_exact
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.renderCssResult = .exact projection.renderCss :=
  rfl

theorem renderPageResult_exact
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.renderPageResult = .exact projection.renderPage :=
  rfl

def checkWithinProjection (available : AvailableSpace) (source : Layout) :
    CheckResult (ExactProjection available source) :=
  match exact : checkWithin available source with
  | .exact _ => .exact (ofCheckWithin exact)
  | .incompatible error => .incompatible error

def checkProjection (available : AvailableSpace) (source : Layout) :
    CheckResult (ExactProjection available source) :=
  match exact : check available source with
  | .exact _ => .exact (ofCheck exact)
  | .incompatible error => .incompatible error

theorem document_ruleClassNamesNodup
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.document.ruleClassNamesNodup := by
  simpa [document] using
    ExactDocument.Document.ofArtifact_ruleClassNamesNodup projection.artifact

theorem document_classReferencesCoveredByStylesheet
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.document.classReferencesCoveredByStylesheet := by
  simpa [document] using
    ExactDocument.Document.ofArtifact_classReferencesCoveredByStylesheet projection.artifact

theorem document_singleRootBody
    {available : AvailableSpace}
    {source : Layout}
    (projection : ExactProjection available source) :
    projection.document.singleRootBody := by
  simpa [document] using
    ExactDocument.Document.ofArtifact_singleRootBody projection.artifact

end ExactProjection

end TypedLayout.Backend.ExactCss
