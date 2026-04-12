import TypedLayout.Backend.ExactCssRender
import TypedLayout.Core.Examples

namespace TypedLayout.Backend.ExactCssExamples

open TypedLayout.Core
open TypedLayout.Backend.ExactCss
open TypedLayout.Core.Examples

def exactRowNode : Node :=
  Node.ofCheckedLayout exactRowCheckedLayout

theorem exactRowNodeStyle :
    exactRowNode.style =
      { boxSizing := .borderBox
      , size := { width := .px 470, height := .px 30 }
      , padding := Padding.zero
      , display := .flex
          { direction := .row
          , gap := .px 10
          , wrap := .nowrap
          , justifyContent := .flexStart
          , alignItems := .flexStart
          }
      , flexItem := FlexItem.fixed
      } := by
  native_decide

theorem exactRowNodeChildSizes :
    exactRowNode.children.map (fun child => child.style.size) =
      [ { width := .px 100, height := .px 20 }
      , { width := .px 150, height := .px 30 }
      , { width := .px 200, height := .px 25 }
      ] := by
  native_decide

def exactColumnNode : Node :=
  Node.ofCheckedLayout exactColumnCheckedLayout

theorem exactColumnNodeStyle :
    exactColumnNode.style =
      { boxSizing := .borderBox
      , size := { width := .px 40, height := .px 70 }
      , padding := Padding.zero
      , display := .flex
          { direction := .column
          , gap := .px 5
          , wrap := .nowrap
          , justifyContent := .flexStart
          , alignItems := .flexStart
          }
      , flexItem := FlexItem.fixed
      } := by
  native_decide

def paddedLeafNode : Node :=
  Node.ofCheckedLayout paddedLeafCheckedLayout

theorem paddedLeafNodeStyle :
    paddedLeafNode.style =
      { boxSizing := .borderBox
      , size := { width := .px 15, height := .px 7 }
      , padding :=
          { left := .px 2
          , top := .px 1
          , right := .px 3
          , bottom := .px 1
          }
      , display := .block
      , flexItem := FlexItem.fixed
      } := by
  native_decide

def framedLeafNode : Node :=
  Node.ofCheckedLayout framedLeafCheckedLayout

theorem framedLeafNodeStyle :
    framedLeafNode.style =
      { boxSizing := .borderBox
      , size := { width := .px 120, height := .px 60 }
      , padding := Padding.zero
      , display := .block
      , flexItem := FlexItem.fixed
      } := by
  native_decide

def exactRowArtifact : Artifact :=
  Artifact.ofCertifiedWithin exactRowCertified

theorem exactRowArtifactMetadata :
    exactRowArtifact =
      { targetProfile := .exact1D_v1
      , sourceKind := .row
      , sourceGuarantee := .exact
      , inputBounds := exactRowAvailable.bounds
      , outputBounds := exactRowExpectedExtent.toBounds
       , root := exactRowNode
       } := by
  native_decide

theorem exactRowCheckWithinArtifactExact :
    checkWithinArtifact exactRowAvailable exactRowLayout = .exact exactRowArtifact := by
  native_decide

theorem exactRowCheckArtifactExact :
    checkArtifact exactRowAvailable exactRowLayout = .exact exactRowArtifact := by
  native_decide

theorem exactRowArtifactOutputBoundsWithinInputBounds :
    exactRowArtifact.inputBounds.containsBounds exactRowArtifact.outputBounds := by
  simpa [exactRowArtifact] using
    Artifact.ofCertifiedWithin_outputBounds_within_inputBounds exactRowCertified

theorem exactRowArtifactRecoveredFromChecked :
    ∃ checked : CheckedWithin exactRowAvailable,
      Artifact.ofCheckedWithin checked = exactRowArtifact ∧
      exactRowArtifact.root.style.size = Size.ofExtent checked.extent := by
  refine ⟨exactRowCertified.checked, ?_, ?_⟩
  · simpa [exactRowArtifact] using
      (Artifact.ofCertifiedWithin_eq_ofCheckedWithin exactRowCertified).symm
  · simpa [exactRowArtifact] using
      Artifact.ofCheckedWithin_root_size exactRowCertified.checked

def exactRowDocument : ExactDocument.Document :=
  exactRowArtifact.document

theorem exactRowArtifactDocumentMatchesNode :
    exactRowArtifact.document = exactRowNode.document := by
  native_decide

theorem exactRowDocumentBody :
    exactRowDocument.body =
      ExactDocument.Element.body
        [ ExactDocument.Element.div { serial := 0 }
            [ ExactDocument.Element.div { serial := 1 }
            , ExactDocument.Element.div { serial := 2 }
            , ExactDocument.Element.div { serial := 3 }
            ]
        ] := by
  native_decide

theorem exactRowDocumentRuleClasses :
    exactRowDocument.stylesheet.rules.map (fun rule => rule.className.serial) =
      [0, 1, 2, 3] := by
  native_decide

theorem exactRowDocumentRuleSizes :
    exactRowDocument.stylesheet.rules.map (fun rule => rule.style.size) =
      [ { width := .px 470, height := .px 30 }
      , { width := .px 100, height := .px 20 }
      , { width := .px 150, height := .px 30 }
      , { width := .px 200, height := .px 25 }
      ] := by
  native_decide

def paddedLeafDocument : ExactDocument.Document :=
  paddedLeafNode.document

theorem paddedLeafDocumentBody :
    paddedLeafDocument.body =
      ExactDocument.Element.body
        [ ExactDocument.Element.div { serial := 0 }
            [ ExactDocument.Element.div { serial := 1 } ]
        ] := by
  native_decide

theorem paddedLeafDocumentRuleClasses :
    paddedLeafDocument.stylesheet.rules.map (fun rule => rule.className.serial) =
      [0, 1] := by
  native_decide

def exactRowRenderedDocument : ExactDocument.RenderedDocument :=
  exactRowDocument.render

theorem exactRowRenderedDocumentMatchesArtifact :
    exactRowArtifact.renderedDocument = exactRowRenderedDocument := by
  native_decide

theorem exactRowRenderedHtml :
    exactRowRenderedDocument.html =
      "<body><div class=\"tl-0\"><div class=\"tl-1\"></div><div class=\"tl-2\"></div><div class=\"tl-3\"></div></div></body>" := by
  native_decide

theorem exactRowRenderedCss :
    exactRowRenderedDocument.css =
      ".tl-0{box-sizing:border-box;width:470px;height:30px;padding-left:0px;padding-top:0px;padding-right:0px;padding-bottom:0px;display:flex;flex-direction:row;gap:10px;flex-wrap:nowrap;justify-content:flex-start;align-items:flex-start;flex-grow:0;flex-shrink:0;}\n" ++
      ".tl-1{box-sizing:border-box;width:100px;height:20px;padding-left:0px;padding-top:0px;padding-right:0px;padding-bottom:0px;display:block;flex-grow:0;flex-shrink:0;}\n" ++
      ".tl-2{box-sizing:border-box;width:150px;height:30px;padding-left:0px;padding-top:0px;padding-right:0px;padding-bottom:0px;display:block;flex-grow:0;flex-shrink:0;}\n" ++
      ".tl-3{box-sizing:border-box;width:200px;height:25px;padding-left:0px;padding-top:0px;padding-right:0px;padding-bottom:0px;display:block;flex-grow:0;flex-shrink:0;}" := by
  native_decide

def paddedLeafRenderedDocument : ExactDocument.RenderedDocument :=
  paddedLeafDocument.render

theorem paddedLeafRenderedHtml :
    paddedLeafRenderedDocument.html =
      "<body><div class=\"tl-0\"><div class=\"tl-1\"></div></div></body>" := by
  native_decide

theorem paddedLeafRenderedCss :
    paddedLeafRenderedDocument.css =
      ".tl-0{box-sizing:border-box;width:15px;height:7px;padding-left:2px;padding-top:1px;padding-right:3px;padding-bottom:1px;display:block;flex-grow:0;flex-shrink:0;}\n" ++
      ".tl-1{box-sizing:border-box;width:10px;height:5px;padding-left:0px;padding-top:0px;padding-right:0px;padding-bottom:0px;display:block;flex-grow:0;flex-shrink:0;}" := by
  native_decide

end TypedLayout.Backend.ExactCssExamples
