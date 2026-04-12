import TypedLayout.Backend.ExactCss
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

end TypedLayout.Backend.ExactCssExamples
