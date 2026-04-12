import TypedLayout.Core.Contract

namespace TypedLayout.Backend.ExactCss

open TypedLayout.Core

/-- Exact-fragment CSS length domain. The current backend layer only lowers to
concrete pixel lengths. -/
inductive Length where
  | px (value : Nat)
  deriving DecidableEq, Repr

namespace Length

def ofNat (value : Nat) : Length :=
  .px value

end Length

/-- Exact-fragment CSS width/height pair. -/
structure Size where
  width : Length
  height : Length
  deriving DecidableEq, Repr

namespace Size

def ofExtent (extent : ExactExtent) : Size :=
  { width := .px extent.width
  , height := .px extent.height
  }

end Size

/-- Typed CSS padding/inset payload for the exact fragment. -/
structure Padding where
  left : Length
  top : Length
  right : Length
  bottom : Length
  deriving DecidableEq, Repr

namespace Padding

def zero : Padding :=
  { left := .px 0
  , top := .px 0
  , right := .px 0
  , bottom := .px 0
  }

def ofInsets (insets : Insets) : Padding :=
  { left := .px insets.left
  , top := .px insets.top
  , right := .px insets.right
  , bottom := .px insets.bottom
  }

end Padding

inductive BoxSizing where
  | borderBox
  deriving DecidableEq, Repr

inductive FlexDirection where
  | row
  | column
  deriving DecidableEq, Repr

namespace FlexDirection

def ofAxis : Axis → FlexDirection
  | .horizontal => .row
  | .vertical => .column

end FlexDirection

inductive FlexWrap where
  | nowrap
  deriving DecidableEq, Repr

inductive JustifyContent where
  | flexStart
  deriving DecidableEq, Repr

inductive AlignItems where
  | flexStart
  deriving DecidableEq, Repr

/-- Flex-container payload restricted to the current exact 1D fragment. -/
structure FlexContainer where
  direction : FlexDirection
  gap : Length
  wrap : FlexWrap
  justifyContent : JustifyContent
  alignItems : AlignItems
  deriving DecidableEq, Repr

namespace FlexContainer

def exact1D (axis : Axis) (gap : Gap) : FlexContainer :=
  { direction := FlexDirection.ofAxis axis
  , gap := .px gap.amount
  , wrap := .nowrap
  , justifyContent := .flexStart
  , alignItems := .flexStart
  }

end FlexContainer

/-- Flex-item payload used to keep exact child extents fixed inside stackers. -/
structure FlexItem where
  grow : Nat
  shrink : Nat
  deriving DecidableEq, Repr

namespace FlexItem

def fixed : FlexItem :=
  { grow := 0, shrink := 0 }

end FlexItem

inductive Display where
  | block
  | flex (container : FlexContainer)
  deriving DecidableEq, Repr

/-- Typed style IR for the exact CSS backend fragment.

This stays intentionally small: border-box sizing, exact width/height, optional
padding, a block-or-flex display model, and the fixed flex-item policy needed by
the current exact row/column fragment. -/
structure Style where
  boxSizing : BoxSizing
  size : Size
  padding : Padding
  display : Display
  flexItem : FlexItem
  deriving DecidableEq, Repr

namespace Style

def block (extent : ExactExtent) (padding : Padding := Padding.zero) : Style :=
  { boxSizing := .borderBox
  , size := Size.ofExtent extent
  , padding := padding
  , display := .block
  , flexItem := FlexItem.fixed
  }

def stack (axis : Axis) (gap : Gap) (extent : ExactExtent) : Style :=
  { boxSizing := .borderBox
  , size := Size.ofExtent extent
  , padding := Padding.zero
  , display := .flex (FlexContainer.exact1D axis gap)
  , flexItem := FlexItem.fixed
  }

def ofCheckedLayout : CheckedLayout → Style
  | .leaf extent =>
      block extent
  | .row gap children =>
      stack .horizontal gap <| ExactExtent.stack .horizontal gap (children.map CheckedLayout.extent)
  | .column gap children =>
      stack .vertical gap <| ExactExtent.stack .vertical gap (children.map CheckedLayout.extent)
  | .padding insets child =>
      block (child.extent.expand insets) (Padding.ofInsets insets)
  | .frame extent _ =>
      block extent

theorem ofCheckedLayout_size (layout : CheckedLayout) :
    (ofCheckedLayout layout).size = Size.ofExtent layout.extent := by
  cases layout <;> simp [ofCheckedLayout, block, stack, Size.ofExtent, CheckedLayout.extent]

end Style

/-- Typed backend node IR for the current exact fragment. -/
structure Node where
  kind : LayoutKind
  style : Style
  children : List Node
  deriving Repr

mutual

private def decEqNode : (left right : Node) → Decidable (left = right)
  | ⟨leftKind, leftStyle, leftChildren⟩, ⟨rightKind, rightStyle, rightChildren⟩ =>
      match decEq leftKind rightKind with
      | isFalse hKind =>
          isFalse (by
            intro h
            injection h with hKind'
            exact hKind hKind')
      | isTrue hKind =>
          match decEq leftStyle rightStyle with
          | isFalse hStyle =>
              isFalse (by
                intro h
                injection h with _ hStyle'
                exact hStyle hStyle')
          | isTrue hStyle =>
              match decEqNodeList leftChildren rightChildren with
              | isFalse hChildren =>
                  isFalse (by
                    intro h
                    injection h with _ _ hChildren'
                    exact hChildren hChildren')
              | isTrue hChildren =>
                  isTrue (by
                    cases hKind
                    cases hStyle
                    cases hChildren
                    rfl)

private def decEqNodeList : (left right : List Node) → Decidable (left = right)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | leftHead :: leftTail, rightHead :: rightTail =>
      match decEqNode leftHead rightHead with
      | isFalse hHead =>
          isFalse (by
            intro h
            injection h with hHead'
            exact hHead hHead')
      | isTrue hHead =>
          match decEqNodeList leftTail rightTail with
          | isFalse hTail =>
              isFalse (by
                intro h
                injection h with _ hTail'
                exact hTail hTail')
          | isTrue hTail =>
              isTrue (by
                cases hHead
                cases hTail
                rfl)

end

instance : DecidableEq Node := decEqNode

namespace Node

mutual

def ofCheckedLayout : CheckedLayout → Node
  | .leaf extent =>
      { kind := .leaf
      , style := Style.ofCheckedLayout (.leaf extent)
      , children := []
      }
  | .row gap children =>
      { kind := .row
      , style := Style.ofCheckedLayout (.row gap children)
      , children := ofCheckedLayouts children
      }
  | .column gap children =>
      { kind := .column
      , style := Style.ofCheckedLayout (.column gap children)
      , children := ofCheckedLayouts children
      }
  | .padding insets child =>
      { kind := .padding
      , style := Style.ofCheckedLayout (.padding insets child)
      , children := [ofCheckedLayout child]
      }
  | .frame extent child =>
      { kind := .frame
      , style := Style.ofCheckedLayout (.frame extent child)
      , children := [ofCheckedLayout child]
      }

termination_by
  layout => sizeOf layout

decreasing_by
  all_goals simp_wf
  all_goals omega

def ofCheckedLayouts : List CheckedLayout → List Node
  | [] => []
  | child :: rest => ofCheckedLayout child :: ofCheckedLayouts rest

termination_by
  children => sizeOf children

decreasing_by
  all_goals simp_wf
  all_goals omega

end

theorem ofCheckedLayout_kind (layout : CheckedLayout) :
    (ofCheckedLayout layout).kind = layout.kind := by
  cases layout <;> simp [ofCheckedLayout, CheckedLayout.kind]

theorem ofCheckedLayout_style (layout : CheckedLayout) :
    (ofCheckedLayout layout).style = Style.ofCheckedLayout layout := by
  cases layout <;> simp [ofCheckedLayout]

theorem ofCheckedLayout_size (layout : CheckedLayout) :
    (ofCheckedLayout layout).style.size = Size.ofExtent layout.extent := by
  rw [ofCheckedLayout_style]
  exact Style.ofCheckedLayout_size layout

end Node

/-- Root-level lowering artifact for the exact CSS backend fragment.

The artifact carries the source-side exact contract envelope alongside the typed
backend node tree. It is still only a lowering target: no raw CSS emission or
backend-fidelity proof is claimed here. -/
structure Artifact where
  targetProfile : BlessedCssProfile
  sourceKind : LayoutKind
  sourceGuarantee : GuaranteeClass
  inputBounds : ExtentBounds
  outputBounds : ExtentBounds
  root : Node
  deriving DecidableEq, Repr

namespace Artifact

def ofCheckedWithin {available : AvailableSpace}
    (checked : CheckedWithin available) : Artifact :=
  { targetProfile := .exact1D_v1
  , sourceKind := checked.layout.kind
  , sourceGuarantee := .exact
  , inputBounds := available.bounds
  , outputBounds := checked.extentBounds
  , root := Node.ofCheckedLayout checked.layout
  }

def ofCertifiedWithin {available : AvailableSpace}
    (certified : CertifiedWithin available) : Artifact :=
  { targetProfile := .exact1D_v1
  , sourceKind := certified.contract.kind
  , sourceGuarantee := certified.contract.guarantee
  , inputBounds := certified.contract.input.bounds
  , outputBounds := certified.contract.output.bounds
  , root := Node.ofCheckedLayout certified.layout
  }

theorem ofCheckedWithin_root_kind {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).root.kind = checked.layout.kind := by
  simp [ofCheckedWithin, Node.ofCheckedLayout_kind]

theorem ofCheckedWithin_root_size {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).root.style.size = Size.ofExtent checked.extent := by
  simpa [CheckedWithin.extent, ofCheckedWithin] using Node.ofCheckedLayout_size checked.layout

theorem ofCertifiedWithin_root_kind {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).root.kind = certified.layout.kind := by
  simp [ofCertifiedWithin, Node.ofCheckedLayout_kind]

theorem ofCertifiedWithin_sourceGuarantee {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).sourceGuarantee = certified.contract.guarantee := by
  rfl

theorem ofCertifiedWithin_outputBounds {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).outputBounds = certified.contract.output.bounds := by
  rfl

theorem ofCertifiedWithin_root_size {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).root.style.size = Size.ofExtent certified.extent := by
  simpa [CertifiedWithin.extent, ofCertifiedWithin] using Node.ofCheckedLayout_size certified.layout

end Artifact

end TypedLayout.Backend.ExactCss
