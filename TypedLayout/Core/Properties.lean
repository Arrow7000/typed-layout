import TypedLayout.Core.Eval

namespace TypedLayout.Core

def ImmediateChildrenFitWithin (tree : GeometryTree) : Prop :=
  ∀ child ∈ tree.children, child.box.fitsWithin tree.box

namespace Box

theorem fitsWithin_refl (box : Box) : box.fitsWithin box := by
  unfold Box.fitsWithin Box.right Box.bottom
  omega

theorem sameOriginFitsWithin_of_extentFits
    (origin : Origin)
    {inner outer : ExactExtent}
    (h : inner.fitsWithin outer) :
    ({ origin := origin, extent := inner } : Box).fitsWithin { origin := origin, extent := outer } := by
  rcases h with ⟨widthFits, heightFits⟩
  unfold Box.fitsWithin Box.right Box.bottom
  simp [widthFits, heightFits]

theorem translatedInsetFitsWithinExpanded
    (origin : Origin)
    (inner : ExactExtent)
    (insets : Insets) :
    ({ origin := origin.translate insets.left insets.top, extent := inner } : Box).fitsWithin
      { origin := origin, extent := inner.expand insets } := by
  unfold Box.fitsWithin Box.right Box.bottom Origin.translate ExactExtent.expand
  simp
  omega

end Box

namespace GeometryTree

theorem immediateChildrenFitWithin_leaf (extent : ExactExtent) (origin : Origin) :
    ImmediateChildrenFitWithin
      { box := { origin := origin, extent := extent }, children := [] } := by
  intro child childMem
  cases childMem

end GeometryTree

namespace CheckedLayout

theorem evaluateAt_row_childrenAdjacentSeparated
    (gap : Gap)
    (children : List CheckedLayout)
    (origin : Origin) :
    AdjacentSeparatedAlong .horizontal gap ((CheckedLayout.row gap children).evaluateAt origin).children := by
  simpa [evaluateAt] using evaluateChildrenAlong_adjacentSeparated .horizontal origin gap 0 children

theorem evaluateAt_column_childrenAdjacentSeparated
    (gap : Gap)
    (children : List CheckedLayout)
    (origin : Origin) :
    AdjacentSeparatedAlong .vertical gap ((CheckedLayout.column gap children).evaluateAt origin).children := by
  simpa [evaluateAt] using evaluateChildrenAlong_adjacentSeparated .vertical origin gap 0 children

theorem evaluateAt_padding_immediateChildrenFitWithin
    (insets : Insets)
    (child : CheckedLayout)
    (origin : Origin) :
    ImmediateChildrenFitWithin ((CheckedLayout.padding insets child).evaluateAt origin) := by
  intro childTree childMem
  simp [CheckedLayout.evaluateAt] at childMem
  rcases childMem with rfl
  rw [CheckedLayout.evaluateAt_box child (origin.translate insets.left insets.top)]
  rw [CheckedLayout.evaluateAt_box (CheckedLayout.padding insets child) origin]
  simpa [CheckedLayout.extent] using
    Box.translatedInsetFitsWithinExpanded origin child.extent insets

theorem evaluateAt_frame_immediateChildrenFitWithin
    (extent : ExactExtent)
    (child : CheckedLayout)
    (origin : Origin)
    (h : child.extent.fitsWithin extent) :
    ImmediateChildrenFitWithin ((CheckedLayout.frame extent child).evaluateAt origin) := by
  intro childTree childMem
  simp [CheckedLayout.evaluateAt] at childMem
  rcases childMem with rfl
  rw [CheckedLayout.evaluateAt_box child origin]
  rw [CheckedLayout.evaluateAt_box (CheckedLayout.frame extent child) origin]
  simpa [CheckedLayout.extent] using Box.sameOriginFitsWithin_of_extentFits origin h

end CheckedLayout

end TypedLayout.Core
