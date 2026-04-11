import TypedLayout.Core.Check

namespace TypedLayout.Core

structure GeometryTree where
  box : Box
  children : List GeometryTree
  deriving Repr

namespace GeometryTree

def origin (tree : GeometryTree) : Origin :=
  tree.box.origin

def extent (tree : GeometryTree) : ExactExtent :=
  tree.box.extent

end GeometryTree

def AdjacentSeparatedAlong (axis : Axis) (gap : Gap) : List GeometryTree → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      first.box.separatedByAtLeastAlong axis gap.amount second.box ∧
        AdjacentSeparatedAlong axis gap (second :: rest)

namespace CheckedLayout

mutual

def evaluateAt (layout : CheckedLayout) (origin : Origin) : GeometryTree :=
  match layout with
  | .leaf extent =>
      { box := { origin := origin, extent := extent }, children := [] }
  | .row gap children =>
      { box := { origin := origin, extent := layout.extent }
      , children := evaluateChildrenAlong .horizontal origin gap 0 children
      }
  | .column gap children =>
      { box := { origin := origin, extent := layout.extent }
      , children := evaluateChildrenAlong .vertical origin gap 0 children
      }
  | .padding insets child =>
      { box := { origin := origin, extent := layout.extent }
      , children := [evaluateAt child (origin.translate insets.left insets.top)]
      }
  | .frame extent child =>
      { box := { origin := origin, extent := extent }
      , children := [evaluateAt child origin]
      }

termination_by
  sizeOf layout

decreasing_by
  all_goals simp_wf
  all_goals omega

def evaluateChildrenAlong
    (axis : Axis)
    (origin : Origin)
    (gap : Gap)
    (cursor : Nat)
    : List CheckedLayout → List GeometryTree
  | [] => []
  | child :: rest =>
      let childOrigin := origin.translateAxis axis cursor
      let childTree := evaluateAt child childOrigin
      let nextCursor := cursor + child.mainExtent axis + gap.amount
      childTree :: evaluateChildrenAlong axis origin gap nextCursor rest

termination_by
  children => sizeOf children

decreasing_by
  all_goals simp_wf
  all_goals omega

end

def evaluate (layout : CheckedLayout) : GeometryTree :=
  layout.evaluateAt Origin.zero

theorem evaluateAt_boxExtent (layout : CheckedLayout) (origin : Origin) :
    (layout.evaluateAt origin).box.extent = layout.extent := by
  cases layout <;> simp [evaluateAt, CheckedLayout.extent]

theorem evaluateAt_boxOrigin (layout : CheckedLayout) (origin : Origin) :
    (layout.evaluateAt origin).box.origin = origin := by
  cases layout <;> simp [evaluateAt]

theorem evaluateAt_box (layout : CheckedLayout) (origin : Origin) :
    (layout.evaluateAt origin).box = { origin := origin, extent := layout.extent } := by
  cases layout <;> simp [evaluateAt, CheckedLayout.extent]

theorem evaluateChildrenAlong_cons
    (axis : Axis)
    (origin : Origin)
    (gap : Gap)
    (cursor : Nat)
    (child : CheckedLayout)
    (rest : List CheckedLayout) :
    evaluateChildrenAlong axis origin gap cursor (child :: rest) =
      child.evaluateAt (origin.translateAxis axis cursor) ::
        evaluateChildrenAlong axis origin gap (cursor + child.mainExtent axis + gap.amount) rest := by
  simp [evaluateChildrenAlong]

theorem evaluateChildrenAlong_adjacentSeparated
    (axis : Axis)
    (origin : Origin)
    (gap : Gap)
    (cursor : Nat)
    (children : List CheckedLayout) :
    AdjacentSeparatedAlong axis gap (evaluateChildrenAlong axis origin gap cursor children) := by
  induction children generalizing cursor with
  | nil =>
      simp [evaluateChildrenAlong, AdjacentSeparatedAlong]
  | cons child rest ih =>
      cases rest with
      | nil =>
          simp [evaluateChildrenAlong, AdjacentSeparatedAlong]
      | cons next tail =>
          simp [evaluateChildrenAlong, AdjacentSeparatedAlong]
          constructor
          · cases axis with
            | horizontal =>
                unfold Box.separatedByAtLeastAlong Box.right
                rw [evaluateAt_boxOrigin child (origin.translateAxis .horizontal cursor)]
                rw [evaluateAt_boxExtent child (origin.translateAxis .horizontal cursor)]
                rw [evaluateAt_boxOrigin next
                  (origin.translateAxis .horizontal (cursor + child.mainExtent .horizontal + gap.amount))]
                simp [Origin.translateAxis, Origin.translate, CheckedLayout.mainExtent,
                  ExactExtent.main]
                omega
            | vertical =>
                unfold Box.separatedByAtLeastAlong Box.bottom
                rw [evaluateAt_boxOrigin child (origin.translateAxis .vertical cursor)]
                rw [evaluateAt_boxExtent child (origin.translateAxis .vertical cursor)]
                rw [evaluateAt_boxOrigin next
                  (origin.translateAxis .vertical (cursor + child.mainExtent .vertical + gap.amount))]
                simp [Origin.translateAxis, Origin.translate, CheckedLayout.mainExtent,
                  ExactExtent.main]
                omega
          · simpa [evaluateChildrenAlong] using ih (cursor + child.mainExtent axis + gap.amount)

end CheckedLayout

namespace CheckedWithin

def evaluate {available : AvailableSpace} (checked : CheckedWithin available) : GeometryTree :=
  checked.layout.evaluate

end CheckedWithin

end TypedLayout.Core
