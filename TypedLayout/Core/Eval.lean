import TypedLayout.Core.Check

namespace TypedLayout.Core

structure GeometryTree where
  origin : Origin
  extent : ExactExtent
  children : List GeometryTree
  deriving Repr

namespace CheckedLayout

mutual

def evaluateAt (layout : CheckedLayout) (origin : Origin) : GeometryTree :=
  match layout with
  | .leaf extent =>
      { origin := origin, extent := extent, children := [] }
  | .row gap children =>
      { origin := origin
      , extent := layout.extent
      , children := evaluateChildrenAlong .horizontal origin gap 0 children
      }
  | .column gap children =>
      { origin := origin
      , extent := layout.extent
      , children := evaluateChildrenAlong .vertical origin gap 0 children
      }
  | .padding insets child =>
      { origin := origin
      , extent := layout.extent
      , children := [evaluateAt child (origin.translate insets.left insets.top)]
      }
  | .frame extent child =>
      { origin := origin
      , extent := extent
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

theorem evaluateHorizontalChildren_cons
    (origin : Origin)
    (gap : Gap)
    (cursor : Nat)
    (child : CheckedLayout)
    (rest : List CheckedLayout) :
    evaluateChildrenAlong .horizontal origin gap cursor (child :: rest) =
      child.evaluateAt (origin.translateAxis .horizontal cursor) ::
        evaluateChildrenAlong .horizontal origin gap (cursor + child.mainExtent .horizontal + gap.amount) rest := by
  simp [evaluateChildrenAlong]

theorem evaluateVerticalChildren_cons
    (origin : Origin)
    (gap : Gap)
    (cursor : Nat)
    (child : CheckedLayout)
    (rest : List CheckedLayout) :
    evaluateChildrenAlong .vertical origin gap cursor (child :: rest) =
      child.evaluateAt (origin.translateAxis .vertical cursor) ::
        evaluateChildrenAlong .vertical origin gap (cursor + child.mainExtent .vertical + gap.amount) rest := by
  simp [evaluateChildrenAlong]

end CheckedLayout

end TypedLayout.Core
