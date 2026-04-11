import TypedLayout.Core.Ast

namespace TypedLayout.Core

inductive CheckedLayout where
  | leaf (extent : ExactExtent)
  | row (gap : Gap) (children : List CheckedLayout)
  | column (gap : Gap) (children : List CheckedLayout)
  | padding (insets : Insets) (child : CheckedLayout)
  | frame (extent : ExactExtent) (child : CheckedLayout)
  deriving Repr

namespace CheckedLayout

def kind : CheckedLayout → LayoutKind
  | .leaf _ => .leaf
  | .row _ _ => .row
  | .column _ _ => .column
  | .padding _ _ => .padding
  | .frame _ _ => .frame

def extent : CheckedLayout → ExactExtent
  | .leaf extent => extent
  | .row gap children =>
      let width :=
        match children with
        | [] => 0
        | child :: rest =>
            rest.foldl (fun total next => total + gap.amount + next.extent.width) child.extent.width
      let height :=
        children.foldl (fun total child => Nat.max total child.extent.height) 0
      { width := width, height := height }
  | .column gap children =>
      let width :=
        children.foldl (fun total child => Nat.max total child.extent.width) 0
      let height :=
        match children with
        | [] => 0
        | child :: rest =>
            rest.foldl (fun total next => total + gap.amount + next.extent.height) child.extent.height
      { width := width, height := height }
  | .padding insets child =>
      child.extent.expand insets
  | .frame extent _ =>
      extent

def mainExtent (layout : CheckedLayout) (axis : Axis) : Nat :=
  layout.extent.main axis

def crossExtent (layout : CheckedLayout) (axis : Axis) : Nat :=
  layout.extent.cross axis

end CheckedLayout

mutual

def checkWithin (available : AvailableSpace) : Layout → CheckResult CheckedLayout
  | .leaf extent =>
      if extent.fitsWithin available.extent then
        .exact (.leaf extent)
      else
        .incompatible (.doesNotFit .leaf available.extent extent)
  | .row gap children =>
      match checkChildrenWithin available children with
      | .incompatible error => .incompatible error
      | .exact checkedChildren =>
          let checked : CheckedLayout := .row gap checkedChildren
          if checked.extent.fitsWithin available.extent then
            .exact checked
          else
            .incompatible (.doesNotFit .row available.extent checked.extent)
  | .column gap children =>
      match checkChildrenWithin available children with
      | .incompatible error => .incompatible error
      | .exact checkedChildren =>
          let checked : CheckedLayout := .column gap checkedChildren
          if checked.extent.fitsWithin available.extent then
            .exact checked
          else
            .incompatible (.doesNotFit .column available.extent checked.extent)
  | .padding insets child =>
      match available.extent.inset? insets with
      | none => .incompatible (.paddingInsetsOverflow available.extent insets)
      | some innerExtent =>
          match checkWithin { extent := innerExtent } child with
          | .incompatible error => .incompatible error
          | .exact checkedChild =>
              let checked : CheckedLayout := .padding insets checkedChild
              if checked.extent.fitsWithin available.extent then
                .exact checked
              else
                .incompatible (.doesNotFit .padding available.extent checked.extent)
  | .frame extent child =>
      if extent.fitsWithin available.extent then
        match checkWithin { extent := extent } child with
        | .incompatible error => .incompatible error
        | .exact checkedChild => .exact (.frame extent checkedChild)
      else
        .incompatible (.doesNotFit .frame available.extent extent)

termination_by
  layout => sizeOf layout

decreasing_by
  all_goals simp_wf
  all_goals omega

def checkChildrenWithin (available : AvailableSpace) : List Layout → CheckResult (List CheckedLayout)
  | [] => .exact []
  | child :: rest =>
      match checkWithin available child with
      | .incompatible error => .incompatible error
      | .exact checkedChild =>
          match checkChildrenWithin available rest with
          | .incompatible error => .incompatible error
          | .exact checkedRest => .exact (checkedChild :: checkedRest)

termination_by
  children => sizeOf children

decreasing_by
  all_goals simp_wf
  all_goals omega

end

def check (available : AvailableSpace) (layout : Layout) : CheckResult CheckedLayout :=
  checkWithin available layout

end TypedLayout.Core
