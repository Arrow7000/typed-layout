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
      ExactExtent.stack .horizontal gap (children.map CheckedLayout.extent)
  | .column gap children =>
      ExactExtent.stack .vertical gap (children.map CheckedLayout.extent)
  | .padding insets child =>
      child.extent.expand insets
  | .frame extent _ =>
      extent

def mainExtent (layout : CheckedLayout) (axis : Axis) : Nat :=
  layout.extent.main axis

def crossExtent (layout : CheckedLayout) (axis : Axis) : Nat :=
  layout.extent.cross axis

def extentBounds (layout : CheckedLayout) : ExtentBounds :=
  layout.extent.toBounds

theorem extentBounds_contains_extent (layout : CheckedLayout) :
    layout.extentBounds.contains layout.extent :=
  ExactExtent.toBounds_contains_self layout.extent

end CheckedLayout

structure CheckedWithin (available : AvailableSpace) where
  layout : CheckedLayout
  fits : layout.extent.fitsWithin available.extent

namespace CheckedWithin

def extent {available : AvailableSpace} (checked : CheckedWithin available) : ExactExtent :=
  checked.layout.extent

def childLayouts {available : AvailableSpace} (children : List (CheckedWithin available)) : List CheckedLayout :=
  children.map CheckedWithin.layout

def extentBounds {available : AvailableSpace} (checked : CheckedWithin available) : ExtentBounds :=
  checked.extent.toBounds

theorem extentBounds_within_availableBounds {available : AvailableSpace}
    (checked : CheckedWithin available) :
    available.bounds.containsBounds checked.extentBounds := by
  exact ⟨⟨Nat.zero_le _, checked.fits.1⟩, ⟨Nat.zero_le _, checked.fits.2⟩⟩

end CheckedWithin

mutual

def checkWithin (available : AvailableSpace) : Layout → CheckResult (CheckedWithin available)
  | .leaf extent =>
      if fits : extent.fitsWithin available.extent then
        .exact { layout := .leaf extent, fits := by simpa [CheckedLayout.extent] using fits }
      else
        .incompatible (.doesNotFit .leaf available.extent extent)
  | .row gap children =>
      match checkChildrenWithin available children with
      | .incompatible error => .incompatible error
      | .exact checkedChildren =>
          let checked : CheckedLayout := .row gap (CheckedWithin.childLayouts checkedChildren)
          if fits : checked.extent.fitsWithin available.extent then
            .exact { layout := checked, fits := fits }
          else
            .incompatible (.doesNotFit .row available.extent checked.extent)
  | .column gap children =>
      match checkChildrenWithin available children with
      | .incompatible error => .incompatible error
      | .exact checkedChildren =>
          let checked : CheckedLayout := .column gap (CheckedWithin.childLayouts checkedChildren)
          if fits : checked.extent.fitsWithin available.extent then
            .exact { layout := checked, fits := fits }
          else
            .incompatible (.doesNotFit .column available.extent checked.extent)
  | .padding insets child =>
      match available.extent.inset? insets with
      | none => .incompatible (.paddingInsetsOverflow available.extent insets)
      | some innerExtent =>
          match checkWithin { extent := innerExtent } child with
          | .incompatible error => .incompatible error
          | .exact checkedChild =>
              let checked : CheckedLayout := .padding insets checkedChild.layout
              if fits : checked.extent.fitsWithin available.extent then
                .exact { layout := checked, fits := fits }
              else
                .incompatible (.doesNotFit .padding available.extent checked.extent)
  | .frame extent child =>
      if frameFits : extent.fitsWithin available.extent then
        match checkWithin { extent := extent } child with
        | .incompatible error => .incompatible error
        | .exact checkedChild =>
            .exact
              { layout := .frame extent checkedChild.layout
              , fits := by simpa [CheckedLayout.extent] using frameFits
              }
      else
        .incompatible (.doesNotFit .frame available.extent extent)

termination_by
  layout => sizeOf layout

decreasing_by
  all_goals simp_wf
  all_goals omega

def checkChildrenWithin (available : AvailableSpace) : List Layout → CheckResult (List (CheckedWithin available))
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

def check (available : AvailableSpace) (layout : Layout) : CheckResult (CheckedWithin available) :=
  checkWithin available layout

end TypedLayout.Core
