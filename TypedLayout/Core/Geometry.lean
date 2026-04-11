namespace TypedLayout.Core

inductive Axis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

structure ExactExtent where
  width : Nat
  height : Nat
  deriving DecidableEq, Repr

structure Origin where
  x : Nat
  y : Nat
  deriving DecidableEq, Repr

structure Insets where
  left : Nat
  top : Nat
  right : Nat
  bottom : Nat
  deriving DecidableEq, Repr

structure Box where
  origin : Origin
  extent : ExactExtent
  deriving DecidableEq, Repr

namespace Box

def right (box : Box) : Nat :=
  box.origin.x + box.extent.width

def bottom (box : Box) : Nat :=
  box.origin.y + box.extent.height

def fitsWithin (inner outer : Box) : Prop :=
  outer.origin.x ≤ inner.origin.x ∧
    outer.origin.y ≤ inner.origin.y ∧
    inner.right ≤ outer.right ∧
    inner.bottom ≤ outer.bottom

instance instDecidableFitsWithin (inner outer : Box) : Decidable (inner.fitsWithin outer) := by
  unfold Box.fitsWithin
  infer_instance

def separatedByAtLeastAlong (axis : Axis) (gap : Nat) (earlier later : Box) : Prop :=
  match axis with
  | .horizontal => earlier.right + gap ≤ later.origin.x
  | .vertical => earlier.bottom + gap ≤ later.origin.y

instance instDecidableSeparatedByAtLeastAlong
    (axis : Axis)
    (gap : Nat)
    (earlier later : Box) :
    Decidable (earlier.separatedByAtLeastAlong axis gap later) := by
  cases axis <;> unfold Box.separatedByAtLeastAlong <;> infer_instance

end Box

namespace Insets

def horizontal (insets : Insets) : Nat :=
  insets.left + insets.right

def vertical (insets : Insets) : Nat :=
  insets.top + insets.bottom

end Insets

namespace ExactExtent

def zero : ExactExtent :=
  { width := 0, height := 0 }

def main (extent : ExactExtent) (axis : Axis) : Nat :=
  match axis with
  | .horizontal => extent.width
  | .vertical => extent.height

def cross (extent : ExactExtent) (axis : Axis) : Nat :=
  match axis with
  | .horizontal => extent.height
  | .vertical => extent.width

def ofAxis (axis : Axis) (main cross : Nat) : ExactExtent :=
  match axis with
  | .horizontal => { width := main, height := cross }
  | .vertical => { width := cross, height := main }

def fitsWithin (extent bound : ExactExtent) : Prop :=
  extent.width ≤ bound.width ∧ extent.height ≤ bound.height

instance instDecidableFitsWithin (extent bound : ExactExtent) : Decidable (extent.fitsWithin bound) :=
  by
    unfold ExactExtent.fitsWithin
    infer_instance

def expand (inner : ExactExtent) (insets : Insets) : ExactExtent :=
  { width := insets.left + inner.width + insets.right
  , height := insets.top + inner.height + insets.bottom
  }

def inset? (outer : ExactExtent) (insets : Insets) : Option ExactExtent :=
  if insets.horizontal ≤ outer.width then
    if insets.vertical ≤ outer.height then
      some
        { width := outer.width - insets.horizontal
        , height := outer.height - insets.vertical
        }
    else
      none
  else
    none

theorem ofAxis_main (axis : Axis) (main cross : Nat) :
    (ofAxis axis main cross).main axis = main := by
  cases axis <;> rfl

theorem ofAxis_cross (axis : Axis) (main cross : Nat) :
    (ofAxis axis main cross).cross axis = cross := by
  cases axis <;> rfl

theorem fitsWithin_refl (extent : ExactExtent) : extent.fitsWithin extent := by
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

end ExactExtent

namespace Origin

def zero : Origin :=
  { x := 0, y := 0 }

def translate (origin : Origin) (dx dy : Nat) : Origin :=
  { x := origin.x + dx, y := origin.y + dy }

def translateAxis (origin : Origin) (axis : Axis) (amount : Nat) : Origin :=
  match axis with
  | .horizontal => origin.translate amount 0
  | .vertical => origin.translate 0 amount

end Origin

end TypedLayout.Core
