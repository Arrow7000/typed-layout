import TypedLayout.Core.Geometry

namespace TypedLayout.Core

structure Gap where
  amount : Nat
  deriving DecidableEq, Repr

structure AvailableSpace where
  extent : ExactExtent
  deriving DecidableEq, Repr

inductive BlessedCssProfile where
  | exact1D_v1
  deriving DecidableEq, Repr

inductive LayoutKind where
  | leaf
  | row
  | column
  | padding
  | frame
  deriving DecidableEq, Repr

inductive GuaranteeClass where
  | exact
  | conditional (profile : BlessedCssProfile)
  | runtimeContingent
  | incompatible
  deriving DecidableEq, Repr

inductive CheckError where
  | doesNotFit (kind : LayoutKind) (available : ExactExtent) (actual : ExactExtent)
  | paddingInsetsOverflow (available : ExactExtent) (insets : Insets)
  deriving DecidableEq, Repr

inductive CheckResult (α : Type u) where
  | exact (value : α)
  | incompatible (error : CheckError)
  deriving DecidableEq, Repr

namespace CheckResult

def guaranteeClass : CheckResult α → GuaranteeClass
  | .exact _ => .exact
  | .incompatible _ => .incompatible

def map (f : α → β) : CheckResult α → CheckResult β
  | .exact value => .exact (f value)
  | .incompatible error => .incompatible error

def error? : CheckResult α → Option CheckError
  | .exact _ => none
  | .incompatible error => some error

end CheckResult

namespace ExactExtent

def stackedMain (axis : Axis) (gap : Gap) : List ExactExtent → Nat
  | [] => 0
  | child :: rest =>
      rest.foldl (fun total next => total + gap.amount + next.main axis) (child.main axis)

def stackedCross (axis : Axis) (children : List ExactExtent) : Nat :=
  children.foldl (fun total child => Nat.max total (child.cross axis)) 0

def stack (axis : Axis) (gap : Gap) (children : List ExactExtent) : ExactExtent :=
  ExactExtent.ofAxis axis (stackedMain axis gap children) (stackedCross axis children)

theorem stack_nil (axis : Axis) (gap : Gap) :
    stack axis gap [] = ExactExtent.zero := by
  cases axis <;> rfl

theorem stack_single (axis : Axis) (gap : Gap) (child : ExactExtent) :
    stack axis gap [child] = child := by
  cases axis <;> rfl

end ExactExtent

end TypedLayout.Core
