import TypedLayout.Core.Geometry

namespace TypedLayout.Core

structure Gap where
  amount : Nat
  deriving DecidableEq, Repr

structure AvailableSpace where
  extent : ExactExtent
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

end CheckResult

end TypedLayout.Core
