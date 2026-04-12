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

def isExact : CheckResult α → Bool
  | .exact _ => true
  | .incompatible _ => false

def hasError (expected : CheckError) : CheckResult α → Bool
  | .exact _ => false
  | .incompatible error => decide (error = expected)

end CheckResult

namespace ExactExtent

def stackedMain (axis : Axis) (gap : Gap) : List ExactExtent → Nat
  | [] => 0
  | [child] => child.main axis
  | child :: next :: rest => child.main axis + gap.amount + stackedMain axis gap (next :: rest)

def stackedCross (axis : Axis) (children : List ExactExtent) : Nat :=
  match children with
  | [] => 0
  | child :: rest => Nat.max (child.cross axis) (stackedCross axis rest)

def stack (axis : Axis) (gap : Gap) (children : List ExactExtent) : ExactExtent :=
  ExactExtent.ofAxis axis (stackedMain axis gap children) (stackedCross axis children)

theorem stack_nil (axis : Axis) (gap : Gap) :
    stack axis gap [] = ExactExtent.zero := by
  cases axis <;> rfl

theorem stack_single (axis : Axis) (gap : Gap) (child : ExactExtent) :
    stack axis gap [child] = child := by
  cases axis <;> simp [stack, stackedMain, stackedCross, ExactExtent.ofAxis, ExactExtent.main, ExactExtent.cross]

theorem stackedMain_cons_cons (axis : Axis) (gap : Gap) (child next : ExactExtent) (rest : List ExactExtent) :
    stackedMain axis gap (child :: next :: rest) =
      child.main axis + gap.amount + stackedMain axis gap (next :: rest) := by
  rfl

theorem stackedCross_cons (axis : Axis) (child : ExactExtent) (rest : List ExactExtent) :
    stackedCross axis (child :: rest) = Nat.max (child.cross axis) (stackedCross axis rest) := by
  rfl

theorem stackedCross_tail_le_cons (axis : Axis) (child : ExactExtent) (rest : List ExactExtent) :
    stackedCross axis rest ≤ stackedCross axis (child :: rest) := by
  simpa [stackedCross_cons] using (Nat.le_max_right (child.cross axis) (stackedCross axis rest))

theorem cross_le_stackedCross_of_mem
    (axis : Axis)
    (target : ExactExtent)
    (children : List ExactExtent)
    (h : target ∈ children) :
    target.cross axis ≤ stackedCross axis children := by
  induction children with
  | nil =>
      cases h
  | cons child rest ih =>
      simp only [List.mem_cons] at h
      simp [stackedCross_cons]
      cases h with
      | inl targetEq =>
          subst target
          exact Nat.le_max_left _ _
      | inr targetMem =>
          exact Nat.le_trans (ih targetMem) (Nat.le_max_right _ _)

end ExactExtent

end TypedLayout.Core
