import TypedLayout.Core.Geometry

namespace TypedLayout.Core

structure Gap where
  amount : Nat
  deriving DecidableEq, Repr

structure AvailableSpace where
  extent : ExactExtent
  deriving DecidableEq, Repr

structure AxisBounds where
  lower : Nat
  upper : Nat
  lower_le_upper : lower ≤ upper
  deriving DecidableEq, Repr

structure ExtentBounds where
  width : AxisBounds
  height : AxisBounds
  deriving DecidableEq, Repr

namespace AxisBounds

def exact (size : Nat) : AxisBounds :=
  { lower := size
  , upper := size
  , lower_le_upper := Nat.le_refl size
  }

def upTo (size : Nat) : AxisBounds :=
  { lower := 0
  , upper := size
  , lower_le_upper := Nat.zero_le size
  }

def contains (bounds : AxisBounds) (size : Nat) : Prop :=
  bounds.lower ≤ size ∧ size ≤ bounds.upper

instance instDecidableContains (bounds : AxisBounds) (size : Nat) :
    Decidable (bounds.contains size) := by
  unfold AxisBounds.contains
  infer_instance

def containsBounds (outer inner : AxisBounds) : Prop :=
  outer.lower ≤ inner.lower ∧ inner.upper ≤ outer.upper

instance instDecidableContainsBounds (outer inner : AxisBounds) :
    Decidable (outer.containsBounds inner) := by
  unfold AxisBounds.containsBounds
  infer_instance

def compatibleWith (left right : AxisBounds) : Prop :=
  left.lower ≤ right.upper ∧ right.lower ≤ left.upper

instance instDecidableCompatibleWith (left right : AxisBounds) :
    Decidable (left.compatibleWith right) := by
  unfold AxisBounds.compatibleWith
  infer_instance

theorem exact_contains (size : Nat) :
    (exact size).contains size := by
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem exact_contains_iff {size candidate : Nat} :
    (exact size).contains candidate ↔ candidate = size := by
  constructor
  · intro h
    exact Nat.le_antisymm h.2 h.1
  · intro h
    cases h
    exact exact_contains size

theorem contains_of_containsBounds
    {outer inner : AxisBounds}
    (hOuter : outer.containsBounds inner)
    {size : Nat}
    (hInner : inner.contains size) :
    outer.contains size := by
  exact ⟨Nat.le_trans hOuter.1 hInner.1, Nat.le_trans hInner.2 hOuter.2⟩

theorem containsBounds_refl (bounds : AxisBounds) :
    bounds.containsBounds bounds := by
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem containsBounds_of_contains
    {outer : AxisBounds}
    {size : Nat}
    (h : outer.contains size) :
    outer.containsBounds (exact size) := by
  exact h

theorem compatibleWith_refl (bounds : AxisBounds) :
    bounds.compatibleWith bounds := by
  exact ⟨bounds.lower_le_upper, bounds.lower_le_upper⟩

theorem compatibleWith_comm (left right : AxisBounds) :
    left.compatibleWith right ↔ right.compatibleWith left := by
  constructor <;> intro h <;> exact ⟨h.2, h.1⟩

theorem compatibleWith_exact_iff_contains
    {bounds : AxisBounds}
    {size : Nat} :
    bounds.compatibleWith (exact size) ↔ bounds.contains size := by
  rfl

theorem compatibleWith_of_containsBounds_left
    {outer inner other : AxisBounds}
    (hContain : outer.containsBounds inner)
    (hCompat : inner.compatibleWith other) :
    outer.compatibleWith other := by
  exact ⟨Nat.le_trans hContain.1 hCompat.1, Nat.le_trans hCompat.2 hContain.2⟩

theorem compatibleWith_of_containsBounds_right
    {left outer inner : AxisBounds}
    (hCompat : left.compatibleWith inner)
    (hContain : outer.containsBounds inner) :
    left.compatibleWith outer := by
  exact ⟨Nat.le_trans hCompat.1 hContain.2, Nat.le_trans hContain.1 hCompat.2⟩

end AxisBounds

namespace ExtentBounds

def exact (extent : ExactExtent) : ExtentBounds :=
  { width := AxisBounds.exact extent.width
  , height := AxisBounds.exact extent.height
  }

def upTo (extent : ExactExtent) : ExtentBounds :=
  { width := AxisBounds.upTo extent.width
  , height := AxisBounds.upTo extent.height
  }

def contains (bounds : ExtentBounds) (extent : ExactExtent) : Prop :=
  bounds.width.contains extent.width ∧ bounds.height.contains extent.height

instance instDecidableContains (bounds : ExtentBounds) (extent : ExactExtent) :
    Decidable (bounds.contains extent) := by
  unfold ExtentBounds.contains
  infer_instance

def containsBounds (outer inner : ExtentBounds) : Prop :=
  outer.width.containsBounds inner.width ∧ outer.height.containsBounds inner.height

instance instDecidableContainsBounds (outer inner : ExtentBounds) :
    Decidable (outer.containsBounds inner) := by
  unfold ExtentBounds.containsBounds
  infer_instance

def compatibleWith (left right : ExtentBounds) : Prop :=
  left.width.compatibleWith right.width ∧ left.height.compatibleWith right.height

instance instDecidableCompatibleWith (left right : ExtentBounds) :
    Decidable (left.compatibleWith right) := by
  unfold ExtentBounds.compatibleWith
  infer_instance

theorem exact_contains (extent : ExactExtent) :
    (exact extent).contains extent := by
  exact ⟨AxisBounds.exact_contains _, AxisBounds.exact_contains _⟩

theorem contains_of_containsBounds
    {outer inner : ExtentBounds}
    (hOuter : outer.containsBounds inner)
    {extent : ExactExtent}
    (hInner : inner.contains extent) :
    outer.contains extent := by
  exact
    ⟨ AxisBounds.contains_of_containsBounds hOuter.1 hInner.1
    , AxisBounds.contains_of_containsBounds hOuter.2 hInner.2
    ⟩

theorem containsBounds_refl (bounds : ExtentBounds) :
    bounds.containsBounds bounds := by
  exact ⟨AxisBounds.containsBounds_refl _, AxisBounds.containsBounds_refl _⟩

theorem containsBounds_of_contains
    {outer : ExtentBounds}
    {extent : ExactExtent}
    (h : outer.contains extent) :
    outer.containsBounds (exact extent) := by
  exact
    ⟨ AxisBounds.containsBounds_of_contains h.1
    , AxisBounds.containsBounds_of_contains h.2
    ⟩

theorem compatibleWith_refl (bounds : ExtentBounds) :
    bounds.compatibleWith bounds := by
  exact ⟨AxisBounds.compatibleWith_refl _, AxisBounds.compatibleWith_refl _⟩

theorem compatibleWith_comm (left right : ExtentBounds) :
    left.compatibleWith right ↔ right.compatibleWith left := by
  constructor
  · intro h
    exact
      ⟨ (AxisBounds.compatibleWith_comm _ _).mp h.1
      , (AxisBounds.compatibleWith_comm _ _).mp h.2
      ⟩
  · intro h
    exact
      ⟨ (AxisBounds.compatibleWith_comm _ _).mp h.1
      , (AxisBounds.compatibleWith_comm _ _).mp h.2
      ⟩

theorem compatibleWith_exact_iff_contains
    {bounds : ExtentBounds}
    {extent : ExactExtent} :
    bounds.compatibleWith (exact extent) ↔ bounds.contains extent := by
  rfl

theorem compatibleWith_of_containsBounds_left
    {outer inner other : ExtentBounds}
    (hContain : outer.containsBounds inner)
    (hCompat : inner.compatibleWith other) :
    outer.compatibleWith other := by
  exact
    ⟨ AxisBounds.compatibleWith_of_containsBounds_left hContain.1 hCompat.1
    , AxisBounds.compatibleWith_of_containsBounds_left hContain.2 hCompat.2
    ⟩

theorem compatibleWith_of_containsBounds_right
    {left outer inner : ExtentBounds}
    (hCompat : left.compatibleWith inner)
    (hContain : outer.containsBounds inner) :
    left.compatibleWith outer := by
  exact
    ⟨ AxisBounds.compatibleWith_of_containsBounds_right hCompat.1 hContain.1
    , AxisBounds.compatibleWith_of_containsBounds_right hCompat.2 hContain.2
    ⟩

end ExtentBounds

namespace ExactExtent

def toBounds (extent : ExactExtent) : ExtentBounds :=
  ExtentBounds.exact extent

def upToBounds (extent : ExactExtent) : ExtentBounds :=
  ExtentBounds.upTo extent

theorem toBounds_contains_self (extent : ExactExtent) :
    extent.toBounds.contains extent :=
  ExtentBounds.exact_contains extent

theorem fitsWithin_iff_upToBounds_contains
    {extent bound : ExactExtent} :
    extent.fitsWithin bound ↔ bound.upToBounds.contains extent := by
  constructor
  · intro h
    exact ⟨⟨Nat.zero_le _, h.1⟩, ⟨Nat.zero_le _, h.2⟩⟩
  · intro h
    exact ⟨h.1.2, h.2.2⟩

end ExactExtent

namespace AvailableSpace

def bounds (available : AvailableSpace) : ExtentBounds :=
  available.extent.upToBounds

end AvailableSpace

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
