import TypedLayout.Core.Domain

namespace TypedLayout.Core

inductive Layout where
  | leaf (extent : ExactExtent)
  | row (gap : Gap) (children : List Layout)
  | column (gap : Gap) (children : List Layout)
  | padding (insets : Insets) (child : Layout)
  | frame (extent : ExactExtent) (child : Layout)
  deriving Repr

namespace Layout

def kind : Layout → LayoutKind
  | .leaf _ => .leaf
  | .row _ _ => .row
  | .column _ _ => .column
  | .padding _ _ => .padding
  | .frame _ _ => .frame

end Layout

end TypedLayout.Core
