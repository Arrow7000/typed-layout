namespace TypedLayout

[<Struct>]
type Px =
    private
    | Px of int

[<RequireQualifiedAccess>]
module Px =
    let create value =
        if value < 0 then
            invalidArg (nameof value) "CSS box dimensions cannot be negative in this POC."

        Px value

    let value (Px value) = value
    let zero = Px 0
    let add (Px left) (Px right) = Px(left + right)
    let multiply count (Px value) = Px(count * value)
    let max (Px left) (Px right) = Px(System.Math.Max(left, right))
    let format (Px value) = $"{value}px"

type ExactSize =
    { Width: Px
      Height: Px }

type Viewport =
    { Width: Px
      Height: Px }

/// The stylesheet environment is deliberately present at the first inference
/// boundary. POC 1 implements only the empty cascade.
[<RequireQualifiedAccess>]
type StyleEnvironment =
    | Empty

type TargetEnvironment =
    { Name: string
      Viewport: Viewport
      Stylesheet: StyleEnvironment }

type ContainingBlock =
    { Width: Px
      Height: Px option }
