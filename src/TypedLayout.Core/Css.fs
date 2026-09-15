namespace TypedLayout

[<RequireQualifiedAccess>]
type Display =
    | Inline
    | Block
    | Flex

[<RequireQualifiedAccess>]
type FlexDirection =
    | Row
    | Column

[<RequireQualifiedAccess>]
type PreferredSize =
    | Auto
    | Length of Px

[<RequireQualifiedAccess>]
type Gap =
    | Normal
    | Length of Px

[<RequireQualifiedAccess>]
type Declaration =
    | Display of Display
    | Width of PreferredSize
    | Height of PreferredSize
    | FlexDirection of FlexDirection
    | Gap of Gap
    | FlexShrink of decimal

[<RequireQualifiedAccess>]
type ValueSource =
    | Initial
    | LocalDeclaration

type Sourced<'value> =
    { Value: 'value
      Source: ValueSource }

type SpecifiedStyle =
    { Display: Sourced<Display>
      Width: Sourced<PreferredSize>
      Height: Sourced<PreferredSize>
      FlexDirection: Sourced<FlexDirection>
      Gap: Sourced<Gap>
      FlexShrink: Sourced<decimal> }

[<RequireQualifiedAccess>]
module SpecifiedStyle =
    let initial =
        { Display =
            { Value = Display.Inline
              Source = ValueSource.Initial }
          Width =
            { Value = PreferredSize.Auto
              Source = ValueSource.Initial }
          Height =
            { Value = PreferredSize.Auto
              Source = ValueSource.Initial }
          FlexDirection =
            { Value = FlexDirection.Row
              Source = ValueSource.Initial }
          Gap =
            { Value = Gap.Normal
              Source = ValueSource.Initial }
          FlexShrink =
            { Value = 1M
              Source = ValueSource.Initial } }

    let private local value =
        { Value = value
          Source = ValueSource.LocalDeclaration }

    /// POC 1's cascade: local declarations are applied in source order over CSS
    /// initial values. A later declaration of the same property wins.
    let resolveLocal declarations =
        (initial, declarations)
        ||> List.fold (fun style declaration ->
            match declaration with
            | Declaration.Display value -> { style with Display = local value }
            | Declaration.Width value -> { style with Width = local value }
            | Declaration.Height value -> { style with Height = local value }
            | Declaration.FlexDirection value -> { style with FlexDirection = local value }
            | Declaration.Gap value -> { style with Gap = local value }
            | Declaration.FlexShrink value ->
                if value < 0M then
                    invalidArg (nameof declarations) "flex-shrink cannot be negative."

                { style with FlexShrink = local value })

    let usedGap style =
        match style.Gap.Value with
        | Gap.Normal -> Px.zero
        | Gap.Length length -> length
