namespace TypedLayout

open System.Text

[<RequireQualifiedAccess>]
module Pretty =
    let private display = function
        | Display.Inline -> "inline"
        | Display.Block -> "block"
        | Display.Flex -> "flex"

    let private flexDirection = function
        | FlexDirection.Row -> "row"
        | FlexDirection.Column -> "column"

    let private preferredSize = function
        | PreferredSize.Auto -> "auto"
        | PreferredSize.Length length -> Px.format length

    let private gap = function
        | Gap.Normal -> "normal"
        | Gap.Length length -> Px.format length

    let private appendNonInitial (builder: StringBuilder) name sourced initialValue render =
        if sourced.Value <> initialValue then
            builder.AppendLine($"    , {name} = {render sourced.Value}") |> ignore

    /// Render the compact, hover-oriented view. Initial-valued properties are
    /// omitted, while derived used geometry is labelled separately.
    let layoutType layoutType =
        let style = layoutType.SpecifiedStyle
        let builder = StringBuilder()
        builder.AppendLine($"{layoutType.ElementName} : Element") |> ignore
        builder.AppendLine("    { css") |> ignore
        appendNonInitial builder "display" style.Display Display.Inline display
        appendNonInitial builder "width" style.Width PreferredSize.Auto preferredSize
        appendNonInitial builder "height" style.Height PreferredSize.Auto preferredSize
        appendNonInitial builder "flex-direction" style.FlexDirection FlexDirection.Row flexDirection
        appendNonInitial builder "gap" style.Gap Gap.Normal gap
        appendNonInitial builder "flex-shrink" style.FlexShrink 1M string
        builder.AppendLine($"    ; used-width = {Px.format layoutType.UsedSize.Width}") |> ignore
        builder.AppendLine($"    ; used-height = {Px.format layoutType.UsedSize.Height}") |> ignore
        builder.AppendLine($"    ; children-require-width = {Px.format layoutType.ContentRequirements.Width}") |> ignore
        builder.AppendLine("    ; children-contained = true") |> ignore
        builder.Append("    }") |> ignore
        builder.ToString()

    let typeError = function
        | TypeError.Unsupported(name, reason) -> $"Cannot infer layout for '{name}': {reason}."
        | TypeError.Overflow error ->
            let axis =
                match error.Axis with
                | Horizontal -> "horizontal"
                | Vertical -> "vertical"

            let contributions =
                error.Contributions
                |> List.map (fun (name, size) -> $"  {name}: {Px.format size}")
                |> String.concat "\n"

            let gapLine =
                if error.GapTotal = Px.zero then
                    ""
                else
                    $"\n  gaps: {Px.format error.GapTotal}"

            $"Layout overflow in '{error.ElementName}' on the {axis} axis.\n{contributions}{gapLine}\n  required: {Px.format error.Required}\n  available: {Px.format error.Available}"
