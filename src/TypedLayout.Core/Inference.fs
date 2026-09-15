namespace TypedLayout

type Axis =
    | Horizontal
    | Vertical

type OverflowError =
    { ElementName: string
      Axis: Axis
      Available: Px
      Required: Px
      Contributions: (string * Px) list
      GapTotal: Px }

[<RequireQualifiedAccess>]
type TypeError =
    | Unsupported of elementName: string * reason: string
    | Overflow of OverflowError

type ContentRequirements =
    { Width: Px
      Height: Px }

type LayoutGuarantees =
    { ChildrenContained: bool }

type LayoutType =
    { ElementName: string
      TagName: string
      SpecifiedStyle: SpecifiedStyle
      UsedSize: ExactSize
      ContentRequirements: ContentRequirements
      Guarantees: LayoutGuarantees
      Children: LayoutType list }

[<RequireQualifiedAccess>]
module Inference =
    let private sum values =
        values |> List.fold Px.add Px.zero

    let private maximum values =
        values |> List.fold Px.max Px.zero

    let private totalGap style childCount =
        let gapCount = System.Math.Max(0, childCount - 1)
        SpecifiedStyle.usedGap style |> Px.multiply gapCount

    let private overflow name axis available required contributions gapTotal =
        TypeError.Overflow
            { ElementName = name
              Axis = axis
              Available = available
              Required = required
              Contributions = contributions
              GapTotal = gapTotal }

    let rec private inferElement (containing: ContainingBlock) (element: Element) =
        let style = SpecifiedStyle.resolveLocal element.Declarations

        match style.Display.Value with
        | Display.Inline ->
            Error(
                TypeError.Unsupported(
                    element.Name,
                    "inline formatting and intrinsic inline content are outside POC 1; set display:block or display:flex explicitly"
                )
            )
        | display ->
            let usedWidth =
                match style.Width.Value with
                | PreferredSize.Length width -> width
                | PreferredSize.Auto -> containing.Width

            let childContaining: ContainingBlock =
                { Width = usedWidth
                  Height = None }

            let rec inferChildren accumulated remaining =
                match remaining with
                | [] -> Ok(List.rev accumulated)
                | child :: rest ->
                    match inferElement childContaining child with
                    | Error error -> Error error
                    | Ok inferred -> inferChildren (inferred :: accumulated) rest

            match inferChildren [] element.Children with
            | Error error -> Error error
            | Ok children ->
                let childWidths = children |> List.map (fun child -> child.UsedSize.Width)
                let childHeights = children |> List.map (fun child -> child.UsedSize.Height)
                let gapTotal = totalGap style children.Length

                let requiredWidth, contentHeight =
                    match display with
                    | Display.Block -> maximum childWidths, sum childHeights
                    | Display.Flex ->
                        match style.FlexDirection.Value with
                        | FlexDirection.Row -> Px.add (sum childWidths) gapTotal, maximum childHeights
                        | FlexDirection.Column -> maximum childWidths, Px.add (sum childHeights) gapTotal
                    | Display.Inline -> failwith "handled above"

                let horizontalContributions =
                    children |> List.map (fun child -> child.ElementName, child.UsedSize.Width)

                let noFlexChildCanShrink =
                    children
                    |> List.forall (fun child -> child.SpecifiedStyle.FlexShrink.Value = 0M)

                if Px.value requiredWidth > Px.value usedWidth then
                    match display with
                    | Display.Flex when style.FlexDirection.Value = FlexDirection.Row && not noFlexChildCanShrink ->
                        Error(
                            TypeError.Unsupported(
                                element.Name,
                                "negative free space requires the CSS flex-shrink algorithm, which POC 1 does not yet implement"
                            )
                        )
                    | _ ->
                        Error(overflow element.Name Horizontal usedWidth requiredWidth horizontalContributions gapTotal)
                else
                    let usedHeight =
                        match style.Height.Value with
                        | PreferredSize.Length height -> height
                        | PreferredSize.Auto -> contentHeight

                    if Px.value contentHeight > Px.value usedHeight then
                        let contributions =
                            children |> List.map (fun child -> child.ElementName, child.UsedSize.Height)

                        Error(overflow element.Name Vertical usedHeight contentHeight contributions gapTotal)
                    else
                        Ok
                            { ElementName = element.Name
                              TagName = element.TagName
                              SpecifiedStyle = style
                              UsedSize =
                                { Width = usedWidth
                                  Height = usedHeight }
                              ContentRequirements =
                                { Width = requiredWidth
                                  Height = contentHeight }
                              Guarantees = { ChildrenContained = true }
                              Children = children }

    /// Infer a complete tree under one explicit target. The stylesheet argument
    /// is intentionally checked even though POC 1 supports only the empty
    /// environment.
    let infer (target: TargetEnvironment) root =
        match target.Stylesheet with
        | StyleEnvironment.Empty ->
            let rootContaining: ContainingBlock =
                { Width = target.Viewport.Width
                  Height = Some target.Viewport.Height }

            inferElement rootContaining
                root

    let rec tryFind name layoutType =
        if layoutType.ElementName = name then
            Some layoutType
        else
            layoutType.Children |> List.tryPick (tryFind name)
