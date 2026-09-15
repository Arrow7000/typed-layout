open TypedLayout

let px = Px.create

let target width =
    { Name = "poc"
      Viewport =
        { Width = px width
          Height = px 600 }
      Stylesheet = StyleEnvironment.Empty }

let fixedChild name =
    Element.div
        name
        [ Declaration.Display Display.Block
          Declaration.Width(PreferredSize.Length(px 100))
          Declaration.Height(PreferredSize.Length(px 40))
          Declaration.FlexShrink 0M ]
        []

let flexParent name width =
    Element.div
        name
        [ Declaration.Display Display.Flex
          Declaration.Width width ]
        [ fixedChild "first"
          fixedChild "second" ]

let show title result =
    printfn "%s" title

    match result with
    | Ok layoutType -> printfn "%s\n" (Pretty.layoutType layoutType)
    | Error error -> printfn "%s\n" (Pretty.typeError error)

show
    "Fixed-width flex container"
    (Inference.infer (target 800) (flexParent "fixedParent" (PreferredSize.Length(px 250))))

show
    "Block-level flex container with width:auto"
    (Inference.infer (target 500) (flexParent "autoParent" PreferredSize.Auto))

show
    "Strict overflow diagnostic"
    (Inference.infer (target 800) (flexParent "tooNarrow" (PreferredSize.Length(px 180))))
