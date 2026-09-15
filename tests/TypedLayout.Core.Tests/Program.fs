open TypedLayout

let px = Px.create

let fail message =
    eprintfn "FAIL: %s" message
    System.Environment.ExitCode <- 1

let equal message expected actual =
    if expected <> actual then
        fail $"{message}. Expected {expected}, got {actual}"

let target width =
    { Name = "tests"
      Viewport =
        { Width = px width
          Height = px 600 }
      Stylesheet = StyleEnvironment.Empty }

let child name width =
    Element.div
        name
        [ Declaration.Display Display.Block
          Declaration.Width(PreferredSize.Length(px width))
          Declaration.Height(PreferredSize.Length(px 40))
          Declaration.FlexShrink 0M ]
        []

let flex name width children =
    Element.div
        name
        [ Declaration.Display Display.Flex
          Declaration.Width width ]
        children

let fixedResult =
    Inference.infer
        (target 800)
        (flex "fixedParent" (PreferredSize.Length(px 250)) [ child "left" 100; child "right" 100 ])

match fixedResult with
| Error error -> fail $"fixed flex row should infer: {Pretty.typeError error}"
| Ok inferred ->
    equal "fixed parent used width" (px 250) inferred.UsedSize.Width
    equal "fixed parent used height" (px 40) inferred.UsedSize.Height
    equal "fixed parent child width requirement" (px 200) inferred.ContentRequirements.Width
    equal "fixed parent child count" 2 inferred.Children.Length

let autoResult =
    Inference.infer
        (target 500)
        (flex "autoParent" PreferredSize.Auto [ child "left" 100; child "right" 100 ])

match autoResult with
| Error error -> fail $"auto flex row should infer: {Pretty.typeError error}"
| Ok inferred ->
    equal "auto block-level flex fills its containing block" (px 500) inferred.UsedSize.Width
    equal "auto flex child requirement remains content-derived" (px 200) inferred.ContentRequirements.Width

let overflowResult =
    Inference.infer
        (target 800)
        (flex "tooNarrow" (PreferredSize.Length(px 180)) [ child "left" 100; child "right" 100 ])

match overflowResult with
| Ok _ -> fail "non-shrinking 200px of children should not fit in 180px"
| Error(TypeError.Unsupported(_, reason)) -> fail $"expected overflow, got unsupported: {reason}"
| Error(TypeError.Overflow overflow) ->
    equal "overflow required width" (px 200) overflow.Required
    equal "overflow available width" (px 180) overflow.Available

if System.Environment.ExitCode = 0 then
    printfn "All TypedLayout.Core POC tests passed."
