namespace TypedLayout.Language

open TypedLayout

type InferredBinding =
    { Name: string
      NameSpan: SourceSpan
      Type: LayoutType
      HoverText: string }

type Analysis =
    { Target: TargetEnvironment
      Root: LayoutType
      Bindings: InferredBinding list }

[<RequireQualifiedAccess>]
module Compiler =
    let private diagnostic message span =
        { Message = message
          Span = span }

    let private resolve (program: Program) =
        let duplicate =
            program.Bindings
            |> List.groupBy (fun (binding: Binding) -> binding.Name)
            |> List.tryPick (fun (_, bindings) ->
                match bindings with
                | _ :: duplicate :: _ -> Some duplicate
                | _ -> None)

        match duplicate with
        | Some binding -> Error(diagnostic $"Duplicate binding '{binding.Name}'." (Some binding.NameSpan))
        | None ->
            let bindings: Map<string, Binding> =
                program.Bindings |> List.map (fun binding -> binding.Name, binding) |> Map.ofList

            let rec resolveBinding (stack: string list) name referenceSpan: Result<Element, SourceDiagnostic> =
                if List.contains name stack then
                    let cycle = List.rev (name :: stack) |> String.concat " -> "
                    Error(diagnostic $"Cyclic element bindings are not supported: {cycle}." (Some referenceSpan))
                else
                    match Map.tryFind name bindings with
                    | None -> Error(diagnostic $"Unknown element binding '{name}'." (Some referenceSpan))
                    | Some binding -> resolveElement (name :: stack) binding.Name binding.Element

            and resolveElement stack elementName (syntaxElement: SyntaxElement): Result<Element, SourceDiagnostic> =
                let rec resolveChildren (accumulated: Element list) children =
                    match children with
                    | [] -> Ok(List.rev accumulated)
                    | Reference(name, span) :: rest ->
                        match resolveBinding stack name span with
                        | Error error -> Error error
                        | Ok child -> resolveChildren (child :: accumulated) rest
                    | InlineElement inlineElement :: rest ->
                        let generatedName = $"{inlineElement.TagName}@{inlineElement.Span.Start}"

                        match resolveElement stack generatedName inlineElement with
                        | Error error -> Error error
                        | Ok child -> resolveChildren (child :: accumulated) rest

                match resolveChildren [] syntaxElement.Children with
                | Error error -> Error error
                | Ok children ->
                    Ok(
                        Element.create
                            elementName
                            syntaxElement.TagName
                            syntaxElement.Declarations
                            children
                    )

            match Map.tryFind "main" bindings with
            | None -> Error(diagnostic "Every program must define a 'main' element binding." None)
            | Some main -> resolveElement [ "main" ] main.Name main.Element

    let private flatten (root: LayoutType) =
        let rec loop (accumulated: LayoutType list) (node: LayoutType) =
            let accumulated = node :: accumulated
            (accumulated, node.Children) ||> List.fold loop

        loop [] root |> List.rev

    let analyze source =
        match Parser.parse source with
        | Error error -> Error error
        | Ok program ->
            match resolve program with
            | Error error -> Error error
            | Ok root ->
                let target =
                    { Name = "source"
                      Viewport = program.Viewport
                      Stylesheet = StyleEnvironment.Empty }

                match Inference.infer target root with
                | Error error -> Error(diagnostic (Pretty.typeError error) None)
                | Ok inferredRoot ->
                    let inferredByName =
                        flatten inferredRoot
                        |> List.groupBy (fun (inferred: LayoutType) -> inferred.ElementName)
                        |> List.map (fun (name, inferred) -> name, List.head inferred)
                        |> Map.ofList

                    let inferredBindings =
                        program.Bindings
                        |> List.choose (fun (binding: Binding) ->
                            Map.tryFind binding.Name inferredByName
                            |> Option.map (fun (inferred: LayoutType) ->
                                { Name = binding.Name
                                  NameSpan = binding.NameSpan
                                  Type = inferred
                                  HoverText = Pretty.layoutType inferred }))

                    Ok
                        { Target = target
                          Root = inferredRoot
                          Bindings = inferredBindings }

    let tryFindBinding name (analysis: Analysis) =
        analysis.Bindings |> List.tryFind (fun binding -> binding.Name = name)
