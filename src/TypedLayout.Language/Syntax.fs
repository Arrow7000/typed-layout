namespace TypedLayout.Language

open TypedLayout

type SourceSpan =
    { Start: int
      End: int }

type SyntaxChild =
    | Reference of name: string * span: SourceSpan
    | InlineElement of SyntaxElement

and SyntaxElement =
    { TagName: string
      Declarations: Declaration list
      Children: SyntaxChild list
      Span: SourceSpan }

type Binding =
    { Name: string
      NameSpan: SourceSpan
      Element: SyntaxElement }

type Program =
    { Viewport: Viewport
      Bindings: Binding list }

type SourceDiagnostic =
    { Message: string
      Span: SourceSpan option }

type SourceLocation =
    { Line: int
      Column: int }

[<RequireQualifiedAccess>]
module SourceText =
    let locationAt (source: string) offset =
        let boundedOffset = System.Math.Clamp(offset, 0, source.Length)
        let mutable line = 1
        let mutable column = 1

        for index in 0 .. boundedOffset - 1 do
            if source[index] = '\n' then
                line <- line + 1
                column <- 1
            else
                column <- column + 1

        { Line = line; Column = column }

    let formatDiagnostic source diagnostic =
        match diagnostic.Span with
        | None -> diagnostic.Message
        | Some span ->
            let location = locationAt source span.Start
            $"{location.Line}:{location.Column}: {diagnostic.Message}"
