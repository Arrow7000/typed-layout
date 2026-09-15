namespace TypedLayout.Language

open System
open TypedLayout

type private TokenKind =
    | Word of string
    | Length of int
    | Number of decimal
    | Equals
    | LeftBracket
    | RightBracket
    | Comma
    | End

type private Token =
    { Kind: TokenKind
      Span: SourceSpan }

exception private ParseFailure of SourceDiagnostic

[<RequireQualifiedAccess>]
module Parser =
    let private diagnostic message span =
        { Message = message
          Span = Some span }

    let private lex (source: string) =
        let tokens = ResizeArray<Token>()
        let mutable index = 0

        let add kind start finish =
            tokens.Add
                { Kind = kind
                  Span = { Start = start; End = finish } }

        let isWordStart character = Char.IsLetter character || character = '_'
        let isWordPart character = Char.IsLetterOrDigit character || character = '_' || character = '-'

        try
            while index < source.Length do
                let character = source[index]

                if Char.IsWhiteSpace character then
                    index <- index + 1
                elif character = '-' && index + 1 < source.Length && source[index + 1] = '-' then
                    index <- index + 2

                    while index < source.Length && source[index] <> '\n' do
                        index <- index + 1
                else
                    match character with
                    | '=' ->
                        add Equals index (index + 1)
                        index <- index + 1
                    | '[' ->
                        add LeftBracket index (index + 1)
                        index <- index + 1
                    | ']' ->
                        add RightBracket index (index + 1)
                        index <- index + 1
                    | ',' ->
                        add Comma index (index + 1)
                        index <- index + 1
                    | _ when isWordStart character ->
                        let start = index
                        index <- index + 1

                        while index < source.Length && isWordPart source[index] do
                            index <- index + 1

                        add (Word(source.Substring(start, index - start))) start index
                    | _ when Char.IsDigit character ->
                        let start = index

                        while index < source.Length && Char.IsDigit source[index] do
                            index <- index + 1

                        let mutable isDecimal = false

                        if index < source.Length && source[index] = '.' then
                            isDecimal <- true
                            index <- index + 1

                            if index >= source.Length || not (Char.IsDigit source[index]) then
                                raise (ParseFailure(diagnostic "Expected digits after decimal point." { Start = start; End = index }))

                            while index < source.Length && Char.IsDigit source[index] do
                                index <- index + 1

                        let numberText = source.Substring(start, index - start)

                        if not isDecimal && index + 1 < source.Length && source[index] = 'p' && source[index + 1] = 'x' then
                            index <- index + 2
                            add (Length(Int32.Parse numberText)) start index
                        else
                            add (Number(Decimal.Parse(numberText, Globalization.CultureInfo.InvariantCulture))) start index
                    | _ ->
                        raise (ParseFailure(diagnostic $"Unexpected character '{character}'." { Start = index; End = index + 1 }))

            add End source.Length source.Length
            Ok(List.ofSeq tokens)
        with ParseFailure error ->
            Error error

    type private State(tokens: Token list) =
        let tokens = List.toArray tokens
        let mutable position = 0

        member _.Current = tokens[position]
        member _.Peek offset = tokens[Math.Clamp(position + offset, 0, tokens.Length - 1)]

        member _.Advance() =
            let token = tokens[position]
            position <- Math.Min(position + 1, tokens.Length - 1)
            token

    let private fail token message =
        raise (ParseFailure(diagnostic message token.Span))

    let private expectWord (state: State) expected =
        let token = state.Advance()

        match token.Kind with
        | Word actual when actual = expected -> token
        | _ -> fail token $"Expected '{expected}'."

    let private takeWord (state: State) description =
        let token = state.Advance()

        match token.Kind with
        | Word value -> value, token.Span
        | _ -> fail token $"Expected {description}."

    let private expectKind (state: State) expected description =
        let token = state.Advance()

        if token.Kind <> expected then
            fail token $"Expected {description}."

        token

    let private takeLength (state: State) description =
        let token = state.Advance()

        match token.Kind with
        | Length value -> Px.create value
        | _ -> fail token $"Expected {description} as a pixel length, such as 800px."

    let private takePreferredSize (state: State) propertyName =
        let token = state.Advance()

        match token.Kind with
        | Word "auto" -> PreferredSize.Auto
        | Length value -> PreferredSize.Length(Px.create value)
        | _ -> fail token $"Expected 'auto' or a pixel length after '{propertyName}'."

    let private parseDeclaration (state: State) =
        let property, propertySpan = takeWord state "a CSS property"

        match property with
        | "display" ->
            let token = state.Advance()

            match token.Kind with
            | Word "inline" -> Declaration.Display Display.Inline
            | Word "block" -> Declaration.Display Display.Block
            | Word "flex" -> Declaration.Display Display.Flex
            | _ -> fail token "Expected 'inline', 'block', or 'flex' after 'display'."
        | "width" -> Declaration.Width(takePreferredSize state property)
        | "height" -> Declaration.Height(takePreferredSize state property)
        | "flex-direction" ->
            let token = state.Advance()

            match token.Kind with
            | Word "row" -> Declaration.FlexDirection FlexDirection.Row
            | Word "column" -> Declaration.FlexDirection FlexDirection.Column
            | _ -> fail token "Expected 'row' or 'column' after 'flex-direction'."
        | "gap" ->
            let token = state.Advance()

            match token.Kind with
            | Word "normal" -> Declaration.Gap Gap.Normal
            | Length value -> Declaration.Gap(Gap.Length(Px.create value))
            | _ -> fail token "Expected 'normal' or a pixel length after 'gap'."
        | "flex-shrink" ->
            let token = state.Advance()

            match token.Kind with
            | Number value when value >= 0M -> Declaration.FlexShrink value
            | _ -> fail token "Expected a non-negative number after 'flex-shrink'."
        | _ -> fail { Kind = Word property; Span = propertySpan } $"Unsupported CSS property '{property}' in POC 2."

    let private parseList (state: State) parseItem =
        expectKind state LeftBracket "'['" |> ignore
        let items = ResizeArray<_>()

        if state.Current.Kind <> RightBracket then
            items.Add(parseItem ())

            while state.Current.Kind = Comma do
                state.Advance() |> ignore

                if state.Current.Kind <> RightBracket then
                    items.Add(parseItem ())

        expectKind state RightBracket "']'" |> ignore
        List.ofSeq items

    let rec private parseElement (state: State) =
        let tagName, tagSpan = takeWord state "an HTML tag name"
        let declarations = parseList state (fun () -> parseDeclaration state)
        let children = parseList state (fun () -> parseChild state)

        { TagName = tagName
          Declarations = declarations
          Children = children
          Span =
            { Start = tagSpan.Start
              End = state.Peek(-1).Span.End } }

    and private parseChild (state: State) =
        let token = state.Current

        match token.Kind, state.Peek(1).Kind with
        | Word _, LeftBracket -> InlineElement(parseElement state)
        | Word name, _ ->
            state.Advance() |> ignore
            Reference(name, token.Span)
        | _ -> fail token "Expected an element or binding name."

    let private parseTokens tokens =
        let state = State tokens
        expectWord state "viewport" |> ignore
        let viewportWidth = takeLength state "viewport width"
        let viewportHeight = takeLength state "viewport height"
        let bindings = ResizeArray<Binding>()

        while state.Current.Kind <> End do
            let name, nameSpan = takeWord state "a binding name"
            expectKind state Equals "'='" |> ignore
            let element = parseElement state

            bindings.Add
                { Name = name
                  NameSpan = nameSpan
                  Element = element }

        { Viewport =
            { Width = viewportWidth
              Height = viewportHeight }
          Bindings = List.ofSeq bindings }

    let parse source =
        match lex source with
        | Error error -> Error error
        | Ok tokens ->
            try
                Ok(parseTokens tokens)
            with ParseFailure error ->
                Error error
