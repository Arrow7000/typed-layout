open System
open System.IO
open Microsoft.AspNetCore.Builder
open Microsoft.AspNetCore.Hosting
open Microsoft.AspNetCore.Http
open Microsoft.Extensions.DependencyInjection
open TypedLayout.Language

[<CLIMutable>]
type AnalyzeRequest =
    { source: string }

[<CLIMutable>]
type BindingResponse =
    { name: string
      start: int
      ``end``: int
      hoverText: string }

[<CLIMutable>]
type AnalyzeResponse =
    { ok: bool
      diagnostic: string
      bindings: BindingResponse array }

let usage () =
    eprintfn "Typed Layout POC"
    eprintfn ""
    eprintfn "  typed-layout check <file>"
    eprintfn "  typed-layout type <file> <identifier>"
    eprintfn "  typed-layout serve [port]"
    2

let readAndAnalyze path =
    let source = File.ReadAllText path
    source, Compiler.analyze source

let check path =
    let source, result = readAndAnalyze path

    match result with
    | Error diagnostic ->
        eprintfn "%s" (SourceText.formatDiagnostic source diagnostic)
        1
    | Ok analysis ->
        printfn
            "OK — %d reachable binding(s) checked under viewport %s × %s."
            analysis.Bindings.Length
            (TypedLayout.Px.format analysis.Target.Viewport.Width)
            (TypedLayout.Px.format analysis.Target.Viewport.Height)

        0

let printType path identifier =
    let source, result = readAndAnalyze path

    match result with
    | Error diagnostic ->
        eprintfn "%s" (SourceText.formatDiagnostic source diagnostic)
        1
    | Ok analysis ->
        match Compiler.tryFindBinding identifier analysis with
        | None ->
            eprintfn "No reachable binding named '%s'." identifier
            1
        | Some binding ->
            printfn "%s" binding.HoverText
            0

let responseFor source =
    match Compiler.analyze source with
    | Error diagnostic ->
        { ok = false
          diagnostic = SourceText.formatDiagnostic source diagnostic
          bindings = [||] }
    | Ok analysis ->
        { ok = true
          diagnostic = ""
          bindings =
            analysis.Bindings
            |> List.map (fun binding ->
                { name = binding.Name
                  start = binding.NameSpan.Start
                  ``end`` = binding.NameSpan.End
                  hoverText = binding.HoverText })
            |> List.toArray }

let serve port =
    let options =
        WebApplicationOptions(WebRootPath = Path.Combine(AppContext.BaseDirectory, "wwwroot"))

    let builder = WebApplication.CreateBuilder(options)
    builder.WebHost.UseUrls($"http://127.0.0.1:{port}") |> ignore
    builder.Services.AddRouting() |> ignore

    let app = builder.Build()
    app.UseDefaultFiles() |> ignore
    app.UseStaticFiles() |> ignore

    app.MapPost(
        "/api/analyze",
        Func<AnalyzeRequest, IResult>(fun request -> Results.Json(responseFor request.source))
    )
    |> ignore

    printfn "Typed Layout playground: http://127.0.0.1:%d" port
    app.Run()
    0

[<EntryPoint>]
let main arguments =
    try
        match Array.toList arguments with
        | [ "check"; path ] -> check path
        | [ "type"; path; identifier ] -> printType path identifier
        | [ "serve" ] -> serve 5078
        | [ "serve"; port ] ->
            match Int32.TryParse port with
            | true, value when value > 0 && value <= 65535 -> serve value
            | _ -> usage ()
        | _ -> usage ()
    with
    | :? IOException as error ->
        eprintfn "%s" error.Message
        1
