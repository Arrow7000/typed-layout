# Typed Layout

Typed Layout is an experiment in making CSS layout visible to, and checkable by,
a programming language's type system.

The intended product is a small standalone, Elm-like language for producing
static HTML and CSS. An element's inferred type includes its layout-relevant CSS
and the geometric facts derived from it. An editor should therefore be able to
show those facts on hover, while definite layout clashes become type errors.

```text
card : Element
    { display = flex
    , width = 320px
    , used-height = 96px
    , children-contained = true
    }
```

CSS is the source semantic model, not merely an output format. The compiler must
not silently introduce layout behaviour from a separate layout algebra.

## Current direction

The active implementation is being restarted in F#. The first proof of concept
is intentionally narrow:

- one explicit viewport target
- element-local declarations
- CSS initial values for omitted properties
- a very small block/flex fragment
- inferred layout summaries for named elements
- strict rejection of layout facts the supported fragment can show are unsafe

The internal checking API is parameterized by a target environment from the
start. Later versions can quantify over viewport ranges, stylesheet contexts,
browser UA profiles, and other environmental inputs.

Build and run the current semantic POC with:

```sh
dotnet build TypedLayout.slnx
dotnet run --project tests/TypedLayout.Core.Tests
dotnet run --project src/TypedLayout.Poc
```

See:

- `docs/vision/PROJECT_VISION.md`
- `docs/design/TYPE_SYSTEM_AND_ENVIRONMENTS.md`
- `docs/plans/2026-09-15-fsharp-poc.md`

## Repository history

The repository previously contained a formally verified exact-box experiment in
Lean. Its source and original design notes remain in the branch temporarily as
historical research, but they are not the architecture of the restarted
project. Documents that describe Lean as the implementation language or a fresh
non-CSS layout algebra are superseded by the documents above.
