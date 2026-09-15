# Standalone Language Spike

**Date:** 2026-09-15  
**Status:** completed

## Goal

Exercise the semantic core through standalone source text and make inferred
layout types directly inspectable without committing to an editor extension.

## Implemented

- a small lexer and parser retaining source spans
- Elm-like named bindings, declaration lists, child lists, and references
- an explicit exact viewport declaration
- duplicate, missing, and cyclic binding diagnostics
- compilation from source AST to the existing semantic core
- hover-ready inferred types associated with reachable binding spans
- `check` and `type` CLI commands
- a local web playground and JSON analysis endpoint
- positive and negative source examples

## Interface decision

The compiler remains an ordinary library. The CLI and playground are two thin
clients of the same analysis function.

The web playground is the early interactive interface because it has no editor
installation lifecycle and can evolve with the language. The retained source
spans and compiler response model are also the right ingredients for a future
LSP. A VS Code extension should wait until syntax and analysis responses are
stable enough that editor integration tests the language instead of constraining
its design.

## Deliberate limitations

- only `div`-shaped empty/fixed boxes are useful, although tag names parse
- supported properties are `display`, `width`, `height`, `flex-direction`,
  `gap`, and `flex-shrink`
- only `px`, `auto`, and numeric `flex-shrink` values are accepted
- inline formatting and negative-space flex shrinking are rejected as unsupported
- only bindings reachable from `main` receive contextual inferred types
- repeated uses of one binding are not yet represented as separate contextual
  instantiations
- semantic diagnostics do not yet carry a precise originating source span
- the playground lists hoverable identifiers beside a textarea rather than
  implementing a full syntax-aware code editor

These limitations are explicit so that the spike cannot be mistaken for a
claim of wider CSS support.

## Next design pressure

The next semantic slice should decide whether to deepen normal-flow block sizing
or implement a narrow, faithful flex sizing phase. Before expanding syntax much
further, the compiler should also represent use-site occurrences independently
so the same binding can have different contextual used geometry.
