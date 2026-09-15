# F# POC 1 Plan

**Date:** 2026-09-15  
**Status:** completed

## Question

Can a small F# semantic core infer useful, hover-ready CSS layout summaries and
reject one genuine layout conflict while preserving the distinctions between
declared CSS, initial values, and used geometry?

## Scope

- an explicit target environment containing one exact viewport
- element-local declarations only
- CSS initial values represented separately from declarations
- a deliberately tiny normal-flow block/flex subset
- exact pixel widths and heights
- named nodes and a per-node inferred layout summary
- strict overflow diagnostics
- deterministic text rendering of summaries suitable for a future LSP

## Architectural constraints

- CSS is the semantic model
- no hidden semantic declarations during lowering or checking
- inference accepts an environment even though the first environment is simple
- source AST, specified/computed style, and inferred geometry remain distinct
- unsupported CSS situations produce explicit diagnostics rather than guesses

## Not in POC 1

- standalone surface parser
- CSS emission
- selectors or cascade specificity
- inheritance
- viewport ranges
- media queries
- text and intrinsic inline formatting
- general flex grow/shrink resolution
- LSP transport

The POC is an executable semantic spike beneath the future standalone language,
not a proposal that users should write an F# embedded DSL.

## Demonstrations

1. A fixed-width flex container with two fixed children infers their exact used
   geometry and a hover-ready type for every name.
2. A block-level flex container with `width: auto` derives its width from the
   containing block, rather than silently becoming content-sized.
3. A non-shrinking flex row whose children require more main-axis space than the
   container receives is rejected with an arithmetic explanation.

## Exit condition

The project builds from a clean checkout and an executable test/demo exercises
all three demonstrations. The result should be small enough to replace freely
after it teaches us what the standalone syntax and richer constraint domain
need.
