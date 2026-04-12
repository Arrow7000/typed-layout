# Exact 1D Core Status

**Status:** implemented in Lean

This note records what the current Lean core actually covers right now.

## Implemented modules

- `TypedLayout/Core/Geometry.lean`
- `TypedLayout/Core/Domain.lean`
- `TypedLayout/Core/Ast.lean`
- `TypedLayout/Core/Check.lean`
- `TypedLayout/Core/Eval.lean`
- `TypedLayout/Core/Properties.lean`
- `TypedLayout/Core/Examples.lean`

## Current implemented fragment

The implemented exact fragment currently includes:

- exact extents over `Nat`
- recursive exact stacking combinators (`stackedMain`, `stackedCross`, `stack`)
- origins and insets
- leaves
- rows
- columns
- padding
- frames
- total extent synthesis for checked layouts
- a checker returning `CheckedWithin available`
- a total evaluator producing geometry trees

## Current proved/exampled facts

The current Lean development already contains proofs/examples for:

- exact row extent computation
- exact column extent computation
- exact row child x-origins
- exact column child y-origins
- nested frame/padding/row geometry examples
- generic row adjacency/separation
- generic column adjacency/separation
- generic padding child containment
- generic framed-leaf child containment when a fit proof is supplied
- concrete row child containment checks via `immediateChildrenFitWithin?`
- concrete column child containment checks via `immediateChildrenFitWithin?`
- incompatible layouts surfacing the expected checker error shape

The checker/result layer also now exposes small boolean projections that are handy
for executable examples:

- `CheckResult.isExact`
- `CheckResult.hasError`

## Current semantic stance of the code

Important boundaries of the current implementation:

1. **This is still the exact box core.**
   No text, no intrinsic sizing, no flex, no grid, no wrapping.

2. **`CheckedWithin` is the current proof-carrying checker boundary.**
   The core does not yet fully index the checked AST by every semantic fact, but
   it does carry fit evidence at the result boundary.

3. **The geometry tree is box-oriented.**
   Origin and extent travel together as a `Box` rather than as loosely related
   fields.

4. **The local proof story is currently asymmetric.**
   Wrapper containment is proved generically today; stacked-layout containment is
   currently represented by concrete executable examples plus generic separation
   lemmas.

## What is still missing before CSS work

Before any serious CSS lowering, the next desirable semantic work is still:

- generic containment properties for stacking layouts
- clearer alignment between exact guarantees and future `conditional(profile)`
  guarantees
- a crisper backend mapping note for row/column/padding/frame

## What is still missing before text work

- any intrinsic leaf story
- any measurement profile story in Lean
- any conditional/profile-indexed result type

So the current core is real, but still intentionally pre-text.
