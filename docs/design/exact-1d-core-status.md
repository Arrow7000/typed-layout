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
- `TypedLayout/Core/Certified.lean`
- `TypedLayout/Core/Summary.lean`
- `TypedLayout/Core/Contract.lean`
- `TypedLayout/Core/Examples.lean`
- `TypedLayout/Backend/ExactCss.lean`
- `TypedLayout/Backend/ExactCssRender.lean`
- `TypedLayout/Backend/ExactCssFixtures.lean`
- `TypedLayout/Backend/ExactCssManifest.lean`
- `TypedLayout/Backend/ExactCssExamples.lean`

## Current implemented fragment

The implemented exact fragment currently includes:

- exact extents over `Nat`
- a first `Nat`-based bounded-size domain layer (`AxisBounds`, `ExtentBounds`) for
  exact-or-bounded range views
- recursive exact stacking combinators (`stackedMain`, `stackedCross`, `stack`)
- manual `DecidableEq` support for geometry trees
- origins and insets
- leaves
- rows
- columns
- padding
- frames
- total extent synthesis for checked layouts
- a checker returning `CheckedWithin available`
- an opt-in `CertifiedWithin available` success certificate bundling fit evidence,
  propositional local soundness, and executable local witness truth
- a `CertifiedLocalLayout` wrapper for locally-sound checked layouts, with
  recursive certified-child recovery for nested exact layouts
- a first public exact-fragment summary layer exposing exact guarantee class,
  exact extents, singleton bounded views, and typed local-invariant inventories
  for checked layouts
- a first explicit exact-fragment contract layer exposing bounded input/output
  views, exact outputs, guarantee class, and local invariants synthesized from
  `CertifiedWithin available`
- a typed exact-fragment CSS backend IR with exact pixel lengths, border-box
  sizing, restricted flex/block display choices, and exact row/column/padding/
  frame lowering from checked/certified layouts
- direct `checkWithinArtifact` / `checkArtifact` helpers for lowering successful
  exact checks straight to backend artifacts
- direct `checkWithinRenderedDocument` / `checkRenderedDocument`,
  `checkWithinRenderHtml` / `checkRenderHtml`, and `checkWithinRenderCss` /
  `checkRenderCss` helpers that keep successful exact checks routed through the
  typed artifact/document pipeline all the way to final rendered output
- a tiny typed exact-fragment HTML/CSS document IR with generated-class
  stylesheet rules and `body`/`div` element trees lowered from backend nodes and
  artifacts without raw string emission
- typed exact-document helpers that collect body-tree class references,
  stylesheet rule class names, and single-root body structure without dropping to
  raw rendered strings
- a total exact-fragment rendering layer that projects the typed backend/document
  IR to concrete HTML/CSS text at the final output boundary
- a small standalone exact-page output layer that assembles rendered document
  HTML/CSS into a complete HTML page string, with direct
  `checkWithinRenderedPage` / `checkRenderedPage` and
  `checkWithinRenderPage` / `checkRenderPage` helpers still routed through the
  typed artifact/document pipeline
- a typed exact-fixture corpus with constructor-backed fixture identifiers and
  canonical exact row / padded leaf / framed leaf / nested-frame-row fixtures
  that package an end-to-end exact projection wrapper (checked/certified/
  contract/artifact/document/rendered outputs) for future backend-fidelity work
- a small typed export/manifest layer that projects canonical exact fixture ids to
  stable output-boundary slugs/file names and packages rendered-document /
  rendered-page outputs into manifest entries without adding IO or an external
  harness
- a pure typed file-plan layer that expands each manifest entry to intended
  document / stylesheet / standalone-page files and contents for future export
  harnessing, still without performing any writes
- a total evaluator producing geometry trees

## Current proved/exampled facts

The current Lean development already contains proofs/examples for:

- exact row extent computation
- exact column extent computation
- exact row child x-origins
- exact column child y-origins
- nested frame/padding/row geometry examples
- full concrete geometry equality for nested exact layouts
- generic row adjacency/separation
- generic column adjacency/separation
- generic row child containment
- generic column child containment
- executable boolean checks for adjacency/separation
- executable per-layout local witness checks (`CheckedLayout.localWitness?`)
- soundness/completeness bridges for the main local executable booleans
- soundness bridges from executable local witnesses back to propositional local facts
- checker-to-witness bridges showing successful exact checks produce locally-sound checked layouts and `localWitness? = true`
- locally certified child access for nested checked row/column/padding/frame
  layouts
- public exact-fragment summaries synthesized from `CheckedLayout` and
  `CertifiedWithin`
- exact-fragment contracts synthesized from `CertifiedWithin`, with examples
  showing exact guarantee, bounded input/output views, and backed local
  invariants
- artifact-bridge theorems showing successful exact artifact lowering recovers
  the blessed target profile, exact source guarantee, output-bounds-within-input
  bounds, and checked/certified root correspondence facts
- rendered-output bridge theorems showing successful exact rendered-document /
  HTML / CSS / standalone-page helpers still recover the backend artifact/
  document provenance they came from
- an `ExactProjection` wrapper that bundles successful exact checks into a single
  typed end-to-end view spanning checked/certified data, contracts, backend
  artifacts, typed documents, and rendered outputs
- exact-document structural theorems showing generated stylesheet class names are
  nodup, body-tree class references are covered by stylesheet rules, and exact
  lowering keeps the document rooted at an unstyled single-child body
- a canonical typed backend fixture layer that keeps a small exact-example corpus
  available through typed identifiers instead of loose ad-hoc example selection
- a typed manifest/export layer showing the canonical exact fixtures can be
  collected with stable slugs/file names while preserving rendered-page
  provenance back to the exact fixture corpus
- a typed file-plan layer showing each manifest entry expands to the expected
  three intended output files, with filename/content correspondence staying at
  the export boundary
- exact-to-bounded embeddings for `ExactExtent`, plus basic containment and
  compatibility lemmas over 1D/2D bounded ranges
- bridges showing the exposed summary invariants are backed by `LocalSound`
- generic padding child containment
- generic framed-leaf child containment when a fit proof is supplied
- incompatible layouts surfacing the expected checker error shape

The checker/result layer also now exposes small boolean projections that are handy
for executable examples:

- `CheckResult.isExact`
- `CheckResult.hasError`

## Current semantic stance of the code

Important boundaries of the current implementation:

1. **This is still the exact box core.**
   No text, no intrinsic sizing, no flex, no grid, no wrapping.

2. **`CheckedWithin` remains the checker boundary, with opt-in certified
   success layers.**
   `check` still returns `CheckedWithin available`, while
   `CertifiedWithin available` gives consumers a small proof-carrying wrapper for
   successful exact checks without globally changing the checker result shape,
   and `CertifiedLocalLayout` lets that local certification story continue down
   through nested checked children.

3. **The geometry tree is box-oriented.**
   Origin and extent travel together as a `Box` rather than as loosely related
   fields.

4. **The local proof story now has a real executable/propositional bridge.**
     Rows/columns have generic separation and immediate-containment theorems,
     padding/frame have generic containment theorems, and executable local witness
     checks now come with soundness/completeness links plus a bridge from
     successful exact checks to `LocalSound` and `localWitness? = true`.

5. **The exact fragment now also exposes a modest bounded-view bridge.**
   Exact extents can be re-viewed as singleton bounds, available space can be
   re-viewed as upper bounds, and summaries/certificates can expose that bounded
   layer without changing the exact checker semantics.

## What is still missing before CSS work

Before any serious CSS lowering, the next desirable semantic work is still:

- decide whether plain contracts should eventually carry enough structural data
  to support standalone backend lowering, rather than relying on
  `CheckedLayout`/`CertifiedWithin` for exact lowering
- a cleaner checked/proof boundary if the guarantee story keeps growing
- clearer alignment between exact guarantees and future `conditional(profile)`
  guarantees
- a fidelity story connecting the typed backend IR, typed document IR, and final
  HTML/CSS text projection to CSS under the blessed profile

## What is still missing before text work

- any intrinsic leaf story
- any measurement profile story in Lean
- any conditional/profile-indexed result type

So the current core is real, but still intentionally pre-text.
