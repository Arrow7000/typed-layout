# Phase 1 Plan — Exact 1D Core

**Date:** 2026-04-11
**Status:** approved implementation slice

## Objective

Bootstrap the Lean project and land the smallest serious exact 1D core.

This slice should be large enough to test the thesis that typed layout contracts
can rule out some invalid compositions statically, but small enough to avoid
accidentally hardening full CSS or even full flexbox semantics by momentum.

## Approved scope for this tranche

Implement:

- the Lean project scaffold
- fundamental domain types
- an exact 1D layout AST
- rows / columns with explicit gaps
- padding/frame wrappers
- exact-size leaves
- a total evaluator for exact geometry
- a static checker for the first arithmetic fit cases
- first proofs/lemmas around layout structure

## Explicitly deferred from this tranche

Do **not** implement yet:

- text or intrinsic sizing
- CSS emission
- browser-fidelity harness
- percentages or mixed units
- wrapping
- grid / 2D layout
- full or even "close enough" flexbox semantics

Flex is deliberately deferred one notch further.

Reason: the project roadmap already identified a fixed/bounded exact core as the
safer first foothold. Landing that first gives us a stable base before we choose
which restricted flex story is honest enough to keep.

## Modules to create first

- `TypedLayout.lean`
- `TypedLayout/Core/Geometry.lean`
- `TypedLayout/Core/Domain.lean`
- `TypedLayout/Core/Ast.lean`
- `TypedLayout/Core/Check.lean`
- `TypedLayout/Core/Eval.lean`
- `TypedLayout/Core/Examples.lean`

The first tranche does **not** need a large proof file if the key structural
facts can live beside the relevant definitions.

## Domain types to introduce first

The first tranche should prefer small semantically-meaningful domain types over
raw tuples and strings.

Likely starting set:

- axes
- 1D/2D extents
- points/origins
- insets
- gap values
- exact sizes / exact extents
- available space
- node identifiers or paths if needed for geometry trees
- guarantee/check outcomes for the exact fragment

The first exact fragment should likely stay on `Nat` dimensions.

## First AST slice

The first AST should represent only what the evaluator can interpret exactly and
the checker can validate honestly.

Likely node forms:

- exact leaf
- row
- column
- padding
- frame / explicit outer extent

It is acceptable if the first AST is not yet fully indexed by all semantic facts,
as long as the domain model stays clean and the checker returns a validated view
or typed evidence for the exact fragment.

## First checker targets

The first checker should handle only clearly exact cases, for example:

- row children + gaps fit within declared parent width
- column children + gaps fit within declared parent height
- padding does not underflow the available extent
- frame/child exact-size compatibility

It is better to reject or defer uncertain cases than to smuggle in looser
semantics early.

## First evaluator target

The evaluator should be a total function that computes exact geometry for a
validated tree in the exact fragment.

The main target output is a geometry tree with explicit:

- origin
- extent
- child geometries

## First proof / lemma targets

Useful first targets:

1. row children are laid out in increasing order with declared gaps
2. column children are laid out in increasing order with declared gaps
3. evaluated child extents stay within the evaluated parent extent for the exact
   checked fragment
4. evaluator totality / no `partial`

## Verification

- `lake build`
- no `sorry`
- no `partial` unless explicitly justified and recorded
- no `opaque` hiding core evaluator/checker behavior unless explicitly justified

## Escalation conditions

Stop and re-open design if any of these happen:

1. the exact fragment already wants non-trivial runtime contingencies
2. the AST starts accreting pseudo-flex behavior without a clear semantic note
3. the checker wants many ad-hoc boolean flags instead of domain types/evidence
4. the evaluator wants partiality or hidden trusted lemmas just to express the
   basic exact fragment

## Immediate next step after this tranche

If this tranche lands cleanly, the next question is:

> do we add a restricted flex fragment next, or do we first define the guarantee
> lattice and CSS-profile/fidelity boundary more sharply?

My current expectation is: do the guarantee/fidelity sharpening first, then flex.
