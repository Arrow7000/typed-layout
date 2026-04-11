# Research Roadmap

**Date:** 2026-04-11
**Status:** proposed roadmap for the new typed-layout project

## Objective

Move from an attractive thesis to a credible implementation frontier.

The project is now specific enough to aim at a typed HTML/CSS layer with CSS as
the target, but still early enough that the main job is to choose the right
semantic and theoretical boundaries before code hardens the wrong assumptions.

## Guiding constraints

- CSS is the backend target
- the source fragment should still have canonical semantics of its own
- the initial focus should be 1D, not 2D
- formal core first, then surface language
- text is strategically essential but should not block the first core
- exact/full CSS parity is explicitly out of scope for the first serious slice

## Phase 0 — Ratify the semantic profile

### Goal

Decide exactly what kind of "typed CSS" this is.

### Deliverables

- `docs/vision/FOUNDING_DECISIONS.md`
- `docs/design/mvp-core-css-subset.md`
- a short statement of the blessed CSS profile for the first fragment

### Main questions

1. what subset is actually in the first core?
2. how close should restricted flex semantics stay to CSS flexbox?
3. what counts as an exact vs conditional guarantee?

### Exit criterion

We can describe the supported fragment in one page without handwaving.

## Phase 1 — Formalize the 1D box core

### Goal

Define the smallest box/layout core that is worth typing and proving against.

### Expected scope

- root box with definite available size
- exact/bounded leaf sizes
- row / column
- padding / gap / frame
- restricted 1D flex behavior
- explicit overflow policy
- no text semantics yet

### Deliverables

- core AST/IR design note
- contract language design note
- checking judgments
- evaluation semantics for the exact fragment

### Verification targets

- local feasibility/composability
- sibling non-overlap for row/column fragment
- bound preservation through wrappers
- determinism/totality of evaluation in the exact fragment

### Exit criterion

The project has a core model that is clearly smaller than CSS but clearly larger
than a toy stack of fixed boxes.

## Phase 2 — Define the guarantee lattice

### Goal

Make the static/runtime boundary explicit before text or CSS quirks muddy it.

### Proposed guarantee classes

- `Exact`
- `Conditional(profile)`
- `RuntimeContingent`

### Deliverables

- guarantee-class note
- contract examples showing the same component under different knowledge levels

### Why this phase matters

Without this, the project risks oscillating between overpromising and giving up.

### Exit criterion

Every supported construct can be described honestly in one of the guarantee
classes.

## Phase 3 — CSS compilation and fidelity harness

### Goal

Prove or at least experimentally demonstrate that the source fragment maps to
real browser behavior honestly.

### Deliverables

- source-to-CSS lowering plan
- test harness plan (likely headless browser based)
- a blessed CSS profile / reset assumptions

### Prototype experiment

Generate representative layout trees, compile them to HTML/CSS, render them in a
headless browser, and compare observed box geometry against source-level
evaluation.

### Verification targets

- layout geometry agreement for the supported fragment
- explicit characterization of where agreement is only conditional

### Exit criterion

The project knows whether CSS is an honest backend for the chosen fragment or
whether the fragment must be narrowed further.

## Phase 4 — Early text frontier

### Goal

Re-enter the problem you already know is waiting: text.

### Scope

Start with compile-time-known and bounded-text cases, not arbitrary dynamic rich
text.

### Deliverables

- text contract note
- static text experiment note
- Pretext integration spike or alternative text oracle comparison

### Suggested experiment order

1. exact static labels/buttons/cards
2. bounded-copy verification at fixed breakpoints
3. dynamic text as runtime-contingent leaves

### Exit criterion

The project has an honest story for at least one non-trivial text case.

## Phase 5 — 2D / grid frontier

### Goal

Extend the typed core beyond 1D once the 1D semantics, guarantees, and CSS story
are stable.

### Scope

Likely first 2D candidates:

- explicit grid tracks
- slot/area admissibility
- bounded spanning rules

### Deliberate non-goals for this phase at first

- exact CSS grid parity
- every track-sizing feature
- text-heavy intrinsic spanning cases

## Recommended order of actual experiments

1. **Write the smallest exact 1D evaluator** for box trees with rows/columns and
   wrappers.
2. **Add contracts/checking** for definite size/bounds and child admissibility.
3. **Introduce a restricted flex fragment** only after the fixed/bounded core is
   stable.
4. **Build the CSS fidelity harness** before expanding the language further.
5. **Only then** do a text oracle spike.
6. **Only after that** attempt 2D.

## Suggested first prototype

The first prototype should not try to be a full language.

It should test one specific thesis:

> A typed 1D CSS-flavored box language can compute and check enough layout facts
> that emitted CSS for the supported fragment matches those facts under a known
> browser/profile.

That prototype is already enough to falsify or validate the direction.

## Stop conditions

Stop and rethink if any of these happen:

1. the first flex fragment is already too close to full CSS complexity
2. CSS fidelity requires so many caveats that the guarantees stop feeling real
3. even the 1D core cannot support useful proofs/checks without excessive proof
   machinery
4. the guarantee lattice becomes too complicated to explain to normal users

## Near-term concrete outputs

The next durable outputs should probably be:

1. a stronger core-contract note
2. a guarantee-lattice note
3. a CSS blessed-profile note
4. a small set of canonical example layouts and failure cases
5. a first prototype plan
