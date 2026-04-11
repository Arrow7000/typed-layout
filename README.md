# Typed Layout

Working title for a separate project exploring statically typed UI layout composition.

## Thesis

Most typed UI systems make **data flow** composable, but not **layout fit** composable.
This project explores whether components can expose layout contracts strongly enough
that some classes of visual incompatibility become compile-time errors rather than
runtime surprises.

The motivating idea is that a component type should be able to say more than
"this renders HTML" or "this is a widget". It should be able to say things like:

- what size/bounds it requires from its parent
- what size/bounds it can produce
- whether it is fixed-size, intrinsic, fill/flex, or bounded
- what kinds of children it can safely contain
- what layout facts are statically known vs runtime-contingent

## Current status

This repo is currently in a **research/bootstrap** phase.

- no implementation code yet
- no surface syntax yet
- no backend/renderer commitment yet
- no claim of full CSS parity

The immediate goal is to clarify the theory, representation, and decision gates
before any implementation starts.

## Foundation docs

- `docs/vision/WORKING_CHARTER.md`
- `docs/vision/FOUNDING_DECISIONS.md`
- `docs/vision/ENGINEERING_PRINCIPLES.md`
- `docs/research/prior-art-and-theory.md`
- `docs/research/text-strategy-and-pretext.md`
- `docs/design/core-representation-sketch.md`
- `docs/design/mvp-core-css-subset.md`
- `docs/design/guarantee-classes.md`
- `docs/design/canonical-example-layouts.md`
- `docs/design/decision-gates.md`
- `docs/plans/2026-04-11-research-roadmap.md`

## Provisional stance

The current best-looking MVP direction is:

1. a typed HTML/CSS layer with CSS as the backend target
2. a restricted 1D subset first, rather than full CSS
3. indexed/refinement-style types rather than full unrestricted dependent types
4. quantifier-free linear arithmetic for automatic checking
5. a clear distinction between:
   - statically proven layout facts
   - runtime-measured layout facts
   - soft preferences

## Explicit non-goals for the bootstrap phase

- full text layout and line breaking
- full Flexbox/Grid parity
- styling, animation, and interaction
- general-purpose global constraint magic as the public semantic model

## Near-term next steps

1. ratify the typed-CSS MVP subset and its canonical source semantics
2. choose the size domain: exact naturals, intervals, units of measure, etc.
3. define the 1D core IR and its contract/checking judgments
4. decide which guarantees are exact, conditional, or runtime-contingent
5. design the CSS-fidelity test harness
6. postpone text from the core MVP, but keep a concrete plan for static-text and bounded-text follow-up
