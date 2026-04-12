# Project Map

**Status:** active strategic map
**Last updated:** 2026-04-12

This document keeps the bigger picture in view.

It is not the place for detailed proofs or implementation mechanics. It is the
place to answer:

> what are we building, why does it matter, what comes before what, and what must
> stay true as the project grows?

## 1. North star

`typed-layout` aims to become a **typed HTML/CSS layer** in which layout
composition is meaningfully checkable.

The eventual goal is not merely:

- well-typed data flow
- well-typed component structure

but also:

- typed layout contracts
- statically rejected incompatible compositions
- explicit distinction between exact, conditional, and runtime-contingent facts
- an honest compilation story to CSS

In short:

> make layout composition feel closer to the kind of composition functional
> programmers already expect from data and APIs.

## 2. What the project is trying to prove

At the deepest level, the project is testing a thesis:

> a useful fragment of UI layout can be made statically compositional if the
> source language exposes layout facts as first-class contracts and keeps its
> reasoning inside an honest, tractable semantic fragment.

This is narrower than "type all of CSS", but stronger than "make a nicer layout
DSL".

## 3. What this project is not

The project is explicitly **not** trying to:

- model the entire CSS specification
- build a custom renderer instead of targeting the web
- typecheck arbitrary legacy CSS from day one
- pretend text and intrinsic sizing are easy
- let browser quirks silently define source-language canon

The intended shape is:

- **source semantics are canonical**
- **CSS is the compilation target**
- **the supported fragment grows only when the semantics stay honest**

## 4. Strategic workstreams

The project has four major workstreams.

### A. Formal core

Define the source semantics in Lean.

This includes:

- domain types
- checked representations
- evaluators
- proofs and executable witnesses

### B. Guarantee model

Define what kinds of claims the system can make.

This includes:

- `Exact`
- `Conditional(profile)`
- `RuntimeContingent`
- `Incompatible`

### C. Backend honesty

Define what it means for the source fragment to compile to CSS honestly.

This includes:

- blessed CSS profiles
- reset/box-model assumptions
- backend fidelity expectations

### D. Product surface

Eventually design the developer-facing language/tooling.

This includes:

- ergonomic syntax
- HTML/CSS-facing abstractions
- compilation pipeline
- user-facing errors and guarantees

## 5. Phase order

The intended order of work is:

### Phase 0 — bootstrap and framing

- thesis clarification
- prior-art mapping
- founding decisions
- engineering principles

**Status:** substantially complete

### Phase 1 — exact 1D core

- rows / columns
- padding / frame
- exact extents
- total evaluator
- checked core in Lean

**Status:** active and already meaningfully implemented

### Phase 2 — local soundness

- adjacency / non-overlap facts
- containment facts
- cleaner checked/proof boundary

**Status:** in progress

We already have:

- generic row/column separation
- generic wrapper containment for padding/frame
- executable local witnesses for concrete exact layouts

The main remaining frontier is:

- **generic row/column containment**

### Phase 3 — guarantee lattice and backend profile

- sharpen exact vs conditional vs runtime-contingent
- name the first real CSS backend promises
- define the first backend fidelity boundary

### Phase 4 — restricted flex frontier

- add the first flex-inspired fragment
- decide how close it stays to CSS flexbox
- preserve honesty over completeness

### Phase 5 — text frontier

- compile-time-known text
- bounded text
- runtime-only text
- measurement/profile assumptions

This is likely the hardest phase conceptually.

### Phase 6 — 2D / grid frontier

- explicit 2D layout support
- eventually grid-like composition
- still likely short of full CSS grid parity at first

### Phase 7 — ergonomic surface language

- developer-facing syntax
- compiler/lowering pipeline
- product-level usability work

## 6. Current position

Right now the project has real momentum and a real foothold.

The implemented Lean core already includes:

- exact extents over `Nat`
- rows, columns, padding, frame
- total evaluation to geometry trees
- checked layouts and fit evidence at the checker boundary
- recursive stack semantics
- generic separation lemmas
- generic wrapper-containment lemmas
- executable local witness checks
- concrete nested exact-layout examples

So the project is no longer just an idea or design memo. It now has a formal
spine.

## 7. Immediate roadmap

The near-term roadmap should be:

1. finish the generic local soundness story for the exact 1D core
2. decide whether the checked representation should be strengthened to support
   that proof story cleanly
3. sharpen the guarantee lattice before backend emission work
4. define the first serious blessed CSS profile
5. only then move into restricted flex

That ordering is intentional. It is there to stop the project from hardening the
wrong semantics too early.

## 8. Decision gates

There are several gates the project should not drift past casually.

### Gate A — checked representation pressure

If generic row/column containment remains awkward, we should seriously consider a
stronger checked representation or stack certificate helper type.

### Gate B — backend honesty

Before serious CSS emission work, we need a stable answer to:

- what exactly the blessed profile assumes
- what is source-exact vs backend-conditional

### Gate C — flex scope

Before implementing flex, we need to decide whether the first flex fragment is:

- a strict typed sub-fragment of CSS flexbox, or
- a cleaner source semantics that only lowers where equivalent

### Gate D — text boundary

Before text enters the core guarantee story, we need an explicit account of:

- static text
- bounded text
- dynamic text
- profile-dependent measurement assumptions

## 9. Major risks

### Risk 1 — hardening the wrong semantics

If we rush into CSS/flex/text too early, we may bake the wrong model into the
core.

### Risk 2 — overpromising certainty

The project becomes fake if it blurs exact, conditional, and runtime-contingent
claims.

### Risk 3 — underusing Lean's type system

If the implementation leaves important domain facts implicit, we lose one of the
main reasons to build this in Lean.

### Risk 4 — proof heroics instead of better modeling

If a proof becomes ugly, the right response may be to strengthen the
representation rather than forcing the proof through a bad shape.

## 10. What success looks like

There are three meaningful levels of success.

### Research success

We identify a fragment where typed layout guarantees are genuinely real and not
just aesthetic.

### Systems success

We produce a Lean-backed core plus an honest CSS compilation boundary.

### Product success

We end up with something developers would actually want to use as a typed
HTML/CSS layer.

The project only becomes truly important at the third level, but it must pass
through the first two honestly.

## 11. Current steering rule

The project should continue to prefer:

- precise semantics over premature convenience
- honest subsets over fake completeness
- stronger domain types over loose representations
- explicit decision gates over accidental canon-by-momentum

That is the path most likely to preserve both rigor and eventual usefulness.
