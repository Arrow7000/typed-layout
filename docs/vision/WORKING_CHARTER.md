# Working Charter

**Status:** bootstrap / research-first / no implementation canon yet

## Objective

Explore a typed HTML/CSS layer in which composition carries meaningful spatial
guarantees, while CSS remains the eventual compilation target.

The central question is:

> Can we design a practical layout language where component composition is
> checked not only structurally, but also geometrically and behaviorally?

Concretely, we want to investigate whether a component can carry a layout
contract rich enough to express facts like:

- fixed or bounded size
- required parent bounds
- intrinsic vs flexible sizing behavior
- slot compatibility for children
- locally checkable fit obligations

## Why this project exists

Typed functional UI systems already give strong guarantees about data and event
composition. But layout remains comparatively weak:

- components can be structurally nestable while still being visually incompatible
- layout errors often emerge only at runtime
- CSS and CSS-like systems are expressive, but their composition model is not
  statically checked in the way typed functional programmers expect

This project exists to investigate a stronger notion of UI composability.

## Current working assumptions

These are **working hypotheses / founding decisions**, not irreversible canon:

1. **The project is a typed HTML/CSS layer, not a totally fresh UI world.**
   CSS is the intended target, not an accidental backend.

2. **The MVP should still not try to model full CSS exactly.**
   Full Flexbox/Grid semantics appear too operational, intrinsic-heavy, and
   context-sensitive to serve as the foundation. The likely path is a typed,
   tractable CSS subset.

3. **A small compositional layout algebra is the right starting point.**
   Rows, columns, padding, alignment, bounded fixed/fill/flex behavior, and a
   carefully chosen flex-inspired 1D fragment look like the right first foothold.

4. **A refinement/indexed-type approach is more plausible than full dependent
   typing.**
   Much of the interesting reasoning seems to live in decidable fragments of
   arithmetic and finite structural facts.

5. **Formal core first is the right sequencing.**
   The initial work should clarify the core representation, contracts, and proof
   story before surface-language ergonomics.

6. **The system must distinguish static facts from runtime-measured facts.**
   Text measurement, intrinsic content sizing, and responsive/environmental data
   are real and should not be smuggled in as fake compile-time certainty.

7. **The first serious foothold should be 1D, not 2D.**
   2D layout matters and should arrive later, but it should not be required to
   validate the core thesis.

8. **Text is essential, but not required in the first POC/MVP.**
   A layout language that cannot eventually talk about text remains toy-like,
   but text should probably be treated as a later frontier rather than a blocker
   on the first core.

9. **The public semantics should probably stay local/compositional.**
   A general global solver may still be useful internally or as a later
   extension, but using it as the foundational public model risks making the
   system hard to reason about.

10. **Source semantics must still be canonical.**
    Even with CSS as the target, the language should define its own precise
    semantics for the supported fragment rather than letting browser quirks and
    unspecified defaults silently define canon.

## What this project is not doing yet

- not choosing a renderer backend
- not choosing a host language
- not committing to Lean or any other proof environment
- not designing the final user syntax
- not tackling styling, animation, accessibility, or interaction yet
- not treating text layout as solved

## Immediate outputs we want

The bootstrap phase should leave behind durable answers to:

1. what kind of layout facts belong in types
2. what constraint language is strong enough but still decidable
3. what the first internal representation should look like
4. where the static/runtime boundary should fall
5. what questions must be decided before implementation begins

## Success criterion for this phase

This phase succeeds if we can produce a credible answer to the following:

> "Here is the smallest useful typed-layout core worth implementing first, here
> is what it can prove, here is what it intentionally cannot prove, and here is
> why that boundary is the right one."
