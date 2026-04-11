# Founding Decisions

**Date:** 2026-04-11
**Status:** current project-shaping decisions; revise consciously if needed

This document records the first explicit decisions made after the initial idea
exploration.

## 1. Product shape

The project is aiming at a **typed HTML/CSS layer**.

It is **not** currently aiming to:

- replace HTML/CSS with a fully unrelated layout world
- build a renderer-first system with no web target
- typecheck arbitrary existing CSS directly from day one

CSS is the intended compilation target.

## 2. Scope strategy

The system should start with a **restricted subset** and only expand when the
semantics and guarantees remain tractable.

Current expected order:

1. fixed sizes / bounds
2. block-ish composition
3. flex-inspired 1D layout
4. text/intrinsic follow-up
5. 2D / grid-like follow-up

If the richer CSS frontier becomes too intractable, the subset may remain the
whole supported language for a long time. That is acceptable.

## 3. Sequencing

The project should be **formal-core first**.

That means:

- core representation and semantics first
- contract/type discipline second
- CSS compilation strategy next
- ergonomic surface language after that

## 4. 1D before 2D

The first proof-of-concept and likely first MVP should focus on **1D** layout.

This means things like:

- rows / columns
- padding / gaps
- alignment
- fixed / bounded / fill / flex behavior

2D definitely matters, but should be treated as a later frontier rather than a
day-one requirement.

## 5. Text stance

Text is acknowledged as strategically essential and technically difficult.

Current stance:

- text does **not** need to be in the first POC/MVP
- a language that can never handle text meaningfully remains toy-like
- text should therefore be treated as a planned frontier, not ignored

The likely first honest split is:

- no text guarantees in the initial core
- later support for compile-time-known / statically measured text
- weaker or runtime-contingent guarantees for dynamic text

## 6. Semantics vs CSS target

Using CSS as a target does **not** mean CSS itself should define canon by
default.

Current decision:

- the source language should have a precise semantic model for the supported
  fragment
- emitted CSS should be treated as a backend whose fidelity can be tested and
  characterized
- if a feature cannot be mapped to CSS with stable enough behavior, it should
  stay outside the guaranteed fragment until the story is honest

This is the middle path between:

- inventing a completely unrelated layout language, and
- letting browser behavior silently define the language by inertia

## 7. Current unresolved questions

These remain open even after the founding decisions:

1. how exact the guarantees can be across browser/font differences
2. whether the first flex fragment should mirror CSS flex semantics closely or be
   a stricter typed sub-fragment
3. whether exact sizes or intervals/bounds should be the primary surface concept
4. how text measurement artifacts should be represented when text is known at
   compile time
5. how far runtime contingencies should be made explicit in the type/contracts

## 8. Immediate implication

The near-term work should focus on:

1. defining the smallest typed CSS subset worth formalizing
2. defining its core contracts/checking story
3. defining what CSS fidelity means for that fragment
4. postponing text without pretending it is unimportant
