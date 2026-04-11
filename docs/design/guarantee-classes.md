# Guarantee Classes

One risk in this project is talking as if every layout fact will either be fully
proven or fully dynamic. Reality is messier.

This document sketches a more honest guarantee vocabulary.

## 1. Why this matters

The project wants strong guarantees, but it also targets CSS and eventually wants
to talk about text.

That means some claims will be:

- exact in the source semantics
- exact only under a browser/font/profile assumption
- only bounded rather than exact
- not statically provable at all

If we do not name these cases explicitly, the project will either overpromise or
become too timid to be useful.

## 2. Proposed outcome space

Every layout check should ideally land in one of these buckets.

### A. Incompatible

The composition is rejected.

Examples:

- fixed child widths + gaps exceed a fixed parent width in the exact fragment
- a child requires definite width but the parent cannot provide it
- a construct uses an unsupported feature inside the guaranteed fragment

This is the straightforward type-error case.

### B. Exact

The fact is derivable in the source semantics with no extra environmental profile
beyond the core model itself.

Examples:

- a row of fixed-width children fits in a fixed-width parent
- padding/gap arithmetic closes exactly
- sibling non-overlap in the exact 1D fragment

This is the strongest class.

### C. Conditional(profile)

The fact is derivable only under a named profile or measurement assumption.

Examples:

- compile-time-known text fits **assuming** browser/font profile `P`
- emitted CSS preserves geometry **assuming** the blessed reset/profile `P`

This is still a real guarantee, but it is not unconditional.

### D. RuntimeContingent

The system cannot prove the exact fit/layout fact statically in the current
fragment, but the program can still be well-formed if it declares an appropriate
runtime behavior.

Examples:

- dynamic text inside a container that allows wrapping and growth
- a leaf with runtime-measured intrinsic size
- a component whose content may overflow unless clipped/truncated/scrolled

This should not be confused with failure. It is an honest weaker class.

## 3. Exactness vs boundedness

There is another distinction that cuts across the classes above: whether the
system knows an exact size or only bounds.

For example, a result may be:

- `Exact` with exact geometry
- `Exact` with only safe bounds
- `Conditional(profile)` with exact geometry
- `Conditional(profile)` with only safe bounds

So it may be useful later to treat **guarantee status** and **precision level**
as separate axes.

For now, the important thing is simply not to collapse them carelessly.

## 4. Why runtime-contingent is not a cop-out

For dynamic text especially, a useful contract may say something like:

- exact fit is not guaranteed statically
- wrapping is allowed
- height may grow up to `N`, or the node truncates/clips/scrolls
- surrounding composition remains structurally valid

That is still a typed guarantee. It is just not the same guarantee as exact
fixed-box fit.

## 5. Likely first use in the project

The first MVP likely uses these classes roughly as follows:

- `Exact`: fixed/bounded box trees in the small 1D core
- `Conditional(profile)`: CSS backend fidelity, later static-text measurement
- `RuntimeContingent`: dynamic text/intrinsic leaves, future responsive cases
- `Incompatible`: impossible compositions in the supported fragment

## 6. A practical rule of thumb

If the system relies on:

- browser defaults
- font loading
- text measurement backend choice
- CSS features outside the exact source fragment

then the result is probably not `Exact`. It is at best `Conditional(profile)`.

## 7. Current recommendation

Treat this guarantee vocabulary as part of the core design, not a later UX detail.
It affects:

- type/checking outcomes
- docs
- error messages
- how users learn to trust the system
