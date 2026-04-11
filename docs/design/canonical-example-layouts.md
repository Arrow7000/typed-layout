# Canonical Example Layouts and Failure Cases

This document collects concrete example scenarios the project should eventually
be able to classify.

The point is not to settle syntax yet. The point is to pin down what kinds of
composition the system should accept, reject, or mark as contingent.

## 1. Fixed row that obviously fits

### Scenario

- parent width = 500
- children widths = 100, 150, 200
- gap = 20 total (two gaps of 10)

### Expected classification

- `Exact`

### Why it matters

This is the basic arithmetic fit story that motivated the whole project.

## 2. Fixed row that obviously does not fit

### Scenario

- parent width = 400
- children widths = 150, 150, 150
- gap = 20 total

### Expected classification

- `Incompatible`

### Why it matters

If the system cannot reject this, the thesis is already weakened.

## 3. Parent width derived from child width

### Scenario

- child width = 800
- parent width = child width + 200

### Expected classification

- `Exact`

### Why it matters

This is the original motivating dependent/refinement-style example.

## 4. Child requires definite width, parent only offers unconstrained width

### Scenario

- child height depends on a definite width
- parent cannot provide a definite width in the current fragment

### Expected classification

- likely `Incompatible` in the exact fragment

### Why it matters

This is the first serious "behavior contract" example, not just numeric fit.

## 5. Restricted flex row with definite container width

### Scenario

- parent width = 600
- one fixed child = 200
- two flex children share the remaining width equally

### Expected classification

- `Exact` if the flex rules are part of the exact source fragment

### Why it matters

This is probably the first non-trivial layout distribution the MVP should handle.

## 6. Static button label with compile-time-known text

### Scenario

- button width = 160
- label text known at build time
- font and break rules fixed
- measurement profile fixed

### Expected classification

- `Conditional(profile)`

### Why it matters

This is the first plausible "text is no longer excluded" example.

## 7. Dynamic CMS title inside a fixed-height card

### Scenario

- card width fixed
- card height fixed
- title text runtime-only and unconstrained

### Expected classification

- either `RuntimeContingent` with truncation/overflow policy,
- or `Incompatible` if no safe policy is provided

### Why it matters

This is probably the first real-world case that prevents the project from being
purely toy-like.

## 8. Known finite set of labels

### Scenario

- a button accepts one of a known finite set of text labels
- all labels are known at build time
- all must fit a fixed width

### Expected classification

- likely `Conditional(profile)` or perhaps `Exact` under a stronger closed-world
  story

### Why it matters

This is an important middle ground between static and fully dynamic text.

## 9. Two-dimensional grid-like dashboard card layout

### Scenario

- explicit rows/columns
- cards assigned to slots
- no text-heavy intrinsic behavior yet

### Expected classification

- later-phase target, not MVP

### Why it matters

It marks the point where 2D becomes necessary for product relevance.

## 10. Example failure classes the system should explain well

The eventual UX should ideally distinguish at least these failure modes:

1. **Arithmetic overflow** — the declared sizes simply do not fit
2. **Definiteness mismatch** — child needs a definite dimension the parent lacks
3. **Unsupported semantic feature** — the construct falls outside the guaranteed fragment
4. **Profile-dependent uncertainty** — would work only under a stronger browser/font profile claim
5. **Runtime-content contingency** — exact fit depends on unknown runtime content

## 11. Why this document exists

The project will be easier to steer if every new core rule or experiment can be
checked against concrete example cases like these, rather than discussed only in
the abstract.
