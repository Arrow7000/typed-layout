# Checked Representation Frontier

**Status:** active design note

This note records a design pressure that has started to become visible in the
Lean implementation.

## 1. The current checked representation

Right now the core uses:

- `CheckedLayout` as a clean checked AST
- `CheckedWithin available` as the checker boundary that carries fit evidence

This is a good first landing spot because it keeps the implementation small and
the recursion pleasant.

## 2. What is working well

The current representation already supports:

- exact extent synthesis
- total evaluation
- local wrapper-containment proofs for padding/frame
- generic row/column adjacency proofs
- a clean executable example corpus

So this representation is not wrong. It has been productive.

## 3. Where pressure is appearing

The pressure point is generic stacked-layout containment.

In rows and columns, the facts that matter include:

- the child extents list
- the gap
- the prefix cursor at each child position
- the relation between the full stacked extent and the tail stacked extent

Those facts are *computable* from the current representation, but not strongly
reflected in the type of the checked node itself.

That makes some proofs feel more operational than structural.

## 4. The design question

When a proof gets awkward, there are at least two very different responses:

1. keep the representation and push harder with helper lemmas
2. strengthen the representation so the awkward fact becomes explicit data/evidence

For this project, option 2 should always be taken seriously before reaching for
ad-hoc proof gymnastics.

## 5. Plausible next representation upgrades

### Option A — Keep `CheckedLayout`, add stack certificates

Introduce a proof-oriented helper structure specifically for stack layouts, e.g.
a certificate that carries:

- child extents
- gap
- computed stacked extent
- maybe cursor/prefix facts

This is attractive because it localizes the extra type machinery to the exact
proof frontier.

### Option B — Index stack nodes more strongly

Make row/column nodes carry richer typed child representations directly.

This could improve proof structure, but it also raises the complexity of the core
representation more sharply.

### Option C — Index `CheckedLayout` by extent again, but more selectively

This revisits an earlier direction, but with more restraint.

The lesson from the first attempt is not that indexing is bad; it is that the
first version was too eager and made the checker/proof boundary awkward.

## 6. Current recommendation

The next good experiment is probably **Option A**:

> keep the current `CheckedLayout` shape, but introduce a proof-oriented internal
> stack certificate/helper type for rows/columns.

That seems like the lowest-risk way to test whether stronger typing genuinely
improves the proof story without prematurely rewriting the whole checked core.

## 7. Why this note matters

This project is explicitly trying to use Lean's type system as a design tool,
not just as a language to write untyped ideas in.

So when proof difficulty starts to point at a missing domain type, that signal
should be recorded and treated as real design feedback.
