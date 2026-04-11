# Tranche 2 Plan

**Status:** next implementation tranche after the strengthened exact core

## What just landed

The current Lean core now has:

- reusable extent-stacking functions
- a `CheckedWithin` result type carrying fit evidence at the checker boundary
- a box-oriented geometry tree
- a reusable adjacent-separation predicate for evaluated children
- example theorems for exact rows, exact columns, and incompatible layouts

## What this tranche should do next

The next useful tranche should focus on **containment and evidence shaping**.

More specifically:

1. add reusable `Box` lemmas (`right`, `bottom`, containment algebra)
2. prove immediate-child containment facts for padding and simple stacking
3. tighten the relationship between `CheckedWithin` and future conditional/runtime
   guarantee classes
4. clean up the exact examples into a more canonical test corpus

## Why containment next

The current core can already say meaningful things about:

- total extents
- placement order
- adjacent non-overlap along the stacking axis

The obvious next semantic property is:

> evaluated children stay inside the evaluated parent when the exact fragment says
> they should.

That is the next theorem-shaped foothold.

## What still stays deferred

Still not in scope for tranche 2:

- text / intrinsic sizing
- CSS emission
- flex
- wrapping
- grid

## Stop condition for tranche 2

If containment proofs reveal that the current unindexed `CheckedLayout` is too
loose to support the semantics cleanly, that is the point to revisit whether the
checked representation should become more strongly typed.
