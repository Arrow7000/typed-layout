# Tranche 2 Plan

**Status:** partially landed; remaining work folded into the next tranche

## What just landed

The current Lean core now has:

- reusable extent-stacking functions
- a `CheckedWithin` result type carrying fit evidence at the checker boundary
- a box-oriented geometry tree
- a reusable adjacent-separation predicate for evaluated children
- `Box` containment lemmas (`fitsWithin_refl`, `fitsWithin_trans`, etc.)
- generic wrapper-containment proofs for padding and frame
- a richer executable example corpus, including a nested frame/padding/row example
- small boolean projections (`CheckResult.isExact`, `CheckResult.hasError`)
- example theorems for exact rows, exact columns, and incompatible layouts

## What this tranche should do next

The remaining useful work after the partial landing still focuses on
**containment and evidence shaping**.

More specifically:

1. prove **generic stacked-layout containment** for rows/columns, not just wrapper containment
2. tighten the relationship between `CheckedWithin` and future conditional/runtime
   guarantee classes
3. continue cleaning up the exact examples into a more canonical test corpus

## Why containment next

The current core can already say meaningful things about:

- total extents
- placement order
- adjacent non-overlap along the stacking axis
- wrapper containment

The still-open next semantic property is:

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

If generic row/column containment proofs reveal that the current unindexed
`CheckedLayout` is too loose to support the semantics cleanly, that is the point
to revisit whether the checked representation should become more strongly typed.
