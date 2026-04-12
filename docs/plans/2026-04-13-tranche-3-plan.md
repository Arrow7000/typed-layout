# Tranche 3 Plan

**Status:** proposed next tranche after the current overnight work

## Objective

Close the gap between what the exact core can already compute and what it can
already prove generically.

At the moment, the project has:

- generic adjacency/separation for row/column
- generic wrapper containment for padding/frame
- concrete containment checks for row/column examples

The obvious next theorem frontier is to make row/column containment generic too.

## Main target

Prove a generic theorem of the shape:

> every immediate evaluated child of a checked row/column layout fits within the
> evaluated parent box.

## Why this matters

That theorem would make the local exact-core story much more balanced:

- rows/columns: generic separation + generic containment
- padding/frame: generic containment
- examples: executable witnesses layered on top

## Likely implementation needs

The current best candidates for supporting this proof are:

1. strengthen the exact stack helper lemmas further
2. introduce a proof-oriented helper representation for stacked children
3. if necessary, revisit whether `CheckedLayout` needs a more structured checked
   child representation for stackers

## Deliberate warning

This is a good place to be careful about not hardening the wrong semantics.

If the generic proof becomes awkward because the checked representation is too
loose, that is a signal to improve the representation, not to smuggle the proof
obligations into ad-hoc conditionals.

## Still deferred

- text
- CSS emission
- flex
- wrapping
- grid
