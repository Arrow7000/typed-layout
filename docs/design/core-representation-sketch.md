# Core Representation Sketch

This document sketches a plausible internal foundation for a typed-layout
system. It is explicitly provisional.

## 1. Guiding principle

The first representation should separate three concerns that are often muddled
together in existing layout systems:

1. **shape of the layout tree**
2. **layout behavior**
3. **numeric obligations**

If we separate those cleanly, the type story becomes much more tractable.

## 2. Proposed layers

### Layer A — Structural layout algebra

Start with a small compositional IR such as:

- `Leaf`
- `Row [children]`
- `Column [children]`
- `Overlay [children]`
- `Padding insets child`
- `Align mode child`
- `Frame constraints child`
- `Grid tracks children` (possibly deferred to MVP+1)

This layer says *how layout is composed*, but not yet what numeric facts hold.

### Layer B — Size and bounds domain

A first useful domain might be:

- exact sizes
- lower/upper bounds
- optional preferred size
- unconstrained / infinite along an axis

For example:

- `Bounds = { minW, maxW, minH, maxH }`
- `Size = { w, h }`
- `Preference = none | preferred Size`

This mirrors the fact that many layout decisions are not about one exact size,
but about admissible ranges.

### Layer C — Behavior descriptors

Components seem to need behavioral classification separate from pure numbers.
Examples:

- `Fixed`
- `Bounded`
- `Intrinsic`
- `Fill`
- `Flex weight`
- `Shrink`

This matters because many incompatibilities are not just numeric mismatches;
they are semantic mismatches between sizing strategies.

### Layer D — Constraint language

Numeric facts should probably live in a restricted constraint language over the
domains above.

Candidate fragment:

- naturals or integers
- linear equalities/inequalities
- finite enums / booleans
- controlled use of `min` / `max`
- no variable-by-variable multiplication
- no unrestricted quantification in user-facing obligations

## 3. A candidate contract shape

One promising direction is for every layout node/component to elaborate to a
layout contract of roughly this shape:

```text
Contract =
  { assumptions   : Formula
  , inputBounds   : BoundsShape
  , outputBounds  : BoundsShape
  , behavior      : BehaviorSummary
  , childPolicy   : ChildPolicy
  , dynamicInputs : Set DynamicQuantity
  }
```

Where:

- `assumptions` are facts required for the component to compose safely
- `inputBounds` describe what parent context the node expects
- `outputBounds` describe what the node can guarantee in return
- `behavior` captures intrinsic/fill/flex/etc. behavior
- `childPolicy` constrains acceptable children or slots
- `dynamicInputs` records what must be measured at runtime

This is deliberately contract-oriented rather than DOM-oriented.

## 4. Why intervals may beat exact dimensions

The original motivating idea used examples like "this component has width 800"
and "the parent width is child width plus 200". Those are useful examples, but
an MVP likely should not center exact sizes everywhere.

Intervals/bounds are often a better primitive because they match actual layout
behavior more closely:

- many nodes accept a range, not a single number
- many nodes produce bounded output rather than exact output
- exact equality is often too strong for ergonomic composition

So the likely direction is:

- exact sizes where available
- intervals/bounds as the default contract surface
- exact arithmetic as a special case of bounded arithmetic

## 5. Candidate typing/checking judgments

The core system probably wants two related judgments.

### A. Contract synthesis

Given a node, synthesize the contract it offers:

```text
Γ ⊢ node ⇒ contract
```

### B. Compatibility checking

Given a parent context and a child contract, decide whether composition is safe:

```text
Γ ⊢ parentContext ⊨ childContract
```

Operationally, this likely becomes implication/satisfiability checking in the
chosen arithmetic fragment.

## 6. Static vs runtime boundary

One of the most important design requirements is to avoid fake certainty.

Some quantities should remain explicitly dynamic, for example:

- text intrinsic width/height
- image natural size if not known statically
- viewport/device class information
- localization-dependent content growth

The system should therefore be able to say something like:

- this composition is **statically proven** safe
- this composition is **safe assuming** measured quantity `q` stays within bound `b`
- this composition is **not statically derivable** in the current fragment

That boundary may be just as important as the type indices themselves.

## 7. Recommended MVP core

If we had to choose the smallest serious first core, it would probably be:

- rows and columns
- padding and gaps
- alignment
- fixed / bounded / fill / flex behavior
- leaf nodes with declared intrinsic or fixed bounds
- no text layout model beyond opaque intrinsic leaves
- no wrapping
- no absolute positioning
- maybe no grid in v1

That already seems large enough to test whether the idea is real.

## 8. Likely theorem/story for the first implementation

An early implementation does not need to prove everything. A good first target
could be something like:

> If a layout tree typechecks under the MVP contract system, then every local
> parent/child composition in the normalized layout IR satisfies the declared
> size/bounds obligations of that fragment.

That would already be a meaningful and non-trivial result.
