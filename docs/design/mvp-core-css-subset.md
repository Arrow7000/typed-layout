# MVP Core and CSS Subset Sketch

This document tries to answer a more specific question than the earlier core
representation sketch:

> If the project is specifically a typed HTML/CSS layer, what is the smallest CSS-
> flavored core worth formalizing first?

## 1. Canonical semantic stance

The source language should be canonical.

That means:

- the typed source fragment gets precise semantics of its own
- emitted CSS is a backend for that fragment
- CSS/browser behavior is tested against the source semantics, not treated as an
  unexamined oracle

This is still compatible with staying **close** to CSS.

The right goal is not "invent a wholly new layout model".
The right goal is:

> define a typed, tractable, CSS-flavored fragment whose semantics are tight
> enough to reason about and faithful enough to emit to CSS honestly.

## 2. Proposed first supported fragment

The first fragment should likely include:

- block/root boxes with definite available width/height
- explicit width/height bounds in pixels or abstract layout units
- padding and gap
- overflow policy as an explicit parameter
- vertical stacking
- horizontal stacking
- a restricted flex-inspired 1D container
- alignment along main/cross axis
- explicit box-sizing assumptions (likely always `border-box` internally)

The first fragment should likely exclude:

- percentages
- auto margins
- wrapping
- absolute/fixed positioning
- floats
- z-index layering semantics beyond simple overlay
- full CSS min-content/max-content/intrinsic keywords
- grid
- text-driven intrinsic layout in the core MVP

## 3. Candidate core nodes

One plausible starting AST:

- `Root bounds child`
- `Leaf contract`
- `Column settings children`
- `Row settings children`
- `Flex1D axis settings children`
- `Padding insets child`
- `Frame bounds child`
- `Align axis mode child`

Where `settings` could include things like:

- gap
- padding
- cross-axis alignment
- overflow policy
- flex distribution mode (in the restricted fragment)

## 4. What should live in contracts/types

The strongest candidates are:

### A. Definiteness / boundedness

Examples:

- requires definite parent width
- requires bounded cross-axis space
- produces definite height
- may only produce bounded width, not exact width

### B. Size behavior per axis

Examples:

- `Fixed n`
- `Bounded lo hi`
- `Fill`
- `Flex weight`
- `Intrinsic` (later, not core MVP)

### C. Child admissibility

Examples:

- this container only accepts children that can resolve under definite width
- this child requires a bounded width before its height is meaningful

### D. Guarantee class

Likely every contract/result should be classed as something like:

- `Exact`
- `Conditional profile`
- `RuntimeContingent`

This matters because CSS targets and later text measurement both depend on
environmental assumptions.

## 5. A likely first judgment split

The system likely wants:

1. **contract synthesis** for source nodes
2. **layout feasibility / compatibility checking**
3. **layout evaluation** for the exact supported fragment
4. **CSS compilation**
5. **backend fidelity testing**

This allows the project to distinguish:

- source-level safety
- source-level computed layout facts
- target-level correctness of compilation

## 6. CSS compilation complications

CSS complicates guarantees in several ways:

- browser defaults and resets matter
- box model choices matter
- fonts and intrinsic content matter
- rounding/used-value behavior matters
- full flexbox has subtleties the source language may want to avoid at first

So the project should likely adopt a **blessed CSS profile** for the supported
fragment.

That might include conventions like:

- explicit reset assumptions
- explicit `box-sizing: border-box`
- explicit width/height policies
- avoiding unsupported CSS features in emitted code
- possibly a declared target browser set for high-fidelity testing

## 7. How close should the first flex fragment be to CSS flexbox?

There are two plausible strategies.

### Option A — A stricter typed sub-fragment of CSS flexbox

Pros:

- easier mapping to CSS
- easier product story
- easier to explain as "typed CSS"

Cons:

- may inherit awkwardness from CSS semantics

### Option B — A source-level simplified flex semantics that only compiles to CSS
when equivalent

Pros:

- cleaner theory
- better guarantees

Cons:

- may feel less like direct typed CSS

Current recommendation:

- start closer to **Option A**, but only for a narrow stable fragment
- do not promise full flexbox semantics

## 8. Where text fits

Text should initially sit outside the exact core as an intrinsic leaf class.

So the MVP source language should be able to say, in effect:

- this leaf has exact known size
- this leaf has bounded size
- this leaf is runtime-contingent

Later, compile-time-known text can become a particular source of exact/bounded
intrinsic contracts.

## 9. First proof / verification targets

The most sensible first targets seem to be:

1. local parent/child feasibility
2. row/column non-overlap in the exact fragment
3. bound preservation through padding/gap/frame composition
4. fidelity checks that emitted CSS matches source semantics for the supported
   fragment under the blessed profile

## 10. Bottom line

The first serious version of this project should probably be:

> a typed, CSS-flavored 1D layout core with definite sizes/bounds and restricted
> flex behavior, explicit contract classes, and a testable compilation story to
> a blessed CSS subset.

That is much smaller than "typed CSS" in the large, but it feels big enough to
be real.
