# Text Strategy and Pretext Notes

Text is likely the hardest problem in the whole project.

This note records a first pass on how text might fit, and whether
[`chenglou/pretext`](https://github.com/chenglou/pretext) looks relevant.

## 1. Why text is hard

Text is awkward because its size is often not a simple input.

It depends on things like:

- content
- font family / weight / style / size
- line height
- available width
- whitespace / breaking rules
- locale / script behavior
- browser/font-engine details

Unlike a fixed-size box, text often has **width-dependent height** and
line-breaking behavior. That makes it the main source of non-locality in layout.

## 2. What Pretext seems to provide

From its README, Pretext appears to provide:

- multiline text measurement and layout in JS/TS
- a precomputation step (`prepare`) for text/font/options
- a cheap layout step (`layout`) for width + line-height
- richer line/width/cursor APIs for manual line routing
- support for some CSS-like text behavior (`white-space`, `word-break`, etc.)
- a clear statement that it is **not** a full CSS inline formatting engine

So the right mental model is:

> Pretext looks like a strong **text measurement oracle for a constrained
> fragment**, not a complete model of browser text semantics.

## 3. Where Pretext could help

Pretext looks genuinely relevant in at least three later-phase scenarios.

### A. Compile-time-known text

If all of these are fixed ahead of time:

- text content
- font/style shorthand
- whitespace/break rules
- width (or a closed set of widths)
- target measurement environment

then a tool like Pretext could precompute:

- natural width
- wrapped line count
- height at given widths
- the widest wrapped line
- even explicit line ranges for some cases

That means compile-time-known text could plausibly feed typed layout contracts.

### B. Build-time verification

Even when exact type-level propagation is too heavy, Pretext could still help as
a build-time checker.

Examples:

- verify that a fixed-width button label never wraps
- verify that a card title fits within a declared height budget
- verify that known marketing copy fits a layout at supported breakpoints

This is valuable even if the main type system remains box-oriented.

### C. Bounded-text experiments

Pretext may also help explore bounded or partially static text stories, where
exact content is unknown but some properties are known.

Examples:

- finite set of allowed labels
- known maximum character/grapheme count
- restricted locales/scripts
- a known set of breakpoints and fonts

In those cases the system may be able to compute conservative bounds rather than
exact metrics.

## 4. Where Pretext does not solve the project

It is important not to over-ascribe magic here.

Pretext does **not** appear to solve:

- full CSS inline formatting semantics
- full browser text behavior
- general rich text / nested markup layout
- cross-browser guarantee problems in the large
- arbitrary runtime text
- the wider box/flex/grid layout problem

It also keeps `lineHeight` as a layout-time input, which is a reminder that even
its model is not "purely derive everything from content once and for all".

## 5. A likely contract model for text

The most promising move is probably not to put raw strings directly in types.
That would be theoretically cute, but ergonomically and operationally awkward.

Instead, the better direction may be to model **knowledge classes** of text.

### Tier 1 — Exact static text

Text is known at compile/build time.

Possible contract shape:

```text
ExactTextMetrics =
  { naturalWidth
  , lineStatsAt : WidthProfile -> LineStats
  , assumptions : TextAssumptions
  }
```

Where `TextAssumptions` might include:

- exact font shorthand
- exact line-height model
- exact break/whitespace options
- exact measurement engine/profile

### Tier 2 — Bounded text

Content is not fully known, but some bounds are known.

Possible contract shape:

```text
BoundedTextContract =
  { maxNaturalWidth?
  , maxLinesAt : WidthProfile -> Nat?
  , maxHeightAt : WidthProfile -> Nat?
  , assumptions : TextAssumptions
  }
```

This seems more realistic for things like labels and CMS content with known
constraints.

### Tier 3 — Dynamic text

Content is runtime-only or too unconstrained for static bounds.

Then the honest story is not "pretend we know the size" but rather:

- this node is runtime-contingent
- the container must tolerate wrapping/overflow/truncation/scroll/growth
- compile-time guarantees stop at structural resilience, not exact fit

## 6. Exact-text guarantees are still conditional

Even for compile-time-known text, an "exact" guarantee is only exact relative to
matching assumptions.

Those assumptions include at least:

- the same font assets actually loading
- the same font engine or a blessed measurement backend
- the same text options (`white-space`, `word-break`, etc.)
- the same emitted CSS affecting text metrics

So a more honest language here is:

- **exact under profile P**
- **bounded under profile P**
- **runtime-contingent**

That profile idea may become important later.

## 7. Recommendation on Pretext

Current recommendation:

- **do not** make Pretext part of the core MVP foundation
- **do** keep it as the most promising near-term text oracle for later phases
- revisit it once the box/flex core and contract language exist

Best likely placement:

1. core MVP: no hard dependency on Pretext
2. early follow-up: static-text / bounded-text experiment using Pretext
3. later: decide whether it is good enough to be a semi-official measurement
   backend for a supported text fragment

## 8. Practical design implication

The first core should probably act as if text is just one instance of a broader
class:

> leaves with intrinsic sizes that may be exact, bounded, or dynamic.

That keeps the core general, while leaving the door open for Pretext-backed text
contracts later.

## 9. Current bottom line

Pretext looks **useful**, but only in a scoped and conditional way.

It does not remove the hard parts of typed CSS layout. But it may become a very
important piece of the eventual answer for the static-text and bounded-text
frontier.
