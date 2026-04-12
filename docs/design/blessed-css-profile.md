# Blessed CSS Profile

**Status:** initial backend profile note
**Current named profile in Lean:** `BlessedCssProfile.exact1D_v1`

This document records what the first CSS-side target profile means.

The point is not to pretend the backend exists already. The point is to name the
assumption boundary early, before CSS details leak into the core by accident.

## 1. Why a blessed profile exists at all

The project targets CSS, but the source semantics should still be canonical.

That means every future backend guarantee needs an explicit profile of the form:

> "source semantics agree with emitted CSS under assumptions P"

The first named profile is deliberately narrow.

## 2. `exact1D_v1`

`exact1D_v1` is the first intended backend profile for the exact 1D core.

It is meant to describe a future backend target where the source fragment and the
emitted CSS agree on simple box geometry.

## 3. What the profile is trying to support

Only the current exact fragment:

- fixed-size leaves
- row / column stacking
- explicit gaps
- padding
- explicit frame extents
- no text semantics in the guarantee story
- no percentages
- no wrapping
- no 2D grid

## 4. Expected backend assumptions

The current working assumptions for `exact1D_v1` are:

1. **Border-box semantics are explicit.**
   The backend should not rely on ambient box-model defaults.

2. **Units are simple and definite.**
   The exact 1D fragment should emit concrete lengths only.

3. **No intrinsic-content dependence is in the guaranteed subset.**
   The first backend profile is box-only, not text-driven.

4. **No unsupported CSS features are mixed in.**
   Emitted output should stay within a disciplined subset rather than leaning on
   unrelated browser behavior.

5. **A reset/profile is part of the contract.**
   Backend fidelity should assume a declared reset/profile, not ambient page
   styles.

## 5. What this profile does *not* mean

It does **not** mean:

- full browser equivalence
- full CSS equivalence
- text guarantees
- intrinsic sizing guarantees
- cross-browser parity without qualification

This profile is intentionally the narrowest honest backend claim.

## 6. Why this matters now

Even before code generation exists, this profile helps steer the core.

If a proposed source-language construct cannot plausibly lower under
`exact1D_v1`, that is a warning sign that it may be too early for the current
tranche.

The repository now also contains a typed exact-fragment backend IR and lowering
for row/column/padding/frame aimed at this profile boundary, plus a tiny typed
HTML/CSS document layer with generated-class stylesheet rules lowered from those
artifacts, a total renderer from that typed document IR to concrete HTML/CSS
text, direct `checkWithinArtifact` / `checkArtifact` helpers, and direct
`checkWithinRenderedDocument` / `checkRenderedDocument`,
`checkWithinRenderHtml` / `checkRenderHtml`, and `checkWithinRenderCss` /
`checkRenderCss` helpers that stay routed through the typed backend/document
layers, plus a small standalone exact-page output type that assembles rendered
body/style text into a complete HTML page string with matching
`checkWithinRenderedPage` / `checkRenderedPage` and
`checkWithinRenderPage` / `checkRenderPage` helpers. The proof bridges recover
exact profile/guarantee/bounds metadata from successful artifact lowering and
recover artifact/document provenance from successful rendered-output helpers.
This is still only an exact-fragment projection layer: it is not yet a
backend-fidelity proof, and it does not by itself upgrade any result to
`Conditional(profile)`.

## 7. Likely next backend questions

The next durable backend questions are probably:

1. what reset assumptions become part of the profile?
2. what exact CSS properties realize row/column/gap/padding/frame?
3. how much browser variation must be part of the profile name?
4. when does `conditional(profile)` become the right guarantee class for a result?

Those should be answered before any serious CSS emission work begins.
