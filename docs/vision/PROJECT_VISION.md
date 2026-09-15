# Project Vision

**Date:** 2026-09-15  
**Status:** canonical direction for the F# restart

## Product

Typed Layout will be a small standalone language with an Elm-like feel. Its
initial output is static HTML and CSS.

The language models CSS rather than defining a separate layout system which
happens to compile to CSS. Source declarations, CSS initial values, cascade
contexts, computed values, intrinsic contributions, and used layout geometry
must remain distinguishable.

The central product promise is:

> Layout-relevant information is part of an element's inferred type. It is
> visible during ordinary editor interaction, and definite spatial conflicts
> are reported as type errors.

## Editor experience

Hovering an identifier should show a compact layout type containing:

- non-initial layout declarations
- important computed property values
- inferred intrinsic contributions
- symbolic or exact used dimensions
- requirements imposed on the containing context
- guarantees established by the checker

An expanded view may show initial properties, provenance, intermediate formulas,
and target-specific variants.

The distinction between CSS value stages matters. A property's computed value
may remain `auto` while layout gives the box a concrete used width. The language
must not present a derived used dimension as though the author declared it.

## Strictness

The initial checker is conservative. A required layout guarantee must be
established for every target environment declared by the application. Unknown
does not count as safe.

CSS permits deliberate overflow, clipping, and overlap. Consequently the
language must distinguish CSS validity from application layout policy. An
explicit policy may weaken a guarantee—for example clipping can guarantee box
containment without guaranteeing content visibility—but the weakening must be
visible in the type.

## CSS fidelity

The compiler does not silently emit declarations such as `width: max-content`
to recreate semantics from another layout model. Convenience syntax is allowed
only when it is transparent sugar for a documented set of CSS declarations.

Omitted properties begin from CSS specification initial values. HTML user-agent
stylesheets are not conflated with those initial values; they will later be
represented as explicit stylesheet environments.

## Environments

Layout is checked relative to a target environment. An application will
eventually declare a set of supported targets, possibly including:

- exact viewports or viewport ranges
- browser/UA stylesheet profiles
- media features
- font and text-measurement profiles
- root styling

The application is accepted only when its required guarantees hold throughout
the declared target space.

Viewport points are examples useful for previews and browser tests. A viewport
range is a universal claim over every size in the range, not a request to sample
a few representative points.

## Text

Text is not required for the first exact-box POC, but the design must eventually
represent a spectrum:

1. build-time-known text under a named font/measurement profile
2. bounded or policy-constrained dynamic text
3. unconstrained runtime text, such as CMS content

The type system must distinguish box containment, content visibility, and
typographic fidelity. It must not manufacture static certainty about arbitrary
runtime text.

## Initial non-goals

- complete CSS coverage
- interactive client-side applications
- responsive ranges in the first executable slice
- arbitrary stylesheets and selectors in the first executable slice
- exact browser text shaping
- formal verification of the implementation
