# Type System and Environment Model

**Date:** 2026-09-15  
**Status:** initial design basis; details remain experimental

## Core judgement

The intended checking judgement is conceptually:

```text
stylesheet environment ; containing context |- element => layout type
```

The stylesheet environment determines the cascade. The containing context
provides available space and inherited/contextual inputs. The inferred layout
type records CSS values, geometric relations, requirements, and guarantees.

For a complete application:

```text
for every target in application.targets:
    check application under target
```

## Layout type

A layout type is not merely a bag of declarations. It contains several related
views:

```text
LayoutType =
    { specifiedStyle
    , computedStyle
    , intrinsicContributions
    , usedGeometry
    , requirements
    , guarantees
    }
```

The implementation may use a different physical representation, but it must not
erase these semantic distinctions.

Definition-site types may be symbolic. Use-site hovers can additionally display
the type instantiated by the actual containing context.

```text
banner : forall availableWidth.
    Element
        { width = auto
        , used-width = stretchFit(availableWidth)
        }
```

## CSS value pipeline

The eventual pipeline is:

```text
DOM + declarations + stylesheet environment
    -> cascaded styles
    -> specified styles
    -> computed styles
    -> layout/intrinsic-size analysis
    -> used geometry and guarantees
```

The first POC begins after a trivial cascade: element-local declarations win and
otherwise the CSS initial value is used. Nevertheless, the implementation entry
point accepts an environment so contextual styles are not designed out.

## Stylesheet environments

Stylesheets are context-sensitive transformations over a DOM, not simple lexical
record overlays. Later support must account for selector matching, origin,
specificity, order, inheritance, and conditional rules.

Browser UA stylesheets should be represented through the same cascade model as
author stylesheets, with their proper origin. Named browser profiles can then be
checked independently and their common/differing inferred facts shown by the
LSP.

## Viewport environments

A target may be a single environment or a region of environments.

```text
mobile =
    viewport.width  in [320px, 767px]
    viewport.height in [568px, 1024px]
    browser          in {Chrome, Safari}
```

Media queries make inferred types piecewise. A future checker should partition
a target range at relevant query thresholds, infer under each stable cascade,
and prove the required constraints symbolically within each partition.

When checking fails, diagnostics should report a concrete counterexample target
when one can be produced.

## Safety policy

CSS defines rendering behaviour, including behaviours that applications may
regard as layout failures. The application therefore supplies or inherits a
layout-safety policy. Early candidates include:

- reject overflow unless explicitly acknowledged
- reject overlap unless explicitly acknowledged
- require children to remain within a declared containment boundary

Policy does not alter emitted CSS. It states which properties the checker must
establish about that CSS.

## Arithmetic domain

The first checker uses exact non-negative pixel lengths. The intended extension
is a restricted symbolic linear domain supporting:

- intervals
- addition and subtraction
- inequalities and equality
- rational multiplication by environmental dimensions
- min/max and piecewise cases where controlled

This is sufficient for many fixed, percentage, viewport-relative, padding, gap,
and breakpoint calculations without admitting arbitrary theorem proving.

## Text

Text introduces width-dependent height, intrinsic sizing, font/environment
assumptions, and line breaking. It should enter as an explicitly profiled or
bounded source of intrinsic contributions. Arbitrary runtime text cannot promise
exact geometry; it must instead compose with policies that make the desired
containment or visibility property provable.
