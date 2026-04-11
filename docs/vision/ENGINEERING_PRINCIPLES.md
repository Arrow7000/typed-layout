# Engineering Principles

**Date:** 2026-04-11
**Status:** active implementation principles

This document records standing implementation principles for the typed-layout
project.

## 1. Lean is the implementation language

The project should be implemented in **Lean**.

That is not an incidental tooling choice. It reflects the project's goals:

- rich domain modeling
- explicit semantics
- machine-checked reasoning where feasible
- tight correspondence between design and implementation

## 2. Prefer total definitions

Avoid `partial` definitions unless there is a compelling reason and the reason is
documented.

The default expectation is:

- structurally recursive or otherwise total functions
- explicit handling of all cases
- impossible cases ruled out by types where possible

## 3. Avoid `opaque` unless genuinely necessary

Do not hide core domain behavior behind `opaque` definitions unless there is a
clear justification.

For the core language, semantics, and checking pipeline, we prefer transparent,
inspectable definitions.

## 4. Prefer domain types over stringly representations

If the domain distinguishes concepts, the code should usually distinguish them
too.

Examples of the intended style:

- use domain enums/structures instead of ad-hoc strings
- use dedicated types for axes, overflow policies, guarantee classes, etc.
- use structured values instead of raw tuples when the fields have meaning

## 5. Encode domain facts in types

If a fact matters to correctness, look for a type-level home for it.

Examples:

- if a construct requires a definite width before height can be computed, model
  that explicitly
- if two values are correlated, model the correlation directly rather than with
  parallel optional fields
- if a node can only exist in a restricted shape, reflect that in the data type

The project should lean toward making invalid states impossible rather than
filtering them out later with conditionals.

## 6. Correlated data should stay correlated

Avoid representations where related fields can drift apart accidentally.

For example, if two values are always present together or absent together, prefer
an option over a product rather than two separate options.

The same principle applies more broadly:

- prefer sum types that reflect real state distinctions
- prefer small domain-specific records over loosely related fields
- prefer witness-carrying structures when they help eliminate invalid states

## 7. Be generous with types

Types are cheap. Ambiguity is expensive.

This project should be comfortable introducing many small domain types where they
improve clarity, prevent invalid states, or encode semantic distinctions.

## 8. Do not smuggle semantics into conditionals

If the system relies on a distinction that matters everywhere, it probably wants
a type, not a repeated `if` statement.

Conditionals still have a place, but they should not be the main home of the
domain model.

## 9. Current implementation bias

When choosing between:

- a quicker but looser representation, and
- a slightly heavier but semantically truer representation,

the project should generally prefer the semantically truer representation.

That preference is especially strong in the core AST, contracts, and evaluation
semantics.
