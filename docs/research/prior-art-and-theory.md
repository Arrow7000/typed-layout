# Prior Art and Theory Notes

This document is not a literature review in the formal academic sense. It is a
working map of the idea space around typed layout.

## 1. Prior-art buckets

### A. Typed UI tree construction

Examples:

- Elm HTML
- PureScript Halogen
- Haskell typed HTML libraries

Contribution:

- structure, attributes, and event wiring become type-safe
- component composition is safer than in untyped DOM construction

Limit:

- these systems usually typecheck *structure*, not *layout fit*
- geometric compatibility still lives in CSS or runtime engine behavior

### B. Typed layout DSLs

Examples:

- `elm-ui`
- SwiftUI / Jetpack Compose style row/column/stack APIs
- layout DSLs that try to replace direct HTML/CSS authoring

Contribution:

- layout becomes a first-class declarative language rather than scattered CSS
- some layout mistakes are prevented by construction
- developer ergonomics are often dramatically better than raw CSS

Limit:

- most do not expose strong static contracts for size/bounds compatibility
- they improve layout authoring, but do not usually make spatial obligations part
  of the type system in a strong way

### C. Directional layout systems

Examples:

- Flutter's box-constraint model

Contribution:

- very clear semantic story: constraints go down, sizes go up, parent sets position
- easier to reason about compositionally than CSS's more web-historical semantics
- attractive as a candidate semantic foundation for a typed layout core

Limit:

- still mostly a runtime negotiation model
- does not by itself yield static proofs of fit or compatibility

### D. Constraint-based layout

Examples:

- Cassowary
- Apple Auto Layout
- Grid Style Sheets and related experiments

Contribution:

- relational layout facts can be expressed naturally as equations/inequalities
- requirements and preferences can be separated
- excellent evidence that linear arithmetic constraints are useful in UI layout

Limit:

- satisfiability/conflict is often discovered at runtime
- a fully global constraint worldview may weaken locality and predictability
- soft constraints/priorities are practically important but hard to reflect
  statically in a clean way

### E. Refinement and indexed/dependent types

Examples / concepts:

- Liquid Types / LiquidHaskell
- indexed families over naturals (`Vect n`, `Fin n`)
- practical dependent typing work such as ATS / DML / Idris-style techniques

Contribution:

- strong evidence that numeric and structural invariants can be checked with low
  manual proof burden when the logic is restricted carefully
- especially relevant for bounds, child counts, grid arities, slot indices, and
  simple size inequalities

Limit:

- full dependent typing is probably too heavy for an ergonomic UI language
- unrestricted theorem-prover-style obligations would likely be too costly for
  everyday layout work

### F. CSS Flexbox and Grid

Contribution:

- the most successful real-world layout algebras we have
- worth studying as targets, inspiration, and a source of counterexamples

Limit:

- exact semantics involve intrinsic sizing, iterative resolution, spanning,
  definiteness, and other context-sensitive behavior that look like a poor fit
  for a small decidable static theory

## 2. Theoretical ingredients that appear relevant

### Refinement-style checking

The user's original instinct looks sound: layout facts such as

- `childWidth <= parentWidth`
- `minW <= prefW <= maxW`
- `width = left + content + right`

fit naturally into refinement-style checking over a small arithmetic logic.

### Indexed structure

Some layout facts are better expressed structurally than numerically, for
example:

- a grid with `n` columns should receive `n` track declarations
- a template with named slots should receive exactly those slots
- a region index should be bounded by the number of regions

This suggests a real role for nat-indexed families, but probably in a targeted
way rather than as a full-spectrum dependent language.

### Decidable arithmetic fragments

The most promising automated fragment is quantifier-free linear arithmetic over
naturals/integers, plus booleans/enums and perhaps a few carefully controlled
derived operations.

That buys a lot:

- fixed sizes
- min/max bounds
- padding/gap accumulation
- some flex-style linear distribution
- basic feasibility checking

It does **not** buy the full web platform.

## 3. Where the hard problems begin

These appear to be the main danger zones:

1. **Intrinsic content measurement** — especially text
2. **Exact Flexbox semantics** — iterative redistribution and implicit mins
3. **Exact Grid track sizing** — spanning items and repeated passes
4. **Percentages / indefinite sizes** — circular dependence on surrounding layout
5. **Wrapping and reflow** — line-breaking creates combinatorial structure
6. **Global soft constraints** — useful in practice, but semantically slippery

This strongly suggests that the first project should model a principled typed
subset, not try to "type CSS" wholesale.

## 4. Recommended MVP theory stack

The current best-looking stack is:

1. a small layout IR
2. lightweight indexed structure where clearly valuable
3. refinement-style contracts over layout records
4. automatic checking via quantifier-free linear arithmetic
5. an explicit split between:
   - statically known layout facts
   - runtime-measured facts
   - soft preferences

## 5. Things worth reading more carefully

Not exhaustive, but likely high-yield:

- Rondon, Kawaguchi, Jhala — **Liquid Types**
- Xi and Pfenning — **Dependent Types in Practical Programming**
- Christoph Haase — **A Survival Guide to Presburger Arithmetic**
- Badros, Borning, Stuckey — **The Cassowary Linear Arithmetic Constraint Solving Algorithm**
- CSS Flexbox spec sections on sizing and distribution
- CSS Grid track sizing algorithm
- `elm-ui` design material
- Flutter's constraint model documentation

## 6. Current synthesis

The opportunity here is probably **not** "invent dependent types for layout" in
the abstract.

The opportunity is narrower and more practical:

> find the smallest layout language where a useful class of composition errors is
> statically rejected, while preserving the ergonomics that make declarative UI
> programming pleasant.

That is the foundation the rest of this project should build on.
