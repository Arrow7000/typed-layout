# Decision Gates

These are the main questions that need explicit answers before implementation
should begin.

## 1. What is the public semantic model?

### Option A — Directional layout

Parent provides bounds, child returns size, parent positions child.

Pros:

- compositional
- easier to explain
- easier to type and verify
- strong prior art from Flutter-style systems

Cons:

- less expressive for relational layouts
- may undershoot some UI use cases that want equations rather than negotiation

### Option B — Global constraint system

Layout is a network of equations/inequalities solved as a whole.

Pros:

- expressive
- closer to Cassowary/Auto Layout
- relational layout is natural

Cons:

- weak locality
- harder error reporting
- harder static story
- risks becoming "a solver with syntax" instead of a compositional language

### Option C — Hybrid

Use a directional core as the public model, with a constrained relational escape
hatch or backend for special cases.

**Current recommendation:** start from A or C, not B.

## 2. What belongs in the type?

Possible answers:

- exact dimensions
- bounds/intervals
- behavior classes (`Fixed`, `Intrinsic`, `Flex`, `Fill`)
- child-slot compatibility
- dynamic-vs-static provenance

**Current recommendation:** center bounds + behavior + obligations, with exact
sizes as a special case.

## 3. What is the size domain?

Options:

- natural numbers in abstract layout units
- integers in pixels
- rationals/reals
- units of measure / mixed units

Tradeoff:

- naturals/integers are much easier for automation
- mixed units and percentages become substantially harder

**Current recommendation:** start with naturals/integers and one canonical unit.

## 4. How should intrinsic sizing be represented?

Options:

- treat intrinsic leaves as opaque but bounded
- include explicit runtime measurement obligations
- try to model text layout directly

**Current recommendation:** opaque intrinsic leaves plus explicit dynamic inputs.

## 5. How close to CSS should the MVP be?

Options:

- define a fresh layout language and maybe compile to CSS later
- try to model a typed subset of Flexbox/Grid directly
- aim for near-parity with web layout

**Current recommendation:** define a fresh core with selective CSS inspiration.

## 6. What logic should checking use?

Options:

- full theorem proving
- SMT-backed refinement checking over a small fragment
- bespoke local checker with no solver

**Current recommendation:** use a small refinement-style fragment with automatic
constraint discharge.

## 7. What should happen when proof does not go through?

Possibilities:

- hard type error
- explicit runtime obligation
- fallback to dynamic layout engine

This decision is product-shaping. It determines whether the language behaves as:

- a proof-first system
- a mixed static/dynamic contract system
- a nicer frontend for an existing runtime engine

**Current recommendation:** expose the static/runtime boundary explicitly rather
than pretending every case is either fully proven or fully dynamic.

## 8. What should the first implementation try to prove?

Candidates:

1. local parent/child fit safety
2. row/column bound preservation
3. grid slot/arity correctness
4. absence of a specific class of overflow/underconstraint bugs

**Current recommendation:** start with local fit safety and row/column bound
preservation.

## 9. What should be deferred deliberately?

Strong candidates for deferral:

- text line breaking
- wrapping layouts
- percentage and viewport-relative sizing
- exact Flexbox parity
- exact Grid track sizing parity
- baseline alignment
- scrolling/infinite extents
- animation and temporal layout changes

## 10. Questions to bring back to the user early

These feel like the first human design choices worth making explicitly:

1. Is the goal primarily a **new layout language**, a **typed HTML/CSS layer**,
   or a **research core that could later target multiple renderers**?
2. Should the system optimize for **predictable compositional semantics** even if
   that means drifting away from web-native behavior?
3. Is the project happy to treat **text/intrinsic measurement as dynamic input**
   for v1, or is deeper static modeling of text a core ambition?
4. Does the MVP need **2D grid** early, or is **1D row/column** enough to test
   the thesis?
5. Is the project trying to be **Elm-like and ergonomic first**, or **formal-core
   first**, with ergonomics layered on later?
