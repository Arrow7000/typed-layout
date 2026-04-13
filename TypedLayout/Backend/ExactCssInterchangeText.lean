import TypedLayout.Backend.ExactCssInterchange

namespace TypedLayout.Backend.ExactCss
namespace Interchange

open TypedLayout.Core
open TypedLayout.Backend.ExactCssFixtures

namespace Text

private def joinWith (separator : String) : List String → String
  | [] => ""
  | [part] => part
  | part :: rest => part ++ separator ++ joinWith separator rest

private def escapeChar : Char → String
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | char => String.ofList [char]

private def escapeChars : List Char → String
  | [] => ""
  | char :: chars => escapeChar char ++ escapeChars chars

/-- Quote a string for the deterministic outer-boundary interchange text format. -/
def string (value : String) : String :=
  "\"" ++ escapeChars value.toList ++ "\""

/-- Render a natural number for the deterministic outer-boundary interchange text format. -/
def nat (value : Nat) : String :=
  toString value

/-- Render a boolean for the deterministic outer-boundary interchange text format. -/
def bool : Bool → String
  | true => "true"
  | false => "false"

/-- Render an ordered array for the deterministic outer-boundary interchange text format. -/
def array (items : List String) : String :=
  "[" ++ joinWith "," items ++ "]"

/-- Render an object for the deterministic outer-boundary interchange text format. -/
def object (fields : List (String × String)) : String :=
  let parts := fields.map (fun field => string field.1 ++ ":" ++ field.2)
  "{" ++ joinWith "," parts ++ "}"

/-- Render a tagged object for the deterministic outer-boundary interchange text format. -/
def tagged (tag : String) (fields : List (String × String) := []) : String :=
  object (("tag", string tag) :: fields)

def renderFixtureId : FixtureId → String
  | .exactRow => string "exactRow"
  | .paddedLeaf => string "paddedLeaf"
  | .framedLeaf => string "framedLeaf"
  | .nestedFrameRow => string "nestedFrameRow"

def renderBlessedCssProfile : BlessedCssProfile → String
  | .exact1D_v1 => string "exact1D_v1"

def renderLayoutKind : LayoutKind → String
  | .leaf => string "leaf"
  | .row => string "row"
  | .column => string "column"
  | .padding => string "padding"
  | .frame => string "frame"

def renderGuaranteeClass : GuaranteeClass → String
  | .exact => tagged "exact"
  | .conditional profile => tagged "conditional" [("profile", renderBlessedCssProfile profile)]
  | .runtimeContingent => tagged "runtimeContingent"
  | .incompatible => tagged "incompatible"

def renderExactExtent (extent : ExactExtent) : String :=
  object
    [ ("width", nat extent.width)
    , ("height", nat extent.height)
    ]

def renderOrigin (origin : Origin) : String :=
  object
    [ ("x", nat origin.x)
    , ("y", nat origin.y)
    ]

def renderBox (box : Box) : String :=
  object
    [ ("origin", renderOrigin box.origin)
    , ("extent", renderExactExtent box.extent)
    ]

def renderLength (length : Length) : String :=
  string (Length.render length)

def renderSize (size : Size) : String :=
  object
    [ ("width", renderLength size.width)
    , ("height", renderLength size.height)
    ]

def renderPadding (padding : Padding) : String :=
  object
    [ ("left", renderLength padding.left)
    , ("top", renderLength padding.top)
    , ("right", renderLength padding.right)
    , ("bottom", renderLength padding.bottom)
    ]

def renderBoxSizing (boxSizing : BoxSizing) : String :=
  string (BoxSizing.render boxSizing)

def renderFlexDirection (direction : FlexDirection) : String :=
  string (FlexDirection.render direction)

def renderFlexWrap (wrap : FlexWrap) : String :=
  string (FlexWrap.render wrap)

def renderJustifyContent (justifyContent : JustifyContent) : String :=
  string (JustifyContent.render justifyContent)

def renderAlignItems (alignItems : AlignItems) : String :=
  string (AlignItems.render alignItems)

def renderFlexContainer (container : FlexContainer) : String :=
  object
    [ ("direction", renderFlexDirection container.direction)
    , ("gap", renderLength container.gap)
    , ("wrap", renderFlexWrap container.wrap)
    , ("justifyContent", renderJustifyContent container.justifyContent)
    , ("alignItems", renderAlignItems container.alignItems)
    ]

def renderFlexItem (item : FlexItem) : String :=
  object
    [ ("grow", nat item.grow)
    , ("shrink", nat item.shrink)
    ]

def renderDisplay : Display → String
  | .block => tagged "block"
  | .flex container => tagged "flex" [("container", renderFlexContainer container)]

def renderStyle (style : Style) : String :=
  object
    [ ("boxSizing", renderBoxSizing style.boxSizing)
    , ("size", renderSize style.size)
    , ("padding", renderPadding style.padding)
    , ("display", renderDisplay style.display)
    , ("flexItem", renderFlexItem style.flexItem)
    ]

def renderClassName (className : ExactDocument.ClassName) : String :=
  object [("serial", nat className.serial)]

def renderSelector : ExactDocument.ProbePlan.Selector → String
  | .generatedClass className =>
      tagged "generatedClass"
        [ ("className", renderClassName className)
        , ("selectorText", string (ExactDocument.ProbePlan.Selector.text (.generatedClass className)))
        ]

def renderObservedBox (box : ExactDocument.ProbeObservation.ObservedBox) : String :=
  object
    [ ("origin", renderOrigin box.origin)
    , ("extent", renderExactExtent box.extent)
    ]

def renderObservedStyle (style : ExactDocument.ProbeObservation.ObservedStyle) : String :=
  renderStyle style.toBackendStyle

end Text

namespace FixtureRef

/-- Render an interchange fixture reference to deterministic outer-boundary text. -/
def render (ref : FixtureRef) : String :=
  Text.object
    [ ("fixtureId", Text.renderFixtureId ref.fixtureId)
    , ("slug", Text.string ref.slug)
    , ("documentHtmlFile", Text.string ref.documentHtmlFile)
    , ("stylesheetCssFile", Text.string ref.stylesheetCssFile)
    , ("standalonePageHtmlFile", Text.string ref.standalonePageHtmlFile)
    ]

end FixtureRef

namespace TargetHandle

/-- Render an interchange target handle to deterministic outer-boundary text. -/
def render (handle : TargetHandle) : String :=
  Text.object
    [ ("className", Text.renderClassName handle.className)
    , ("classToken", Text.string handle.classToken)
    , ("selectorText", Text.string handle.selectorText)
    ]

end TargetHandle

namespace ExpectedTarget

/-- Render an interchange expected target to deterministic outer-boundary text. -/
def render (target : ExpectedTarget) : String :=
  Text.object
    [ ("handle", target.handle.render)
    , ("kind", Text.renderLayoutKind target.kind)
    , ("backendStyle", Text.renderStyle target.backendStyle)
    , ("sourceBox", Text.renderBox target.sourceBox)
    ]

end ExpectedTarget

namespace ExpectationPayload

/-- Render an interchange expectation payload to deterministic outer-boundary text. -/
def render (payload : ExpectationPayload) : String :=
  Text.object
    [ ("targetProfile", Text.renderBlessedCssProfile payload.targetProfile)
    , ("sourceGuarantee", Text.renderGuaranteeClass payload.sourceGuarantee)
    , ("root", payload.root.render)
    , ("targets", Text.array (payload.targets.map ExpectedTarget.render))
    ]

end ExpectationPayload

namespace ProbePlanPayload

/-- Render an interchange probe-plan payload to deterministic outer-boundary text. -/
def render (payload : ProbePlanPayload) : String :=
  Text.object
    [ ("targetProfile", Text.renderBlessedCssProfile payload.targetProfile)
    , ("sourceGuarantee", Text.renderGuaranteeClass payload.sourceGuarantee)
    , ("root", payload.root.render)
    , ("targets", Text.array (payload.targets.map ExpectedTarget.render))
    ]

end ProbePlanPayload

namespace ObservedTarget

/-- Render an interchange observed target to deterministic outer-boundary text. -/
def render (target : ObservedTarget) : String :=
  Text.object
    [ ("handle", target.handle.render)
    , ("box", Text.renderObservedBox target.box)
    , ("style", Text.renderObservedStyle target.style)
    ]

end ObservedTarget

namespace ObservationPayload

/-- Render an interchange observation payload to deterministic outer-boundary text. -/
def render (payload : ObservationPayload) : String :=
  Text.object
    [("targets", Text.array (payload.targets.map ObservedTarget.render))]

end ObservationPayload

namespace FieldComparison

/-- Render an interchange field comparison to deterministic outer-boundary text. -/
def render (renderValue : α → String) : FieldComparison α → String
  | .same => Text.tagged "same"
  | .different expected observed =>
      Text.tagged "different"
        [ ("expected", renderValue expected)
        , ("observed", renderValue observed)
        ]

end FieldComparison

namespace BoxComparison

/-- Render an interchange box comparison to deterministic outer-boundary text. -/
def render (comparison : BoxComparison) : String :=
  Text.object
    [ ("origin", FieldComparison.render Text.renderOrigin comparison.origin)
    , ("extent", FieldComparison.render Text.renderExactExtent comparison.extent)
    ]

end BoxComparison

namespace StyleComparison

/-- Render an interchange style comparison to deterministic outer-boundary text. -/
def render (comparison : StyleComparison) : String :=
  Text.object
    [ ("boxSizing", FieldComparison.render Text.renderBoxSizing comparison.boxSizing)
    , ("size", FieldComparison.render Text.renderSize comparison.size)
    , ("padding", FieldComparison.render Text.renderPadding comparison.padding)
    , ("display", FieldComparison.render Text.renderDisplay comparison.display)
    , ("flexItem", FieldComparison.render Text.renderFlexItem comparison.flexItem)
    ]

end StyleComparison

namespace TargetComparison

/-- Render an interchange target comparison to deterministic outer-boundary text. -/
def render (comparison : TargetComparison) : String :=
  Text.object
    [ ("expected", comparison.expected.render)
    , ("observed", comparison.observed.render)
    , ("selector", FieldComparison.render Text.renderSelector comparison.selector)
    , ("box", comparison.box.render)
    , ("style", comparison.style.render)
    ]

end TargetComparison

namespace TargetResult

/-- Render an interchange target result to deterministic outer-boundary text. -/
def render : TargetResult → String
  | .paired comparison =>
      Text.tagged "paired" [("comparison", comparison.render)]
  | .missingObservation expected =>
      Text.tagged "missingObservation" [("expected", expected.render)]
  | .unexpectedObservation observed =>
      Text.tagged "unexpectedObservation" [("observed", observed.render)]

end TargetResult

namespace ComparisonPayload

/-- Render an interchange comparison payload to deterministic outer-boundary text. -/
def render (payload : ComparisonPayload) : String :=
  Text.object
    [ ("targetProfile", Text.renderBlessedCssProfile payload.targetProfile)
    , ("sourceGuarantee", Text.renderGuaranteeClass payload.sourceGuarantee)
    , ("expectedCount", Text.nat payload.expectedCount)
    , ("observedCount", Text.nat payload.observedCount)
    , ("results", Text.array (payload.results.map TargetResult.render))
    ]

end ComparisonPayload

namespace Bundle

/-- Render an interchange bundle to deterministic outer-boundary text. -/
def render (bundle : Bundle) : String :=
  Text.object
    [ ("fixture", bundle.fixture.render)
    , ("expectations", bundle.expectations.render)
    , ("probePlan", bundle.probePlan.render)
    , ("observation", bundle.observation.render)
    , ("comparison", bundle.comparison.render)
    ]

/-- Render a list of interchange bundles to deterministic outer-boundary text. -/
def renderList (bundles : List Bundle) : String :=
  Text.array (bundles.map render)

/-- Canonical interchange bundle corpus for the current exact fixtures. -/
def canonical : List Bundle :=
  FixtureId.all.map (fun fixtureId => ofFixture (TypedLayout.Backend.ExactCssFixtures.fixture fixtureId))

/-- Deterministic outer-boundary text for the canonical interchange bundle corpus. -/
def renderCanonical : String :=
  renderList canonical

theorem canonical_length : canonical.length = FixtureId.all.length := by
  simp [canonical]

theorem renderCanonical_ne_empty : renderCanonical ≠ "" := by
  native_decide

end Bundle

theorem exactRowBundle_fixture_render :
    exactRowBundle.fixture.render =
      "{\"fixtureId\":\"exactRow\",\"slug\":\"exact-row\",\"documentHtmlFile\":\"exact-row.document.html\",\"stylesheetCssFile\":\"exact-row.styles.css\",\"standalonePageHtmlFile\":\"exact-row.page.html\"}" := by
  native_decide

theorem exactRowComparison_render_ne_shifted :
    exactRowBundle.comparison.render ≠ exactRowShiftedComparisonPayload.render := by
  native_decide

end Interchange
end TypedLayout.Backend.ExactCss
