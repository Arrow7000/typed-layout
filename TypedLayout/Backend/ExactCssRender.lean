import TypedLayout.Backend.ExactCss

namespace TypedLayout.Backend.ExactCss

open TypedLayout.Core

private theorem exact_of_map_eq_exact
    {α β : Type _}
    {result : CheckResult α}
    {f : α → β}
    {output : β}
    (h : CheckResult.map f result = .exact output) :
    ∃ value, result = .exact value ∧ f value = output := by
  cases result with
  | incompatible error =>
      simp [CheckResult.map] at h
  | exact value =>
      refine ⟨value, rfl, ?_⟩
      simpa [CheckResult.map] using h

private def joinWith (separator : String) : List String → String
  | [] => ""
  | [part] => part
  | part :: rest => part ++ separator ++ joinWith separator rest

namespace Length

/-- Render an exact-fragment CSS length to concrete CSS text. -/
def render : Length → String
  | .px value => toString value ++ "px"

end Length

namespace Size

/-- Render exact-fragment width/height declarations. -/
def renderDeclarations (size : Size) : List String :=
  [ "width:" ++ Length.render size.width ++ ";"
  , "height:" ++ Length.render size.height ++ ";"
  ]

end Size

namespace Padding

/-- Render exact-fragment padding declarations. -/
def renderDeclarations (padding : Padding) : List String :=
  [ "padding-left:" ++ Length.render padding.left ++ ";"
  , "padding-top:" ++ Length.render padding.top ++ ";"
  , "padding-right:" ++ Length.render padding.right ++ ";"
  , "padding-bottom:" ++ Length.render padding.bottom ++ ";"
  ]

end Padding

namespace BoxSizing

/-- Render exact-fragment box-sizing values. -/
def render : BoxSizing → String
  | .borderBox => "border-box"

end BoxSizing

namespace FlexDirection

/-- Render exact-fragment flex-direction values. -/
def render : FlexDirection → String
  | .row => "row"
  | .column => "column"

end FlexDirection

namespace FlexWrap

/-- Render exact-fragment flex-wrap values. -/
def render : FlexWrap → String
  | .nowrap => "nowrap"

end FlexWrap

namespace JustifyContent

/-- Render exact-fragment justify-content values. -/
def render : JustifyContent → String
  | .flexStart => "flex-start"

end JustifyContent

namespace AlignItems

/-- Render exact-fragment align-items values. -/
def render : AlignItems → String
  | .flexStart => "flex-start"

end AlignItems

namespace FlexContainer

/-- Render exact-fragment flex-container declarations. -/
def renderDeclarations (container : FlexContainer) : List String :=
  [ "flex-direction:" ++ FlexDirection.render container.direction ++ ";"
  , "gap:" ++ Length.render container.gap ++ ";"
  , "flex-wrap:" ++ FlexWrap.render container.wrap ++ ";"
  , "justify-content:" ++ JustifyContent.render container.justifyContent ++ ";"
  , "align-items:" ++ AlignItems.render container.alignItems ++ ";"
  ]

end FlexContainer

namespace FlexItem

/-- Render exact-fragment fixed-item declarations. -/
def renderDeclarations (item : FlexItem) : List String :=
  [ "flex-grow:" ++ toString item.grow ++ ";"
  , "flex-shrink:" ++ toString item.shrink ++ ";"
  ]

end FlexItem

namespace Display

/-- Render exact-fragment display declarations. -/
def renderDeclarations : Display → List String
  | .block => ["display:block;"]
  | .flex container =>
      "display:flex;" :: FlexContainer.renderDeclarations container

end Display

namespace Style

/-- Render exact-fragment CSS declarations from the typed style IR. -/
def renderDeclarations (style : Style) : List String :=
  [ "box-sizing:" ++ BoxSizing.render style.boxSizing ++ ";" ] ++
    Size.renderDeclarations style.size ++
    Padding.renderDeclarations style.padding ++
    Display.renderDeclarations style.display ++
    FlexItem.renderDeclarations style.flexItem

/-- Render a typed exact-fragment style to concrete CSS declaration text. -/
def render (style : Style) : String :=
  joinWith "" (renderDeclarations style)

end Style

namespace ExactDocument

/-- Final concrete output bundle for the exact-fragment renderer. -/
structure RenderedDocument where
  html : String
  css : String
  deriving DecidableEq, Repr

namespace ClassName

/-- Render generated exact-fragment classes to valid CSS/HTML class tokens. -/
def render (className : ClassName) : String :=
  "tl-" ++ toString className.serial

end ClassName

namespace Tag

/-- Render exact-fragment HTML tags. -/
def render : Tag → String
  | .body => "body"
  | .div => "div"

end Tag

namespace ClassRule

/-- Render a typed exact-fragment rule to concrete CSS text. -/
def render (rule : ClassRule) : String :=
  "." ++ ClassName.render rule.className ++ "{" ++ Style.render rule.style ++ "}"

end ClassRule

namespace Stylesheet

/-- Render an exact-fragment stylesheet to concrete CSS text. -/
def render (stylesheet : Stylesheet) : String :=
  joinWith "\n" (stylesheet.rules.map ClassRule.render)

end Stylesheet

namespace Element

private def renderClassAttribute (classes : List ClassName) : String :=
  match classes with
  | [] => ""
  | _ =>
      " class=\"" ++ joinWith " " (classes.map ClassName.render) ++ "\""

mutual

private def renderElement : Element → String
  | .node tag classes children =>
      let tagText := Tag.render tag
      "<" ++ tagText ++ renderClassAttribute classes ++ ">" ++
        renderElements children ++
        "</" ++ tagText ++ ">"

private def renderElements : List Element → String
  | [] => ""
  | child :: rest => renderElement child ++ renderElements rest

end

/-- Render an exact-fragment HTML element tree to concrete HTML text. -/
def render (element : Element) : String :=
  renderElement element

end Element

namespace Document

/-- Render an exact-fragment typed document IR to concrete HTML/CSS text. -/
def render (document : Document) : RenderedDocument :=
  { html := Element.render document.body
  , css := Stylesheet.render document.stylesheet
  }

end Document

end ExactDocument

namespace Node

/-- Render a backend node via the typed exact document IR. -/
def renderedDocument (node : Node) : ExactDocument.RenderedDocument :=
  node.document.render

/-- Render a backend node to concrete HTML text via the typed document IR. -/
def renderHtml (node : Node) : String :=
  node.renderedDocument.html

/-- Render a backend node to concrete CSS text via the typed document IR. -/
def renderCss (node : Node) : String :=
  node.renderedDocument.css

theorem renderedDocument_eq_document_render (node : Node) :
    node.renderedDocument = node.document.render :=
  rfl

end Node

namespace Artifact

/-- Render a backend artifact via the typed exact document IR. -/
def renderedDocument (artifact : Artifact) : ExactDocument.RenderedDocument :=
  artifact.document.render

/-- Render a backend artifact to concrete HTML text via the typed document IR. -/
def renderHtml (artifact : Artifact) : String :=
  artifact.renderedDocument.html

/-- Render a backend artifact to concrete CSS text via the typed document IR. -/
def renderCss (artifact : Artifact) : String :=
  artifact.renderedDocument.css

theorem renderedDocument_eq_document_render (artifact : Artifact) :
    artifact.renderedDocument = artifact.document.render :=
  rfl

end Artifact

/-- Check and, on exact success, lower straight to a rendered exact document via
the typed artifact/document pipeline. -/
def checkWithinRenderedDocument (available : AvailableSpace) (layout : Layout) :
    CheckResult ExactDocument.RenderedDocument :=
  (checkWithinArtifact available layout).map Artifact.renderedDocument

/-- Alias of `checkWithinRenderedDocument` at the public exact-check boundary. -/
def checkRenderedDocument (available : AvailableSpace) (layout : Layout) :
    CheckResult ExactDocument.RenderedDocument :=
  (checkArtifact available layout).map Artifact.renderedDocument

/-- Check and, on exact success, lower straight to rendered HTML text via the
typed artifact/document pipeline. -/
def checkWithinRenderHtml (available : AvailableSpace) (layout : Layout) :
    CheckResult String :=
  (checkWithinArtifact available layout).map Artifact.renderHtml

/-- Alias of `checkWithinRenderHtml` at the public exact-check boundary. -/
def checkRenderHtml (available : AvailableSpace) (layout : Layout) :
    CheckResult String :=
  (checkArtifact available layout).map Artifact.renderHtml

/-- Check and, on exact success, lower straight to rendered CSS text via the
typed artifact/document pipeline. -/
def checkWithinRenderCss (available : AvailableSpace) (layout : Layout) :
    CheckResult String :=
  (checkWithinArtifact available layout).map Artifact.renderCss

/-- Alias of `checkWithinRenderCss` at the public exact-check boundary. -/
def checkRenderCss (available : AvailableSpace) (layout : Layout) :
    CheckResult String :=
  (checkArtifact available layout).map Artifact.renderCss

theorem checkWithinRenderedDocument_exact_artifact
    {available : AvailableSpace}
    {layout : Layout}
    {rendered : ExactDocument.RenderedDocument}
    (h : checkWithinRenderedDocument available layout = .exact rendered) :
    ∃ artifact : Artifact,
      checkWithinArtifact available layout = .exact artifact ∧
      artifact.renderedDocument = rendered := by
  rcases exact_of_map_eq_exact
      (result := checkWithinArtifact available layout)
      (f := Artifact.renderedDocument)
      (output := rendered)
      (by simpa [checkWithinRenderedDocument] using h)
    with ⟨artifact, hArtifact, hRendered⟩
  exact ⟨artifact, hArtifact, hRendered⟩

theorem checkWithinRenderedDocument_exact_document
    {available : AvailableSpace}
    {layout : Layout}
    {rendered : ExactDocument.RenderedDocument}
    (h : checkWithinRenderedDocument available layout = .exact rendered) :
    ∃ artifact : Artifact,
      checkWithinArtifact available layout = .exact artifact ∧
      artifact.document.render = rendered := by
  rcases checkWithinRenderedDocument_exact_artifact h with ⟨artifact, hArtifact, hRendered⟩
  refine ⟨artifact, hArtifact, ?_⟩
  rw [Artifact.renderedDocument_eq_document_render artifact] at hRendered
  exact hRendered

theorem checkWithinRenderHtml_exact_artifact
    {available : AvailableSpace}
    {layout : Layout}
    {html : String}
    (h : checkWithinRenderHtml available layout = .exact html) :
    ∃ artifact : Artifact,
      checkWithinArtifact available layout = .exact artifact ∧
      artifact.renderHtml = html := by
  rcases exact_of_map_eq_exact
      (result := checkWithinArtifact available layout)
      (f := Artifact.renderHtml)
      (output := html)
      (by simpa [checkWithinRenderHtml] using h)
    with ⟨artifact, hArtifact, hHtml⟩
  exact ⟨artifact, hArtifact, hHtml⟩

theorem checkWithinRenderCss_exact_artifact
    {available : AvailableSpace}
    {layout : Layout}
    {css : String}
    (h : checkWithinRenderCss available layout = .exact css) :
    ∃ artifact : Artifact,
      checkWithinArtifact available layout = .exact artifact ∧
      artifact.renderCss = css := by
  rcases exact_of_map_eq_exact
      (result := checkWithinArtifact available layout)
      (f := Artifact.renderCss)
      (output := css)
      (by simpa [checkWithinRenderCss] using h)
    with ⟨artifact, hArtifact, hCss⟩
  exact ⟨artifact, hArtifact, hCss⟩

theorem checkRenderedDocument_exact_artifact
    {available : AvailableSpace}
    {layout : Layout}
    {rendered : ExactDocument.RenderedDocument}
    (h : checkRenderedDocument available layout = .exact rendered) :
    ∃ artifact : Artifact,
      checkArtifact available layout = .exact artifact ∧
      artifact.renderedDocument = rendered := by
  rcases exact_of_map_eq_exact
      (result := checkArtifact available layout)
      (f := Artifact.renderedDocument)
      (output := rendered)
      (by simpa [checkRenderedDocument] using h)
    with ⟨artifact, hArtifact, hRendered⟩
  exact ⟨artifact, hArtifact, hRendered⟩

theorem checkRenderedDocument_exact_document
    {available : AvailableSpace}
    {layout : Layout}
    {rendered : ExactDocument.RenderedDocument}
    (h : checkRenderedDocument available layout = .exact rendered) :
    ∃ artifact : Artifact,
      checkArtifact available layout = .exact artifact ∧
      artifact.document.render = rendered := by
  rcases checkRenderedDocument_exact_artifact h with ⟨artifact, hArtifact, hRendered⟩
  refine ⟨artifact, hArtifact, ?_⟩
  rw [Artifact.renderedDocument_eq_document_render artifact] at hRendered
  exact hRendered

theorem checkRenderHtml_exact_artifact
    {available : AvailableSpace}
    {layout : Layout}
    {html : String}
    (h : checkRenderHtml available layout = .exact html) :
    ∃ artifact : Artifact,
      checkArtifact available layout = .exact artifact ∧
      artifact.renderHtml = html := by
  rcases exact_of_map_eq_exact
      (result := checkArtifact available layout)
      (f := Artifact.renderHtml)
      (output := html)
      (by simpa [checkRenderHtml] using h)
    with ⟨artifact, hArtifact, hHtml⟩
  exact ⟨artifact, hArtifact, hHtml⟩

theorem checkRenderCss_exact_artifact
    {available : AvailableSpace}
    {layout : Layout}
    {css : String}
    (h : checkRenderCss available layout = .exact css) :
    ∃ artifact : Artifact,
      checkArtifact available layout = .exact artifact ∧
      artifact.renderCss = css := by
  rcases exact_of_map_eq_exact
      (result := checkArtifact available layout)
      (f := Artifact.renderCss)
      (output := css)
      (by simpa [checkRenderCss] using h)
    with ⟨artifact, hArtifact, hCss⟩
  exact ⟨artifact, hArtifact, hCss⟩

end TypedLayout.Backend.ExactCss
