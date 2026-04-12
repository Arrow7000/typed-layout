import TypedLayout.Backend.ExactCss

namespace TypedLayout.Backend.ExactCss

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

end TypedLayout.Backend.ExactCss
