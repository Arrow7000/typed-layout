import TypedLayout.Core.Contract

namespace TypedLayout.Backend.ExactCss

open TypedLayout.Core

/-- Exact-fragment CSS length domain. The current backend layer only lowers to
concrete pixel lengths. -/
inductive Length where
  | px (value : Nat)
  deriving DecidableEq, Repr

namespace Length

def ofNat (value : Nat) : Length :=
  .px value

end Length

/-- Exact-fragment CSS width/height pair. -/
structure Size where
  width : Length
  height : Length
  deriving DecidableEq, Repr

namespace Size

def ofExtent (extent : ExactExtent) : Size :=
  { width := .px extent.width
  , height := .px extent.height
  }

end Size

/-- Typed CSS padding/inset payload for the exact fragment. -/
structure Padding where
  left : Length
  top : Length
  right : Length
  bottom : Length
  deriving DecidableEq, Repr

namespace Padding

def zero : Padding :=
  { left := .px 0
  , top := .px 0
  , right := .px 0
  , bottom := .px 0
  }

def ofInsets (insets : Insets) : Padding :=
  { left := .px insets.left
  , top := .px insets.top
  , right := .px insets.right
  , bottom := .px insets.bottom
  }

end Padding

inductive BoxSizing where
  | borderBox
  deriving DecidableEq, Repr

inductive FlexDirection where
  | row
  | column
  deriving DecidableEq, Repr

namespace FlexDirection

def ofAxis : Axis → FlexDirection
  | .horizontal => .row
  | .vertical => .column

end FlexDirection

inductive FlexWrap where
  | nowrap
  deriving DecidableEq, Repr

inductive JustifyContent where
  | flexStart
  deriving DecidableEq, Repr

inductive AlignItems where
  | flexStart
  deriving DecidableEq, Repr

/-- Flex-container payload restricted to the current exact 1D fragment. -/
structure FlexContainer where
  direction : FlexDirection
  gap : Length
  wrap : FlexWrap
  justifyContent : JustifyContent
  alignItems : AlignItems
  deriving DecidableEq, Repr

namespace FlexContainer

def exact1D (axis : Axis) (gap : Gap) : FlexContainer :=
  { direction := FlexDirection.ofAxis axis
  , gap := .px gap.amount
  , wrap := .nowrap
  , justifyContent := .flexStart
  , alignItems := .flexStart
  }

end FlexContainer

/-- Flex-item payload used to keep exact child extents fixed inside stackers. -/
structure FlexItem where
  grow : Nat
  shrink : Nat
  deriving DecidableEq, Repr

namespace FlexItem

def fixed : FlexItem :=
  { grow := 0, shrink := 0 }

end FlexItem

inductive Display where
  | block
  | flex (container : FlexContainer)
  deriving DecidableEq, Repr

/-- Typed style IR for the exact CSS backend fragment.

This stays intentionally small: border-box sizing, exact width/height, optional
padding, a block-or-flex display model, and the fixed flex-item policy needed by
the current exact row/column fragment. -/
structure Style where
  boxSizing : BoxSizing
  size : Size
  padding : Padding
  display : Display
  flexItem : FlexItem
  deriving DecidableEq, Repr

namespace Style

def block (extent : ExactExtent) (padding : Padding := Padding.zero) : Style :=
  { boxSizing := .borderBox
  , size := Size.ofExtent extent
  , padding := padding
  , display := .block
  , flexItem := FlexItem.fixed
  }

def stack (axis : Axis) (gap : Gap) (extent : ExactExtent) : Style :=
  { boxSizing := .borderBox
  , size := Size.ofExtent extent
  , padding := Padding.zero
  , display := .flex (FlexContainer.exact1D axis gap)
  , flexItem := FlexItem.fixed
  }

def ofCheckedLayout : CheckedLayout → Style
  | .leaf extent =>
      block extent
  | .row gap children =>
      stack .horizontal gap <| ExactExtent.stack .horizontal gap (children.map CheckedLayout.extent)
  | .column gap children =>
      stack .vertical gap <| ExactExtent.stack .vertical gap (children.map CheckedLayout.extent)
  | .padding insets child =>
      block (child.extent.expand insets) (Padding.ofInsets insets)
  | .frame extent _ =>
      block extent

theorem ofCheckedLayout_size (layout : CheckedLayout) :
    (ofCheckedLayout layout).size = Size.ofExtent layout.extent := by
  cases layout <;> simp [ofCheckedLayout, block, stack, Size.ofExtent, CheckedLayout.extent]

end Style

/-- Typed backend node IR for the current exact fragment. -/
structure Node where
  kind : LayoutKind
  style : Style
  children : List Node
  deriving Repr

mutual

private def decEqNode : (left right : Node) → Decidable (left = right)
  | ⟨leftKind, leftStyle, leftChildren⟩, ⟨rightKind, rightStyle, rightChildren⟩ =>
      match decEq leftKind rightKind with
      | isFalse hKind =>
          isFalse (by
            intro h
            injection h with hKind'
            exact hKind hKind')
      | isTrue hKind =>
          match decEq leftStyle rightStyle with
          | isFalse hStyle =>
              isFalse (by
                intro h
                injection h with _ hStyle'
                exact hStyle hStyle')
          | isTrue hStyle =>
              match decEqNodeList leftChildren rightChildren with
              | isFalse hChildren =>
                  isFalse (by
                    intro h
                    injection h with _ _ hChildren'
                    exact hChildren hChildren')
              | isTrue hChildren =>
                  isTrue (by
                    cases hKind
                    cases hStyle
                    cases hChildren
                    rfl)

private def decEqNodeList : (left right : List Node) → Decidable (left = right)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | leftHead :: leftTail, rightHead :: rightTail =>
      match decEqNode leftHead rightHead with
      | isFalse hHead =>
          isFalse (by
            intro h
            injection h with hHead'
            exact hHead hHead')
      | isTrue hHead =>
          match decEqNodeList leftTail rightTail with
          | isFalse hTail =>
              isFalse (by
                intro h
                injection h with _ hTail'
                exact hTail hTail')
          | isTrue hTail =>
              isTrue (by
                cases hHead
                cases hTail
                rfl)

end

instance : DecidableEq Node := decEqNode

namespace Node

mutual

def ofCheckedLayout : CheckedLayout → Node
  | .leaf extent =>
      { kind := .leaf
      , style := Style.ofCheckedLayout (.leaf extent)
      , children := []
      }
  | .row gap children =>
      { kind := .row
      , style := Style.ofCheckedLayout (.row gap children)
      , children := ofCheckedLayouts children
      }
  | .column gap children =>
      { kind := .column
      , style := Style.ofCheckedLayout (.column gap children)
      , children := ofCheckedLayouts children
      }
  | .padding insets child =>
      { kind := .padding
      , style := Style.ofCheckedLayout (.padding insets child)
      , children := [ofCheckedLayout child]
      }
  | .frame extent child =>
      { kind := .frame
      , style := Style.ofCheckedLayout (.frame extent child)
      , children := [ofCheckedLayout child]
      }

termination_by
  layout => sizeOf layout

decreasing_by
  all_goals simp_wf
  all_goals omega

def ofCheckedLayouts : List CheckedLayout → List Node
  | [] => []
  | child :: rest => ofCheckedLayout child :: ofCheckedLayouts rest

termination_by
  children => sizeOf children

decreasing_by
  all_goals simp_wf
  all_goals omega

end

theorem ofCheckedLayout_kind (layout : CheckedLayout) :
    (ofCheckedLayout layout).kind = layout.kind := by
  cases layout <;> simp [ofCheckedLayout, CheckedLayout.kind]

theorem ofCheckedLayout_style (layout : CheckedLayout) :
    (ofCheckedLayout layout).style = Style.ofCheckedLayout layout := by
  cases layout <;> simp [ofCheckedLayout]

theorem ofCheckedLayout_size (layout : CheckedLayout) :
    (ofCheckedLayout layout).style.size = Size.ofExtent layout.extent := by
  rw [ofCheckedLayout_style]
  exact Style.ofCheckedLayout_size layout

end Node

/-- Root-level lowering artifact for the exact CSS backend fragment.

The artifact carries the source-side exact contract envelope alongside the typed
backend node tree. It is still only a lowering target: no raw CSS emission or
backend-fidelity proof is claimed here. -/
structure Artifact where
  targetProfile : BlessedCssProfile
  sourceKind : LayoutKind
  sourceGuarantee : GuaranteeClass
  inputBounds : ExtentBounds
  outputBounds : ExtentBounds
  root : Node
  deriving DecidableEq, Repr

namespace Artifact

def ofCheckedWithin {available : AvailableSpace}
    (checked : CheckedWithin available) : Artifact :=
  { targetProfile := .exact1D_v1
  , sourceKind := checked.layout.kind
  , sourceGuarantee := .exact
  , inputBounds := available.bounds
  , outputBounds := checked.extentBounds
  , root := Node.ofCheckedLayout checked.layout
  }

theorem ofCheckedWithin_targetProfile {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).targetProfile = .exact1D_v1 :=
  rfl

theorem ofCheckedWithin_sourceKind {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).sourceKind = checked.layout.kind :=
  rfl

theorem ofCheckedWithin_sourceGuarantee_exact {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).sourceGuarantee = .exact :=
  rfl

theorem ofCheckedWithin_inputBounds {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).inputBounds = available.bounds :=
  rfl

theorem ofCheckedWithin_outputBounds {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).outputBounds = checked.extentBounds :=
  rfl

theorem ofCheckedWithin_outputBounds_within_inputBounds {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).inputBounds.containsBounds
      (ofCheckedWithin checked).outputBounds := by
  simpa [ofCheckedWithin] using checked.extentBounds_within_availableBounds

def ofCertifiedWithin {available : AvailableSpace}
    (certified : CertifiedWithin available) : Artifact :=
  { targetProfile := .exact1D_v1
  , sourceKind := certified.contract.kind
  , sourceGuarantee := certified.contract.guarantee
  , inputBounds := certified.contract.input.bounds
  , outputBounds := certified.contract.output.bounds
  , root := Node.ofCheckedLayout certified.layout
  }

theorem ofCertifiedWithin_eq_ofCheckedWithin {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    ofCertifiedWithin certified = ofCheckedWithin certified.checked := by
  cases certified
  rfl

theorem ofCheckedWithin_root_matches_sourceKind {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).root.kind = (ofCheckedWithin checked).sourceKind := by
  simp [ofCheckedWithin, Node.ofCheckedLayout_kind]

theorem ofCertifiedWithin_targetProfile {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).targetProfile = .exact1D_v1 :=
  rfl

theorem ofCertifiedWithin_sourceKind {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).sourceKind = certified.layout.kind := by
  simpa [ofCertifiedWithin, CertifiedWithin.contract] using
    ExactLayoutContract.ofCertifiedWithin_kind certified

theorem ofCertifiedWithin_inputBounds {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).inputBounds = available.bounds := by
  simpa [ofCertifiedWithin, CertifiedWithin.contract] using
    ExactLayoutContract.ofCertifiedWithin_input_bounds certified

theorem ofCheckedWithin_root_kind {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).root.kind = checked.layout.kind := by
  simp [ofCheckedWithin, Node.ofCheckedLayout_kind]

theorem ofCheckedWithin_root_size {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).root.style.size = Size.ofExtent checked.extent := by
  simpa [CheckedWithin.extent, ofCheckedWithin] using Node.ofCheckedLayout_size checked.layout

theorem ofCertifiedWithin_root_kind {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).root.kind = certified.layout.kind := by
  simp [ofCertifiedWithin, Node.ofCheckedLayout_kind]

theorem ofCertifiedWithin_sourceGuarantee {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).sourceGuarantee = certified.contract.guarantee := by
  rfl

theorem ofCertifiedWithin_sourceGuarantee_exact {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).sourceGuarantee = .exact := by
  rw [ofCertifiedWithin_sourceGuarantee]
  exact certified.contract_guarantee

theorem ofCertifiedWithin_outputBounds {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).outputBounds = certified.contract.output.bounds := by
  rfl

theorem ofCertifiedWithin_outputBounds_within_inputBounds {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).inputBounds.containsBounds
      (ofCertifiedWithin certified).outputBounds := by
  simpa [ofCertifiedWithin] using
    certified.contract_output_bounds_within_input_bounds

theorem ofCertifiedWithin_root_size {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).root.style.size = Size.ofExtent certified.extent := by
  simpa [CertifiedWithin.extent, ofCertifiedWithin] using Node.ofCheckedLayout_size certified.layout

theorem ofCertifiedWithin_root_matches_sourceKind {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).root.kind = (ofCertifiedWithin certified).sourceKind := by
  simp [ofCertifiedWithin_root_kind certified, ofCertifiedWithin_sourceKind certified]

end Artifact

/- Typed HTML/CSS document IR for the current exact backend fragment.

This stays intentionally small and div-centric: a stylesheet is a list of typed
class rules that reuse the exact backend `Style`, and the HTML side is just a
`body` wrapper around generated `div` elements. -/
namespace ExactDocument

/-- Generated stylesheet class handle for lowered exact nodes. -/
structure ClassName where
  serial : Nat
  deriving DecidableEq, Repr

/-- Tiny exact-fragment HTML tag domain. -/
inductive Tag where
  | body
  | div
  deriving DecidableEq, Repr

/-- Exact-fragment HTML element tree.

The current lowering only emits `div` elements with generated classes, wrapped in
an unstyled `body`. -/
inductive Element where
  | node (tag : Tag) (classes : List ClassName) (children : List Element)
  deriving Repr

mutual

private def decEqElement : (left right : Element) → Decidable (left = right)
  | .node leftTag leftClasses leftChildren, .node rightTag rightClasses rightChildren =>
      match decEq leftTag rightTag with
      | isFalse hTag =>
          isFalse (by
            intro h
            injection h with hTag'
            exact hTag hTag')
      | isTrue hTag =>
          match decEq leftClasses rightClasses with
          | isFalse hClasses =>
              isFalse (by
                intro h
                injection h with _ hClasses'
                exact hClasses hClasses')
          | isTrue hClasses =>
              match decEqElementList leftChildren rightChildren with
              | isFalse hChildren =>
                  isFalse (by
                    intro h
                    injection h with _ _ hChildren'
                    exact hChildren hChildren')
              | isTrue hChildren =>
                  isTrue (by
                    cases hTag
                    cases hClasses
                    cases hChildren
                    rfl)

private def decEqElementList : (left right : List Element) → Decidable (left = right)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | leftHead :: leftTail, rightHead :: rightTail =>
      match decEqElement leftHead rightHead with
      | isFalse hHead =>
          isFalse (by
            intro h
            injection h with hHead'
            exact hHead hHead')
      | isTrue hHead =>
          match decEqElementList leftTail rightTail with
          | isFalse hTail =>
              isFalse (by
                intro h
                injection h with _ hTail'
                exact hTail hTail')
          | isTrue hTail =>
              isTrue (by
                cases hHead
                cases hTail
                rfl)

end

instance : DecidableEq Element := decEqElement

namespace Element

def body (children : List Element) : Element :=
  .node .body [] children

def div (className : ClassName) (children : List Element := []) : Element :=
  .node .div [className] children

def tag : Element → Tag
  | .node tag _ _ => tag

def classes : Element → List ClassName
  | .node _ classes _ => classes

def children : Element → List Element
  | .node _ _ children => children

mutual

/-- Collect all generated class references used by an exact-fragment element tree. -/
def classReferences : Element → List ClassName
  | .node _ classes children => classes ++ classReferencesList children

/-- Collect all generated class references used by a list of exact-fragment elements. -/
def classReferencesList : List Element → List ClassName
  | [] => []
  | child :: rest => classReferences child ++ classReferencesList rest

end

end Element

/-- Exact-fragment stylesheet rule keyed by a generated class handle. -/
structure ClassRule where
  className : ClassName
  style : Style
  deriving DecidableEq, Repr

/-- Exact-fragment stylesheet. -/
structure Stylesheet where
  rules : List ClassRule
  deriving DecidableEq, Repr

/-- Exact-fragment HTML/CSS document.

The document keeps HTML structure and CSS structure separate while still reusing
the typed exact backend style domain. -/
structure Document where
  body : Element
  stylesheet : Stylesheet
  deriving DecidableEq, Repr

namespace ClassName

/-- Collect raw serial numbers from generated exact-fragment class handles. -/
def serials : List ClassName → List Nat
  | [] => []
  | className :: rest => className.serial :: serials rest

end ClassName

namespace ClassRule

/-- Collect generated class handles from exact-fragment stylesheet rules. -/
def classNames (rules : List ClassRule) : List ClassName :=
  rules.map ClassRule.className

theorem classNames_append (left right : List ClassRule) :
    classNames (left ++ right) = classNames left ++ classNames right := by
  simp [classNames]

end ClassRule

namespace Stylesheet

/-- Collect generated class handles keyed by an exact-fragment stylesheet. -/
def classNames (stylesheet : Stylesheet) : List ClassName :=
  ClassRule.classNames stylesheet.rules

end Stylesheet

namespace Document

/-- Collect all generated class references used by the document body tree. -/
def classReferences (document : Document) : List ClassName :=
  document.body.classReferences

/-- Collect all generated class handles owned by the stylesheet rules. -/
def ruleClassNames (document : Document) : List ClassName :=
  document.stylesheet.classNames

/-- Structural sanity property: stylesheet rule class names are pairwise distinct. -/
def ruleClassNamesNodup (document : Document) : Prop :=
  document.ruleClassNames.Nodup

/-- Structural sanity property: every body-tree class reference is covered by a stylesheet rule. -/
def classReferencesCoveredByStylesheet (document : Document) : Prop :=
  ∀ className, className ∈ document.classReferences → className ∈ document.ruleClassNames

/-- Structural sanity property: lowered exact documents use an unstyled body with exactly one root child. -/
def singleRootBody (document : Document) : Prop :=
  document.body.tag = .body ∧
    document.body.classes = [] ∧
    document.body.children.length = 1

end Document

mutual

private def nodeRuleCount : Node → Nat
  | ⟨_, _, children⟩ => 1 + nodesRuleCount children

private def nodesRuleCount : List Node → Nat
  | [] => 0
  | child :: rest => nodeRuleCount child + nodesRuleCount rest

end

private def classSpan (start count : Nat) : List ClassName :=
  match count with
  | 0 => []
  | count + 1 => { serial := start } :: classSpan (start + 1) count

private theorem classSpan_append (start leftCount rightCount : Nat) :
    classSpan start leftCount ++ classSpan (start + leftCount) rightCount =
      classSpan start (leftCount + rightCount) := by
  induction leftCount generalizing start with
  | zero =>
      simp [classSpan]
  | succ leftCount ih =>
      simpa [classSpan, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        congrArg (List.cons { serial := start }) (ih (start + 1))

private theorem classSpan_mem_serial_ge
    {start count : Nat}
    {className : ClassName}
    (h : className ∈ classSpan start count) :
    start ≤ className.serial := by
  induction count generalizing start with
  | zero =>
      simp [classSpan] at h
  | succ count ih =>
      simp [classSpan] at h
      rcases h with hEq | hTail
      · cases hEq
        exact Nat.le_refl _
      · exact Nat.le_trans (Nat.le_succ _) (ih (start := start + 1) hTail)

private theorem classSpan_nodup (start count : Nat) :
    (classSpan start count).Nodup := by
  induction count generalizing start with
  | zero =>
      simp [classSpan]
  | succ count ih =>
      simp [classSpan, ih]
      intro hMem
      have hImpossible : start + 1 ≤ start := by
        simpa using classSpan_mem_serial_ge (start := start + 1) (count := count) hMem
      exact Nat.not_succ_le_self start hImpossible

private theorem sizeOf_children_lt (node : Node) :
    sizeOf node.children < sizeOf node := by
  cases node
  simp
  omega

private theorem sizeOf_head_lt_cons (child : Node) (rest : List Node) :
    sizeOf child < sizeOf (child :: rest) := by
  simp
  omega

private theorem sizeOf_tail_lt_cons (child : Node) (rest : List Node) :
    sizeOf rest < sizeOf (child :: rest) := by
  simp
  omega

private structure LoweredNode where
  element : Element
  rules : List ClassRule
  nextClass : Nat

private structure LoweredNodes where
  elements : List Element
  rules : List ClassRule
  nextClass : Nat

mutual

private def lowerNode (nextClass : Nat) : Node → LoweredNode
  | node =>
      let className : ClassName := { serial := nextClass }
      let loweredChildren := lowerNodes (nextClass + 1) node.children
      { element := Element.div className loweredChildren.elements
      , rules := { className := className, style := node.style } :: loweredChildren.rules
      , nextClass := loweredChildren.nextClass
      }

termination_by
  node => sizeOf node

decreasing_by
  · exact sizeOf_children_lt node

private def lowerNodes (nextClass : Nat) : List Node → LoweredNodes
  | [] =>
      { elements := []
      , rules := []
      , nextClass := nextClass
      }
  | child :: rest =>
      let loweredChild := lowerNode nextClass child
      let loweredRest := lowerNodes loweredChild.nextClass rest
      { elements := loweredChild.element :: loweredRest.elements
      , rules := loweredChild.rules ++ loweredRest.rules
      , nextClass := loweredRest.nextClass
      }

termination_by
  children => sizeOf children

decreasing_by
  · exact sizeOf_head_lt_cons child rest
  · exact sizeOf_tail_lt_cons child rest

end

mutual

private theorem lowerNode_nextClass (nextClass : Nat) :
    ∀ node : Node, (lowerNode nextClass node).nextClass = nextClass + nodeRuleCount node
  | ⟨_, _, children⟩ => by
      simp [lowerNode, nodeRuleCount, lowerNodes_nextClass, Nat.add_assoc]

private theorem lowerNodes_nextClass (nextClass : Nat) :
    ∀ nodes : List Node, (lowerNodes nextClass nodes).nextClass = nextClass + nodesRuleCount nodes
  | [] => by
      simp [lowerNodes, nodesRuleCount]
  | child :: rest => by
      simp [lowerNodes, nodesRuleCount, lowerNode_nextClass, lowerNodes_nextClass,
        Nat.add_assoc]

end

mutual

private theorem lowerNode_ruleClassNames (nextClass : Nat) :
    ∀ node : Node,
      ClassRule.classNames (lowerNode nextClass node).rules =
        classSpan nextClass (nodeRuleCount node)
  | ⟨_, _, children⟩ => by
      unfold lowerNode
      simp [ClassRule.classNames, nodeRuleCount]
      change { serial := nextClass } ::
          List.map ClassRule.className (lowerNodes (nextClass + 1) children).rules =
        classSpan nextClass (1 + nodesRuleCount children)
      have hChildren :
          { serial := nextClass } ::
              List.map ClassRule.className (lowerNodes (nextClass + 1) children).rules =
            { serial := nextClass } :: classSpan (nextClass + 1) (nodesRuleCount children) := by
        exact congrArg (fun classNames => { serial := nextClass } :: classNames)
          (lowerNodes_ruleClassNames (nextClass := nextClass + 1) children)
      have hSpan :
          classSpan nextClass (1 + nodesRuleCount children) =
            { serial := nextClass } :: classSpan (nextClass + 1) (nodesRuleCount children) := by
        rw [Nat.add_comm]
        rfl
      rw [hSpan]
      exact hChildren

private theorem lowerNodes_ruleClassNames (nextClass : Nat) :
    ∀ nodes : List Node,
      ClassRule.classNames (lowerNodes nextClass nodes).rules =
        classSpan nextClass (nodesRuleCount nodes)
  | [] => by
      simp [lowerNodes, ClassRule.classNames, nodesRuleCount, classSpan]
  | child :: rest => by
      rw [lowerNodes]
      rw [ClassRule.classNames_append]
      rw [lowerNode_ruleClassNames, lowerNodes_ruleClassNames, lowerNode_nextClass]
      exact classSpan_append nextClass (nodeRuleCount child) (nodesRuleCount rest)

end

mutual

private theorem lowerNode_elementClassReferences (nextClass : Nat) :
    ∀ node : Node,
      (lowerNode nextClass node).element.classReferences =
        classSpan nextClass (nodeRuleCount node)
  | ⟨_, _, children⟩ => by
      unfold lowerNode
      simp [Element.div, Element.classReferences, nodeRuleCount]
      change { serial := nextClass } ::
          Element.classReferencesList (lowerNodes (nextClass + 1) children).elements =
        classSpan nextClass (1 + nodesRuleCount children)
      have hChildren :
          { serial := nextClass } ::
              Element.classReferencesList (lowerNodes (nextClass + 1) children).elements =
            { serial := nextClass } :: classSpan (nextClass + 1) (nodesRuleCount children) := by
        exact congrArg (fun classNames => { serial := nextClass } :: classNames)
          (lowerNodes_elementClassReferencesList (nextClass := nextClass + 1) children)
      have hSpan :
          classSpan nextClass (1 + nodesRuleCount children) =
            { serial := nextClass } :: classSpan (nextClass + 1) (nodesRuleCount children) := by
        rw [Nat.add_comm]
        rfl
      rw [hSpan]
      exact hChildren

private theorem lowerNodes_elementClassReferencesList (nextClass : Nat) :
    ∀ nodes : List Node,
      Element.classReferencesList (lowerNodes nextClass nodes).elements =
        classSpan nextClass (nodesRuleCount nodes)
  | [] => by
      simp [lowerNodes, Element.classReferencesList, nodesRuleCount, classSpan]
  | child :: rest => by
      rw [lowerNodes]
      simp [Element.classReferencesList]
      rw [lowerNode_elementClassReferences, lowerNodes_elementClassReferencesList,
        lowerNode_nextClass]
      exact classSpan_append nextClass (nodeRuleCount child) (nodesRuleCount rest)

end

/-- Lower a backend node tree into the tiny exact-fragment HTML/CSS document IR. -/
def ofNode (node : Node) : Document :=
  let lowered := lowerNode 0 node
  { body := Element.body [lowered.element]
  , stylesheet := { rules := lowered.rules }
  }

/-- Lower a backend artifact into the tiny exact-fragment HTML/CSS document IR. -/
def ofArtifact (artifact : Artifact) : Document :=
  ofNode artifact.root

theorem ofArtifact_eq_ofNode (artifact : Artifact) :
    ofArtifact artifact = ofNode artifact.root :=
  rfl

namespace Document

theorem ofNode_classReferences_eq_ruleClassNames (node : Node) :
    (ExactDocument.ofNode node).classReferences = (ExactDocument.ofNode node).ruleClassNames := by
  simp [Document.classReferences, Document.ruleClassNames, ExactDocument.ofNode,
    Element.body,
    Stylesheet.classNames, Element.classReferences, Element.classReferencesList,
    lowerNode_elementClassReferences, lowerNode_ruleClassNames]

theorem ofNode_ruleClassNamesNodup (node : Node) :
    (ExactDocument.ofNode node).ruleClassNamesNodup := by
  simp [Document.ruleClassNamesNodup, Document.ruleClassNames, ExactDocument.ofNode,
    Stylesheet.classNames, lowerNode_ruleClassNames, classSpan_nodup]

theorem ofNode_classReferencesCoveredByStylesheet (node : Node) :
    (ExactDocument.ofNode node).classReferencesCoveredByStylesheet := by
  intro className hMem
  simpa [ofNode_classReferences_eq_ruleClassNames node] using hMem

theorem ofNode_singleRootBody (node : Node) :
    (ExactDocument.ofNode node).singleRootBody := by
  simp [Document.singleRootBody, Element.tag, Element.classes, Element.children,
    ExactDocument.ofNode, Element.body]

theorem ofArtifact_classReferences_eq_ruleClassNames (artifact : Artifact) :
    (ExactDocument.ofArtifact artifact).classReferences =
      (ExactDocument.ofArtifact artifact).ruleClassNames := by
  simpa [ExactDocument.ofArtifact] using ofNode_classReferences_eq_ruleClassNames artifact.root

theorem ofArtifact_ruleClassNamesNodup (artifact : Artifact) :
    (ExactDocument.ofArtifact artifact).ruleClassNamesNodup := by
  simpa [ExactDocument.ofArtifact] using ofNode_ruleClassNamesNodup artifact.root

theorem ofArtifact_classReferencesCoveredByStylesheet (artifact : Artifact) :
    (ExactDocument.ofArtifact artifact).classReferencesCoveredByStylesheet := by
  simpa [ExactDocument.ofArtifact] using
    ofNode_classReferencesCoveredByStylesheet artifact.root

theorem ofArtifact_singleRootBody (artifact : Artifact) :
    (ExactDocument.ofArtifact artifact).singleRootBody := by
  simpa [ExactDocument.ofArtifact] using ofNode_singleRootBody artifact.root

end Document

namespace Fidelity

/-- Typed backend-fidelity expectation for one lowered exact-fragment node. -/
structure NodeExpectation where
  className : ClassName
  kind : LayoutKind
  style : Style
  box : Box
  deriving DecidableEq, Repr

namespace NodeExpectation

def origin (expectation : NodeExpectation) : Origin :=
  expectation.box.origin

def extent (expectation : NodeExpectation) : ExactExtent :=
  expectation.box.extent

def size (expectation : NodeExpectation) : Size :=
  expectation.style.size

end NodeExpectation

/-- Typed backend-fidelity expectations for a fully lowered exact document.

The bundle keeps the future harness boundary typed: generated classes stay as
typed labels, backend styles stay in the exact backend IR, and geometry stays in
source-semantic boxes instead of loose rendered strings.
-/
structure DocumentExpectation where
  targetProfile : BlessedCssProfile
  sourceGuarantee : GuaranteeClass
  root : NodeExpectation
  nodes : List NodeExpectation
  deriving DecidableEq, Repr

namespace DocumentExpectation

def nodeCount (expectation : DocumentExpectation) : Nat :=
  expectation.nodes.length

def rootClassName (expectation : DocumentExpectation) : ClassName :=
  expectation.root.className

def labels (expectation : DocumentExpectation) : List ClassName :=
  expectation.nodes.map NodeExpectation.className

def kinds (expectation : DocumentExpectation) : List LayoutKind :=
  expectation.nodes.map NodeExpectation.kind

def styles (expectation : DocumentExpectation) : List Style :=
  expectation.nodes.map NodeExpectation.style

def boxes (expectation : DocumentExpectation) : List Box :=
  expectation.nodes.map NodeExpectation.box

def sizes (expectation : DocumentExpectation) : List Size :=
  expectation.nodes.map NodeExpectation.size

theorem labels_length (expectation : DocumentExpectation) :
    expectation.labels.length = expectation.nodeCount := by
  simp [labels, nodeCount]

theorem boxes_length (expectation : DocumentExpectation) :
    expectation.boxes.length = expectation.nodeCount := by
  simp [boxes, nodeCount]

theorem styles_length (expectation : DocumentExpectation) :
    expectation.styles.length = expectation.nodeCount := by
  simp [styles, nodeCount]

theorem sizes_length (expectation : DocumentExpectation) :
    expectation.sizes.length = expectation.nodeCount := by
  simp [sizes, nodeCount]

end DocumentExpectation

private structure SourceNode where
  kind : LayoutKind
  box : Box
  deriving DecidableEq, Repr

mutual

private def sourceNodesAt (origin : Origin) : CheckedLayout → List SourceNode
  | .leaf extent =>
      [ { kind := .leaf
        , box := { origin := origin, extent := extent }
        } ]
  | .row gap children =>
      { kind := .row
      , box := { origin := origin, extent := CheckedLayout.extent (.row gap children) }
      } :: sourceNodesAlong .horizontal origin gap 0 children
  | .column gap children =>
      { kind := .column
      , box := { origin := origin, extent := CheckedLayout.extent (.column gap children) }
      } :: sourceNodesAlong .vertical origin gap 0 children
  | .padding insets child =>
      { kind := .padding
      , box := { origin := origin, extent := CheckedLayout.extent (.padding insets child) }
      } :: sourceNodesAt (origin.translate insets.left insets.top) child
  | .frame extent child =>
      { kind := .frame
      , box := { origin := origin, extent := extent }
      } :: sourceNodesAt origin child

termination_by
  layout => sizeOf layout

decreasing_by
  all_goals simp_wf
  all_goals omega

private def sourceNodesAlong
    (axis : Axis)
    (origin : Origin)
    (gap : Gap)
    (cursor : Nat)
    : List CheckedLayout → List SourceNode
  | [] => []
  | child :: rest =>
      sourceNodesAt (origin.translateAxis axis cursor) child ++
        sourceNodesAlong axis origin gap (cursor + child.mainExtent axis + gap.amount) rest

termination_by
  children => sizeOf children

decreasing_by
  all_goals simp_wf
  all_goals omega

end

mutual

private theorem sourceNodesAt_length (origin : Origin) :
    ∀ layout : CheckedLayout,
      (sourceNodesAt origin layout).length = nodeRuleCount (Node.ofCheckedLayout layout)
  | .leaf _ => by
      simp [sourceNodesAt, nodeRuleCount, nodesRuleCount, Node.ofCheckedLayout]
  | .row gap children => by
      simp [sourceNodesAt, sourceNodesAlong_length, nodeRuleCount, Node.ofCheckedLayout,
        Nat.add_comm]
  | .column gap children => by
      simp [sourceNodesAt, sourceNodesAlong_length, nodeRuleCount, Node.ofCheckedLayout,
        Nat.add_comm]
  | .padding insets child => by
      simp [sourceNodesAt, sourceNodesAt_length, nodeRuleCount, Node.ofCheckedLayout,
        nodesRuleCount, Nat.add_comm]
  | .frame extent child => by
      simp [sourceNodesAt, sourceNodesAt_length, nodeRuleCount, Node.ofCheckedLayout,
        nodesRuleCount, Nat.add_comm]

private theorem sourceNodesAlong_length
    (axis : Axis)
    (origin : Origin)
    (gap : Gap)
    (cursor : Nat) :
    ∀ children : List CheckedLayout,
      (sourceNodesAlong axis origin gap cursor children).length =
        nodesRuleCount (Node.ofCheckedLayouts children)
  | [] => by
      simp [sourceNodesAlong, nodesRuleCount, Node.ofCheckedLayouts]
  | child :: rest => by
      simp [sourceNodesAlong, sourceNodesAt_length, sourceNodesAlong_length,
        nodesRuleCount, Node.ofCheckedLayouts, Nat.add_assoc]

end

private theorem classSpan_length (start count : Nat) :
    (classSpan start count).length = count := by
  induction count generalizing start with
  | zero =>
      simp [classSpan]
  | succ count ih =>
      simp [classSpan, ih]

private theorem lowerNode_rules_length (nextClass : Nat) (node : Node) :
    (lowerNode nextClass node).rules.length = nodeRuleCount node := by
  have hLengths := congrArg List.length (lowerNode_ruleClassNames nextClass node)
  simpa [ClassRule.classNames, classSpan_length] using hLengths

private def stitchExpectations : List ClassRule → List SourceNode → List NodeExpectation
  | [], [] => []
  | rule :: rules, source :: sources =>
      { className := rule.className
      , kind := source.kind
      , style := rule.style
      , box := source.box
      } :: stitchExpectations rules sources
  | [], _ :: _ => []
  | _ :: _, [] => []

private theorem stitchExpectations_labels
    {rules : List ClassRule}
    {sources : List SourceNode}
    (hLen : rules.length = sources.length) :
    (stitchExpectations rules sources).map NodeExpectation.className =
      rules.map ClassRule.className := by
  induction rules generalizing sources with
  | nil =>
      cases sources with
      | nil =>
          simp [stitchExpectations]
      | cons source sources =>
          simp at hLen
  | cons rule rest ih =>
      cases sources with
      | nil =>
          simp at hLen
      | cons source tail =>
          simp at hLen
          simp [stitchExpectations, ih hLen]

private theorem stitchExpectations_styles
    {rules : List ClassRule}
    {sources : List SourceNode}
    (hLen : rules.length = sources.length) :
    (stitchExpectations rules sources).map NodeExpectation.style =
      rules.map ClassRule.style := by
  induction rules generalizing sources with
  | nil =>
      cases sources with
      | nil =>
          simp [stitchExpectations]
      | cons source sources =>
          simp at hLen
  | cons rule rest ih =>
      cases sources with
      | nil =>
          simp at hLen
      | cons source tail =>
          simp at hLen
          simp [stitchExpectations, ih hLen]

private theorem stitchExpectations_length
    {rules : List ClassRule}
    {sources : List SourceNode}
    (hLen : rules.length = sources.length) :
    (stitchExpectations rules sources).length = rules.length := by
  induction rules generalizing sources with
  | nil =>
      cases sources with
      | nil =>
          simp [stitchExpectations]
      | cons source sources =>
          simp at hLen
  | cons rule rest ih =>
      cases sources with
      | nil =>
          simp at hLen
      | cons source tail =>
          simp at hLen
          simp [stitchExpectations, ih hLen]

private theorem checked_sourceNodes_length_eq_rules_length
    {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (sourceNodesAt Origin.zero checked.layout).length =
      (lowerNode 0 (Artifact.ofCheckedWithin checked).root).rules.length := by
  rw [sourceNodesAt_length, lowerNode_rules_length]
  simp [Artifact.ofCheckedWithin]

/-- Derive a typed exact-fragment backend-fidelity expectation bundle from a
successful exact check.

The bundle is intentionally render-free. It keeps generated classes and lowered
styles from the backend/document pipeline while attaching source-semantic boxes
for the same preorder of nodes.
-/
def ofCheckedWithin {available : AvailableSpace}
    (checked : CheckedWithin available) : DocumentExpectation :=
  let artifact := Artifact.ofCheckedWithin checked
  { targetProfile := artifact.targetProfile
  , sourceGuarantee := artifact.sourceGuarantee
  , root :=
      { className := { serial := 0 }
      , kind := checked.layout.kind
      , style := Style.ofCheckedLayout checked.layout
      , box := checked.evaluate.box
      }
  , nodes :=
      stitchExpectations
        (lowerNode 0 artifact.root).rules
        (sourceNodesAt Origin.zero checked.layout)
  }

theorem ofCheckedWithin_targetProfile {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).targetProfile = .exact1D_v1 := by
  simp [ofCheckedWithin, Artifact.ofCheckedWithin]

theorem ofCheckedWithin_sourceGuarantee {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).sourceGuarantee = .exact := by
  simp [ofCheckedWithin, Artifact.ofCheckedWithin]

theorem ofCheckedWithin_rootClassName {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).root.className = { serial := 0 } :=
  rfl

theorem ofCheckedWithin_rootKind {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).root.kind = checked.layout.kind :=
  rfl

theorem ofCheckedWithin_rootBox {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).root.box = checked.evaluate.box :=
  rfl

theorem ofCheckedWithin_rootExtent {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).root.extent = checked.extent := by
  simpa [NodeExpectation.extent, ofCheckedWithin, CheckedWithin.evaluate,
    CheckedWithin.extent, CheckedLayout.evaluate] using
    CheckedLayout.evaluateAt_boxExtent checked.layout Origin.zero

theorem ofCheckedWithin_rootSize {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).root.size = Size.ofExtent checked.extent := by
  simpa [NodeExpectation.size, ofCheckedWithin, CheckedWithin.extent] using
    Style.ofCheckedLayout_size checked.layout

theorem ofCheckedWithin_rootSize_eq_rootExtent {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).root.size =
      Size.ofExtent (ofCheckedWithin checked).root.extent := by
  rw [ofCheckedWithin_rootExtent, ofCheckedWithin_rootSize]

theorem ofCheckedWithin_labels_eq_ruleClassNames {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).labels =
      (ofArtifact (Artifact.ofCheckedWithin checked)).ruleClassNames := by
  have hLen := checked_sourceNodes_length_eq_rules_length checked
  simpa [ofCheckedWithin, DocumentExpectation.labels, ofArtifact, ofNode,
    Document.ruleClassNames, Stylesheet.classNames, ClassRule.classNames] using
    stitchExpectations_labels (rules := (lowerNode 0 (Artifact.ofCheckedWithin checked).root).rules)
      (sources := sourceNodesAt Origin.zero checked.layout) hLen.symm

theorem ofCheckedWithin_labels_eq_classReferences {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).labels =
      (ofArtifact (Artifact.ofCheckedWithin checked)).classReferences := by
  rw [ofCheckedWithin_labels_eq_ruleClassNames checked]
  exact (Document.ofArtifact_classReferences_eq_ruleClassNames
    (Artifact.ofCheckedWithin checked)).symm

theorem ofCheckedWithin_labelsNodup {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).labels.Nodup := by
  rw [ofCheckedWithin_labels_eq_ruleClassNames checked]
  exact Document.ofArtifact_ruleClassNamesNodup (Artifact.ofCheckedWithin checked)

theorem ofCheckedWithin_nodeCount_eq_ruleCount {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).nodeCount =
      (ofArtifact (Artifact.ofCheckedWithin checked)).stylesheet.rules.length := by
  have hLen := checked_sourceNodes_length_eq_rules_length checked
  simpa [DocumentExpectation.nodeCount, ofCheckedWithin, ofArtifact, ofNode] using
    stitchExpectations_length (rules := (lowerNode 0 (Artifact.ofCheckedWithin checked).root).rules)
      (sources := sourceNodesAt Origin.zero checked.layout) hLen.symm

theorem ofCheckedWithin_styles_eq_ruleStyles {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).styles =
      (ofArtifact (Artifact.ofCheckedWithin checked)).stylesheet.rules.map ClassRule.style := by
  have hLen := checked_sourceNodes_length_eq_rules_length checked
  simpa [DocumentExpectation.styles, ofCheckedWithin, ofArtifact, ofNode] using
    stitchExpectations_styles (rules := (lowerNode 0 (Artifact.ofCheckedWithin checked).root).rules)
      (sources := sourceNodesAt Origin.zero checked.layout) hLen.symm

theorem ofCheckedWithin_sizes_eq_ruleSizes {available : AvailableSpace}
    (checked : CheckedWithin available) :
    (ofCheckedWithin checked).sizes =
      (ofArtifact (Artifact.ofCheckedWithin checked)).stylesheet.rules.map
        (fun rule => rule.style.size) := by
  calc
    (ofCheckedWithin checked).sizes = (ofCheckedWithin checked).styles.map Style.size := by
      simp [DocumentExpectation.sizes, DocumentExpectation.styles, NodeExpectation.size, List.map_map]
    _ = ((ofArtifact (Artifact.ofCheckedWithin checked)).stylesheet.rules.map ClassRule.style).map Style.size := by
      rw [ofCheckedWithin_styles_eq_ruleStyles]
    _ = (ofArtifact (Artifact.ofCheckedWithin checked)).stylesheet.rules.map
          (fun rule => rule.style.size) := by
      simp [List.map_map]

end Fidelity

end ExactDocument

namespace Node

/-- Render-free lowering of a backend node into the typed exact document IR. -/
def document (node : Node) : ExactDocument.Document :=
  ExactDocument.ofNode node

end Node

namespace Artifact

/-- Render-free lowering of a backend artifact into the typed exact document IR. -/
def document (artifact : Artifact) : ExactDocument.Document :=
  ExactDocument.ofArtifact artifact

theorem document_eq_ofNode (artifact : Artifact) :
    artifact.document = artifact.root.document :=
  rfl

end Artifact

def checkWithinArtifact (available : AvailableSpace) (layout : Layout) :
    CheckResult Artifact :=
  (checkWithinCertified available layout).map Artifact.ofCertifiedWithin

def checkArtifact (available : AvailableSpace) (layout : Layout) :
    CheckResult Artifact :=
  (checkCertified available layout).map Artifact.ofCertifiedWithin

theorem checkWithinArtifact_exact_certified
    {available : AvailableSpace}
    {layout : Layout}
    {artifact : Artifact}
    (h : checkWithinArtifact available layout = .exact artifact) :
    ∃ certified : CertifiedWithin available,
      Artifact.ofCertifiedWithin certified = artifact := by
  unfold checkWithinArtifact at h
  cases hCheck : checkWithinCertified available layout with
  | incompatible error =>
      simp [CheckResult.map, hCheck] at h
  | exact certified =>
      refine ⟨certified, ?_⟩
      simpa [CheckResult.map, hCheck] using h

theorem checkWithinArtifact_exact_checked
    {available : AvailableSpace}
    {layout : Layout}
    {artifact : Artifact}
    (h : checkWithinArtifact available layout = .exact artifact) :
    ∃ checked : CheckedWithin available,
      Artifact.ofCheckedWithin checked = artifact := by
  rcases checkWithinArtifact_exact_certified h with ⟨certified, hArtifact⟩
  refine ⟨certified.checked, ?_⟩
  rw [← Artifact.ofCertifiedWithin_eq_ofCheckedWithin certified]
  exact hArtifact

theorem checkWithinArtifact_exact_targetProfile
    {available : AvailableSpace}
    {layout : Layout}
    {artifact : Artifact}
    (h : checkWithinArtifact available layout = .exact artifact) :
    artifact.targetProfile = .exact1D_v1 := by
  rcases checkWithinArtifact_exact_certified h with ⟨certified, hArtifact⟩
  cases hArtifact
  exact Artifact.ofCertifiedWithin_targetProfile certified

theorem checkWithinArtifact_exact_sourceGuarantee
    {available : AvailableSpace}
    {layout : Layout}
    {artifact : Artifact}
    (h : checkWithinArtifact available layout = .exact artifact) :
    artifact.sourceGuarantee = .exact := by
  rcases checkWithinArtifact_exact_certified h with ⟨certified, hArtifact⟩
  rw [← hArtifact]
  exact Artifact.ofCertifiedWithin_sourceGuarantee_exact certified

theorem checkWithinArtifact_exact_outputBounds_within_inputBounds
    {available : AvailableSpace}
    {layout : Layout}
    {artifact : Artifact}
    (h : checkWithinArtifact available layout = .exact artifact) :
    artifact.inputBounds.containsBounds artifact.outputBounds := by
  rcases checkWithinArtifact_exact_certified h with ⟨certified, hArtifact⟩
  rw [← hArtifact]
  exact Artifact.ofCertifiedWithin_outputBounds_within_inputBounds certified

theorem checkWithinArtifact_exact_root_kind
    {available : AvailableSpace}
    {layout : Layout}
    {artifact : Artifact}
    (h : checkWithinArtifact available layout = .exact artifact) :
    ∃ checked : CheckedWithin available,
      Artifact.ofCheckedWithin checked = artifact ∧ artifact.root.kind = checked.layout.kind := by
  rcases checkWithinArtifact_exact_checked h with ⟨checked, hArtifact⟩
  refine ⟨checked, hArtifact, ?_⟩
  rw [← hArtifact]
  exact Artifact.ofCheckedWithin_root_kind checked

theorem checkWithinArtifact_exact_root_size
    {available : AvailableSpace}
    {layout : Layout}
    {artifact : Artifact}
    (h : checkWithinArtifact available layout = .exact artifact) :
    ∃ checked : CheckedWithin available,
      Artifact.ofCheckedWithin checked = artifact ∧
      artifact.root.style.size = Size.ofExtent checked.extent := by
  rcases checkWithinArtifact_exact_checked h with ⟨checked, hArtifact⟩
  refine ⟨checked, hArtifact, ?_⟩
  rw [← hArtifact]
  exact Artifact.ofCheckedWithin_root_size checked

theorem checkArtifact_exact_certified
    {available : AvailableSpace}
    {layout : Layout}
    {artifact : Artifact}
    (h : checkArtifact available layout = .exact artifact) :
    ∃ certified : CertifiedWithin available,
      Artifact.ofCertifiedWithin certified = artifact := by
  unfold checkArtifact at h
  cases hCheck : checkCertified available layout with
  | incompatible error =>
      simp [CheckResult.map, hCheck] at h
  | exact certified =>
      refine ⟨certified, ?_⟩
      simpa [CheckResult.map, hCheck] using h

theorem checkArtifact_exact_checked
    {available : AvailableSpace}
    {layout : Layout}
    {artifact : Artifact}
    (h : checkArtifact available layout = .exact artifact) :
    ∃ checked : CheckedWithin available,
      Artifact.ofCheckedWithin checked = artifact := by
  rcases checkArtifact_exact_certified h with ⟨certified, hArtifact⟩
  refine ⟨certified.checked, ?_⟩
  rw [← Artifact.ofCertifiedWithin_eq_ofCheckedWithin certified]
  exact hArtifact

theorem checkArtifact_exact_targetProfile
    {available : AvailableSpace}
    {layout : Layout}
    {artifact : Artifact}
    (h : checkArtifact available layout = .exact artifact) :
    artifact.targetProfile = .exact1D_v1 := by
  rcases checkArtifact_exact_certified h with ⟨certified, hArtifact⟩
  cases hArtifact
  exact Artifact.ofCertifiedWithin_targetProfile certified

theorem checkArtifact_exact_sourceGuarantee
    {available : AvailableSpace}
    {layout : Layout}
    {artifact : Artifact}
    (h : checkArtifact available layout = .exact artifact) :
    artifact.sourceGuarantee = .exact := by
  rcases checkArtifact_exact_certified h with ⟨certified, hArtifact⟩
  rw [← hArtifact]
  exact Artifact.ofCertifiedWithin_sourceGuarantee_exact certified

theorem checkArtifact_exact_outputBounds_within_inputBounds
    {available : AvailableSpace}
    {layout : Layout}
    {artifact : Artifact}
    (h : checkArtifact available layout = .exact artifact) :
    artifact.inputBounds.containsBounds artifact.outputBounds := by
  rcases checkArtifact_exact_certified h with ⟨certified, hArtifact⟩
  rw [← hArtifact]
  exact Artifact.ofCertifiedWithin_outputBounds_within_inputBounds certified

theorem checkArtifact_exact_root_kind
    {available : AvailableSpace}
    {layout : Layout}
    {artifact : Artifact}
    (h : checkArtifact available layout = .exact artifact) :
    ∃ checked : CheckedWithin available,
      Artifact.ofCheckedWithin checked = artifact ∧ artifact.root.kind = checked.layout.kind := by
  rcases checkArtifact_exact_checked h with ⟨checked, hArtifact⟩
  refine ⟨checked, hArtifact, ?_⟩
  rw [← hArtifact]
  exact Artifact.ofCheckedWithin_root_kind checked

theorem checkArtifact_exact_root_size
    {available : AvailableSpace}
    {layout : Layout}
    {artifact : Artifact}
    (h : checkArtifact available layout = .exact artifact) :
    ∃ checked : CheckedWithin available,
      Artifact.ofCheckedWithin checked = artifact ∧
      artifact.root.style.size = Size.ofExtent checked.extent := by
  rcases checkArtifact_exact_checked h with ⟨checked, hArtifact⟩
  refine ⟨checked, hArtifact, ?_⟩
  rw [← hArtifact]
  exact Artifact.ofCheckedWithin_root_size checked

end TypedLayout.Backend.ExactCss
