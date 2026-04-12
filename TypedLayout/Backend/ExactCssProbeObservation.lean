import TypedLayout.Backend.ExactCssProbePlan

namespace TypedLayout.Backend.ExactCss

open TypedLayout.Core

namespace ExactDocument
namespace ProbeObservation

/-- Typed observed box payload for the exact browser-probe fragment. -/
structure ObservedBox where
  origin : Origin
  extent : ExactExtent
  deriving DecidableEq, Repr

namespace ObservedBox

def ofSourceBox (box : Box) : ObservedBox :=
  { origin := box.origin
  , extent := box.extent
  }

def toSourceBox (box : ObservedBox) : Box :=
  { origin := box.origin
  , extent := box.extent
  }

@[simp] theorem ofSourceBox_origin (box : Box) :
    (ofSourceBox box).origin = box.origin :=
  rfl

@[simp] theorem ofSourceBox_extent (box : Box) :
    (ofSourceBox box).extent = box.extent :=
  rfl

@[simp] theorem toSourceBox_ofSourceBox (box : Box) :
    (ofSourceBox box).toSourceBox = box :=
  rfl

end ObservedBox

/-- Selected observed style fields for the current exact browser-probe fragment.

The observed slice intentionally mirrors the exact backend style fragment without
introducing untyped computed-style strings. -/
structure ObservedStyle where
  boxSizing : BoxSizing
  size : Size
  padding : Padding
  display : Display
  flexItem : FlexItem
  deriving DecidableEq, Repr

namespace ObservedStyle

def ofBackendStyle (style : Style) : ObservedStyle :=
  { boxSizing := style.boxSizing
  , size := style.size
  , padding := style.padding
  , display := style.display
  , flexItem := style.flexItem
  }

def toBackendStyle (style : ObservedStyle) : Style :=
  { boxSizing := style.boxSizing
  , size := style.size
  , padding := style.padding
  , display := style.display
  , flexItem := style.flexItem
  }

@[simp] theorem ofBackendStyle_boxSizing (style : Style) :
    (ofBackendStyle style).boxSizing = style.boxSizing :=
  rfl

@[simp] theorem ofBackendStyle_size (style : Style) :
    (ofBackendStyle style).size = style.size :=
  rfl

@[simp] theorem ofBackendStyle_padding (style : Style) :
    (ofBackendStyle style).padding = style.padding :=
  rfl

@[simp] theorem ofBackendStyle_display (style : Style) :
    (ofBackendStyle style).display = style.display :=
  rfl

@[simp] theorem ofBackendStyle_flexItem (style : Style) :
    (ofBackendStyle style).flexItem = style.flexItem :=
  rfl

@[simp] theorem toBackendStyle_ofBackendStyle (style : Style) :
    (ofBackendStyle style).toBackendStyle = style :=
  rfl

end ObservedStyle

/-- Typed observed payload for one exact probe target.

This stays intentionally ordered with the probe plan. The current layer does not
yet define any selector-lookup or browser-automation protocol. -/
structure Target where
  selector : ProbePlan.Selector
  box : ObservedBox
  style : ObservedStyle
  deriving DecidableEq, Repr

namespace Target

def className (target : Target) : ClassName :=
  target.selector.className

def selectorText (target : Target) : String :=
  target.selector.text

def origin (target : Target) : Origin :=
  target.box.origin

def extent (target : Target) : ExactExtent :=
  target.box.extent

def size (target : Target) : Size :=
  target.style.size

def sourceBox (target : Target) : Box :=
  target.box.toSourceBox

def backendStyle (target : Target) : Style :=
  target.style.toBackendStyle

/-- Exact matching observation derived from a probe-plan target. -/
def ofProbeTarget (target : ProbePlan.Target) : Target :=
  { selector := target.selector
  , box := ObservedBox.ofSourceBox target.sourceBox
  , style := ObservedStyle.ofBackendStyle target.backendStyle
  }

@[simp] theorem ofProbeTarget_selector (target : ProbePlan.Target) :
    (ofProbeTarget target).selector = target.selector :=
  rfl

@[simp] theorem ofProbeTarget_box (target : ProbePlan.Target) :
    (ofProbeTarget target).box = ObservedBox.ofSourceBox target.sourceBox :=
  rfl

@[simp] theorem ofProbeTarget_style (target : ProbePlan.Target) :
    (ofProbeTarget target).style = ObservedStyle.ofBackendStyle target.backendStyle :=
  rfl

@[simp] theorem ofProbeTarget_className (target : ProbePlan.Target) :
    (ofProbeTarget target).className = target.className :=
  rfl

@[simp] theorem ofProbeTarget_selectorText (target : ProbePlan.Target) :
    (ofProbeTarget target).selectorText = target.selectorText :=
  rfl

@[simp] theorem ofProbeTarget_origin (target : ProbePlan.Target) :
    (ofProbeTarget target).origin = target.origin :=
  rfl

@[simp] theorem ofProbeTarget_extent (target : ProbePlan.Target) :
    (ofProbeTarget target).extent = target.extent :=
  rfl

@[simp] theorem ofProbeTarget_size (target : ProbePlan.Target) :
    (ofProbeTarget target).size = target.size :=
  rfl

@[simp] theorem ofProbeTarget_sourceBox (target : ProbePlan.Target) :
    (ofProbeTarget target).sourceBox = target.sourceBox :=
  rfl

@[simp] theorem ofProbeTarget_backendStyle (target : ProbePlan.Target) :
    (ofProbeTarget target).backendStyle = target.backendStyle :=
  rfl

end Target

/-- Ordered exact-fragment browser observation document.

The target list is intentionally kept in probe-plan order for now, so the
comparison layer can stay typed without deciding harness lookup semantics early.
-/
structure Document where
  targets : List Target
  deriving DecidableEq, Repr

namespace Document

def nodeCount (document : Document) : Nat :=
  document.targets.length

def selectors (document : Document) : List ProbePlan.Selector :=
  document.targets.map Target.selector

def labels (document : Document) : List ClassName :=
  document.targets.map Target.className

def boxes (document : Document) : List ObservedBox :=
  document.targets.map Target.box

def origins (document : Document) : List Origin :=
  document.targets.map Target.origin

def extents (document : Document) : List ExactExtent :=
  document.targets.map Target.extent

def sourceBoxes (document : Document) : List Box :=
  document.targets.map Target.sourceBox

def styles (document : Document) : List ObservedStyle :=
  document.targets.map Target.style

def sizes (document : Document) : List Size :=
  document.targets.map Target.size

def backendStyles (document : Document) : List Style :=
  document.targets.map Target.backendStyle

def selectorTexts (document : Document) : List String :=
  document.targets.map Target.selectorText

theorem labels_length (document : Document) :
    document.labels.length = document.nodeCount := by
  simp [labels, nodeCount]

theorem sourceBoxes_length (document : Document) :
    document.sourceBoxes.length = document.nodeCount := by
  simp [sourceBoxes, nodeCount]

theorem backendStyles_length (document : Document) :
    document.backendStyles.length = document.nodeCount := by
  simp [backendStyles, nodeCount]

theorem sizes_length (document : Document) :
    document.sizes.length = document.nodeCount := by
  simp [sizes, nodeCount]

theorem selectorTexts_length (document : Document) :
    document.selectorTexts.length = document.nodeCount := by
  simp [selectorTexts, nodeCount]

/-- Exact matching observation corpus derived from a probe plan. -/
def ofPlan (plan : ProbePlan.Plan) : Document :=
  { targets := plan.targets.map Target.ofProbeTarget }

theorem ofPlan_nodeCount (plan : ProbePlan.Plan) :
    (ofPlan plan).nodeCount = plan.nodeCount := by
  simp [ofPlan, nodeCount, ProbePlan.Plan.nodeCount]

theorem ofPlan_labels (plan : ProbePlan.Plan) :
    (ofPlan plan).labels = plan.labels := by
  simp [ofPlan, labels, ProbePlan.Plan.labels, List.map_map]

theorem ofPlan_sourceBoxes (plan : ProbePlan.Plan) :
    (ofPlan plan).sourceBoxes = plan.boxes := by
  simp [ofPlan, sourceBoxes, ProbePlan.Plan.boxes, List.map_map]

theorem ofPlan_backendStyles (plan : ProbePlan.Plan) :
    (ofPlan plan).backendStyles = plan.styles := by
  simp [ofPlan, backendStyles, ProbePlan.Plan.styles, List.map_map]

theorem ofPlan_sizes (plan : ProbePlan.Plan) :
    (ofPlan plan).sizes = plan.sizes := by
  simp [ofPlan, sizes, ProbePlan.Plan.sizes, List.map_map]

theorem ofPlan_selectorTexts (plan : ProbePlan.Plan) :
    (ofPlan plan).selectorTexts = plan.selectorTexts := by
  simp [ofPlan, selectorTexts, ProbePlan.Plan.selectorTexts, List.map_map]

end Document

end ProbeObservation

namespace ProbeComparison

/-- Typed equality-style comparison for one exact observed field. -/
inductive ValueComparison (α : Type u) where
  | same
  | different (expected : α) (observed : α)
  deriving DecidableEq, Repr

namespace ValueComparison

def isMatch : ValueComparison α → Bool
  | .same => true
  | .different _ _ => false

def ofValues [DecidableEq α] (expected observed : α) : ValueComparison α :=
  if expected = observed then .same else .different expected observed

@[simp] theorem matches_same :
    (ValueComparison.same : ValueComparison α).isMatch = true :=
  rfl

@[simp] theorem matches_different (expected observed : α) :
    (ValueComparison.different expected observed).isMatch = false :=
  rfl

@[simp] theorem ofValues_self [DecidableEq α] (value : α) :
    ofValues value value = .same := by
  simp [ofValues]

@[simp] theorem ofValues_isMatch_self [DecidableEq α] (value : α) :
    (ofValues value value).isMatch = true := by
  simp [ofValues]

theorem ofValues_isMatch_eq_true_iff [DecidableEq α] (expected observed : α) :
    (ofValues expected observed).isMatch = true ↔ expected = observed := by
  by_cases h : expected = observed
  · simp [ofValues, h, isMatch]
  · simp [ofValues, h, isMatch]

end ValueComparison

/-- Typed comparison between an expected source box and an observed exact box. -/
structure BoxComparison where
  origin : ValueComparison Origin
  extent : ValueComparison ExactExtent
  deriving DecidableEq, Repr

namespace BoxComparison

def isMatch (comparison : BoxComparison) : Bool :=
  comparison.origin.isMatch && comparison.extent.isMatch

def compare (expected : Box) (observed : ProbeObservation.ObservedBox) : BoxComparison :=
  { origin := ValueComparison.ofValues expected.origin observed.origin
  , extent := ValueComparison.ofValues expected.extent observed.extent
  }

theorem compare_ofSourceBox_isMatch (box : Box) :
    (compare box (ProbeObservation.ObservedBox.ofSourceBox box)).isMatch = true := by
  simp [compare, isMatch]

end BoxComparison

/-- Typed comparison between an expected backend style and an observed style slice. -/
structure StyleComparison where
  boxSizing : ValueComparison BoxSizing
  size : ValueComparison Size
  padding : ValueComparison Padding
  display : ValueComparison Display
  flexItem : ValueComparison FlexItem
  deriving DecidableEq, Repr

namespace StyleComparison

def isMatch (comparison : StyleComparison) : Bool :=
  comparison.boxSizing.isMatch &&
    comparison.size.isMatch &&
    comparison.padding.isMatch &&
    comparison.display.isMatch &&
    comparison.flexItem.isMatch

def compare (expected : Style) (observed : ProbeObservation.ObservedStyle) : StyleComparison :=
  { boxSizing := ValueComparison.ofValues expected.boxSizing observed.boxSizing
  , size := ValueComparison.ofValues expected.size observed.size
  , padding := ValueComparison.ofValues expected.padding observed.padding
  , display := ValueComparison.ofValues expected.display observed.display
  , flexItem := ValueComparison.ofValues expected.flexItem observed.flexItem
  }

theorem compare_ofBackendStyle_isMatch (style : Style) :
    (compare style (ProbeObservation.ObservedStyle.ofBackendStyle style)).isMatch = true := by
  simp [compare, isMatch]

end StyleComparison

/-- Typed comparison between one expected probe target and one observed target. -/
structure TargetComparison where
  expected : ProbePlan.Target
  observed : ProbeObservation.Target
  selector : ValueComparison ProbePlan.Selector
  box : BoxComparison
  style : StyleComparison
  deriving DecidableEq, Repr

namespace TargetComparison

def isMatch (comparison : TargetComparison) : Bool :=
  comparison.selector.isMatch && comparison.box.isMatch && comparison.style.isMatch

def compare
    (expected : ProbePlan.Target)
    (observed : ProbeObservation.Target) : TargetComparison :=
  { expected := expected
  , observed := observed
  , selector := ValueComparison.ofValues expected.selector observed.selector
  , box := BoxComparison.compare expected.sourceBox observed.box
  , style := StyleComparison.compare expected.backendStyle observed.style
  }

theorem compare_ofProbeTarget_isMatch (target : ProbePlan.Target) :
    (compare target (ProbeObservation.Target.ofProbeTarget target)).isMatch = true := by
  simp [compare, isMatch]
  constructor
  · exact BoxComparison.compare_ofSourceBox_isMatch target.sourceBox
  · exact StyleComparison.compare_ofBackendStyle_isMatch target.backendStyle

end TargetComparison

/-- Positional comparison result for one probe target slot. -/
inductive TargetResult where
  | paired (comparison : TargetComparison)
  | missingObservation (expected : ProbePlan.Target)
  | unexpectedObservation (observed : ProbeObservation.Target)
  deriving DecidableEq, Repr

namespace TargetResult

def isMatch : TargetResult → Bool
  | .paired comparison => comparison.isMatch
  | .missingObservation _ => false
  | .unexpectedObservation _ => false

@[simp] theorem paired_isMatch (comparison : TargetComparison) :
    (TargetResult.paired comparison).isMatch = comparison.isMatch :=
  rfl

end TargetResult

/-- Typed comparison bundle between an exact probe plan and an ordered observed corpus. -/
structure DocumentComparison where
  targetProfile : BlessedCssProfile
  sourceGuarantee : GuaranteeClass
  expectedCount : Nat
  observedCount : Nat
  results : List TargetResult
  deriving DecidableEq, Repr

namespace DocumentComparison

private def compareTargets : List ProbePlan.Target → List ProbeObservation.Target → List TargetResult
  | [], [] => []
  | expected :: expecteds, observed :: observeds =>
      .paired (TargetComparison.compare expected observed) :: compareTargets expecteds observeds
  | expected :: expecteds, [] =>
      .missingObservation expected :: compareTargets expecteds []
  | [], observed :: observeds =>
      .unexpectedObservation observed :: compareTargets [] observeds

def resultCount (comparison : DocumentComparison) : Nat :=
  comparison.results.length

def targetCountMatches (comparison : DocumentComparison) : Bool :=
  decide (comparison.expectedCount = comparison.observedCount)

def allTargetsMatch (comparison : DocumentComparison) : Bool :=
  comparison.results.all TargetResult.isMatch

def matchesExactly (comparison : DocumentComparison) : Bool :=
  comparison.targetCountMatches && comparison.allTargetsMatch

def compare
    (plan : ProbePlan.Plan)
    (observed : ProbeObservation.Document) : DocumentComparison :=
  { targetProfile := plan.targetProfile
  , sourceGuarantee := plan.sourceGuarantee
  , expectedCount := plan.nodeCount
  , observedCount := observed.nodeCount
  , results := compareTargets plan.targets observed.targets
  }

private theorem compareTargets_ofProbeTargets_length :
    ∀ targets : List ProbePlan.Target,
      (compareTargets targets (targets.map ProbeObservation.Target.ofProbeTarget)).length =
        targets.length
  | [] => by
      simp [compareTargets]
  | target :: targets => by
      simp [compareTargets, compareTargets_ofProbeTargets_length]

private theorem compareTargets_ofProbeTargets_allTargetsMatched :
    ∀ targets : List ProbePlan.Target,
      (compareTargets targets (targets.map ProbeObservation.Target.ofProbeTarget)).all
        TargetResult.isMatch = true
  | [] => by
      simp [compareTargets]
  | target :: targets => by
      simp [compareTargets, TargetComparison.compare_ofProbeTarget_isMatch,
        compareTargets_ofProbeTargets_allTargetsMatched]

theorem compare_targetProfile (plan : ProbePlan.Plan) (observed : ProbeObservation.Document) :
    (compare plan observed).targetProfile = plan.targetProfile :=
  rfl

theorem compare_sourceGuarantee (plan : ProbePlan.Plan) (observed : ProbeObservation.Document) :
    (compare plan observed).sourceGuarantee = plan.sourceGuarantee :=
  rfl

theorem compare_expectedCount (plan : ProbePlan.Plan) (observed : ProbeObservation.Document) :
    (compare plan observed).expectedCount = plan.nodeCount :=
  rfl

theorem compare_observedCount (plan : ProbePlan.Plan) (observed : ProbeObservation.Document) :
    (compare plan observed).observedCount = observed.nodeCount :=
  rfl

theorem compare_ofPlan_resultCount (plan : ProbePlan.Plan) :
    (compare plan (ProbeObservation.Document.ofPlan plan)).resultCount = plan.nodeCount := by
  simpa [compare, resultCount, ProbeObservation.Document.ofPlan, ProbePlan.Plan.nodeCount] using
    compareTargets_ofProbeTargets_length plan.targets

theorem compare_ofPlan_targetCountMatches (plan : ProbePlan.Plan) :
    (compare plan (ProbeObservation.Document.ofPlan plan)).targetCountMatches = true := by
  simp [compare, targetCountMatches, ProbeObservation.Document.ofPlan,
    ProbeObservation.Document.nodeCount, ProbePlan.Plan.nodeCount]

theorem compare_ofPlan_allTargetsMatch (plan : ProbePlan.Plan) :
    (compare plan (ProbeObservation.Document.ofPlan plan)).allTargetsMatch = true := by
  simpa [compare, allTargetsMatch, ProbeObservation.Document.ofPlan] using
    compareTargets_ofProbeTargets_allTargetsMatched plan.targets

theorem compare_ofPlan_matchesExactly (plan : ProbePlan.Plan) :
    (compare plan (ProbeObservation.Document.ofPlan plan)).matchesExactly = true := by
  simp [matchesExactly, compare_ofPlan_targetCountMatches, compare_ofPlan_allTargetsMatch]

end DocumentComparison

end ProbeComparison
end ExactDocument
end TypedLayout.Backend.ExactCss
