import TypedLayout.Core.Certified

namespace TypedLayout.Core

/--
Public exact-fragment local invariants currently exposed by checked layouts.
-/
inductive ExactLocalInvariant where
  | immediateChildrenFitWithin
  | adjacentChildrenSeparated (axis : Axis) (gap : Gap)
  | frameChildFitsWithin
  deriving DecidableEq, Repr

namespace ExactLocalInvariant

/--
Interpret a public exact-fragment local invariant as the existing proposition it
asserts about a checked layout.
-/
def Holds : ExactLocalInvariant → CheckedLayout → Prop
  | .immediateChildrenFitWithin, layout =>
      ImmediateChildrenFitWithin layout.evaluate
  | .adjacentChildrenSeparated axis gap, layout =>
      AdjacentSeparatedAlong axis gap layout.evaluate.children
  | .frameChildFitsWithin, .frame extent child =>
      child.extent.fitsWithin extent
  | .frameChildFitsWithin, _ =>
      False

end ExactLocalInvariant

/--
Minimal public exact-fragment summary for a checked layout.

For now this stays deliberately modest: exact extent, exact guarantee class, the
currently exposed local invariants, and recursive child summaries.
-/
structure ExactLayoutSummary where
  kind : LayoutKind
  extent : ExactExtent
  guarantee : GuaranteeClass
  localInvariants : List ExactLocalInvariant
  children : List ExactLayoutSummary
  deriving Repr

namespace ExactLayoutSummary

def extentBounds (summary : ExactLayoutSummary) : ExtentBounds :=
  summary.extent.toBounds

def ofCheckedLayout : CheckedLayout → ExactLayoutSummary
  | .leaf extent =>
      { kind := .leaf
      , extent := extent
      , guarantee := .exact
      , localInvariants := []
      , children := []
      }
  | .row gap children =>
      { kind := .row
      , extent := ExactExtent.stack .horizontal gap (children.map CheckedLayout.extent)
      , guarantee := .exact
      , localInvariants :=
          [ .immediateChildrenFitWithin
          , .adjacentChildrenSeparated .horizontal gap
          ]
      , children := children.map ofCheckedLayout
      }
  | .column gap children =>
      { kind := .column
      , extent := ExactExtent.stack .vertical gap (children.map CheckedLayout.extent)
      , guarantee := .exact
      , localInvariants :=
          [ .immediateChildrenFitWithin
          , .adjacentChildrenSeparated .vertical gap
          ]
      , children := children.map ofCheckedLayout
      }
  | .padding insets child =>
      { kind := .padding
      , extent := child.extent.expand insets
      , guarantee := .exact
      , localInvariants := [ .immediateChildrenFitWithin ]
      , children := [ ofCheckedLayout child ]
      }
  | .frame extent child =>
      { kind := .frame
      , extent := extent
      , guarantee := .exact
      , localInvariants :=
          [ .frameChildFitsWithin
          , .immediateChildrenFitWithin
          ]
      , children := [ ofCheckedLayout child ]
      }

def ofCheckedWithin {available : AvailableSpace}
    (checked : CheckedWithin available) : ExactLayoutSummary :=
  ofCheckedLayout checked.layout

def ofCertifiedWithin {available : AvailableSpace}
    (certified : CertifiedWithin available) : ExactLayoutSummary :=
  ofCheckedLayout certified.layout

theorem ofCheckedLayout_kind (layout : CheckedLayout) :
    (ofCheckedLayout layout).kind = layout.kind := by
  cases layout <;> simp [ofCheckedLayout, CheckedLayout.kind]

theorem ofCheckedLayout_extent (layout : CheckedLayout) :
    (ofCheckedLayout layout).extent = layout.extent := by
  cases layout <;> simp [ofCheckedLayout, CheckedLayout.extent]

theorem ofCheckedLayout_extentBounds (layout : CheckedLayout) :
    (ofCheckedLayout layout).extentBounds = layout.extent.toBounds := by
  simp [extentBounds, ofCheckedLayout_extent]

theorem ofCheckedLayout_guarantee (layout : CheckedLayout) :
    (ofCheckedLayout layout).guarantee = .exact := by
  cases layout <;> simp [ofCheckedLayout]

theorem invariant_mem_holds_of_localSound :
    ∀ {layout : CheckedLayout} (_ : CheckedLayout.LocalSound layout)
      {invariant : ExactLocalInvariant},
      invariant ∈ (ofCheckedLayout layout).localInvariants →
        invariant.Holds layout
  | .leaf _, _, _, hMem => by
      simp [ofCheckedLayout] at hMem
  | .row gap children, hSound, invariant, hMem => by
      rcases hSound with ⟨hWithin, hAdjacent, _⟩
      simp [ofCheckedLayout] at hMem
      cases hMem with
      | inl hEqual =>
          cases hEqual
          simpa [ExactLocalInvariant.Holds] using hWithin
      | inr hEqual =>
          cases hEqual
          simpa [ExactLocalInvariant.Holds] using hAdjacent
  | .column gap children, hSound, invariant, hMem => by
      rcases hSound with ⟨hWithin, hAdjacent, _⟩
      simp [ofCheckedLayout] at hMem
      cases hMem with
      | inl hEqual =>
          cases hEqual
          simpa [ExactLocalInvariant.Holds] using hWithin
      | inr hEqual =>
          cases hEqual
          simpa [ExactLocalInvariant.Holds] using hAdjacent
  | .padding _ child, hSound, invariant, hMem => by
      rcases hSound with ⟨hWithin, _⟩
      simp [ofCheckedLayout] at hMem
      cases hMem
      simpa [ExactLocalInvariant.Holds] using hWithin
  | .frame extent child, hSound, invariant, hMem => by
      rcases hSound with ⟨hFit, hWithin, _⟩
      simp [ofCheckedLayout] at hMem
      cases hMem with
      | inl hEqual =>
          cases hEqual
          simpa [ExactLocalInvariant.Holds] using hFit
      | inr hEqual =>
          cases hEqual
          simpa [ExactLocalInvariant.Holds] using hWithin

theorem invariant_mem_holds_of_certified
    {available : AvailableSpace}
    (certified : CertifiedWithin available)
    {invariant : ExactLocalInvariant}
    (hMem : invariant ∈ (ofCertifiedWithin certified).localInvariants) :
    invariant.Holds certified.layout :=
  invariant_mem_holds_of_localSound certified.localSound hMem

end ExactLayoutSummary

namespace CheckedLayout

def summary (layout : CheckedLayout) : ExactLayoutSummary :=
  ExactLayoutSummary.ofCheckedLayout layout

theorem summary_guarantee (layout : CheckedLayout) :
    layout.summary.guarantee = .exact :=
  ExactLayoutSummary.ofCheckedLayout_guarantee layout

theorem summary_invariant_holds
    {layout : CheckedLayout}
    (hSound : CheckedLayout.LocalSound layout)
    {invariant : ExactLocalInvariant}
    (hMem : invariant ∈ layout.summary.localInvariants) :
    invariant.Holds layout :=
  ExactLayoutSummary.invariant_mem_holds_of_localSound hSound hMem

end CheckedLayout

namespace CertifiedWithin

def summary {available : AvailableSpace}
    (certified : CertifiedWithin available) : ExactLayoutSummary :=
  ExactLayoutSummary.ofCertifiedWithin certified

theorem summary_guarantee {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    certified.summary.guarantee = .exact :=
  ExactLayoutSummary.ofCheckedLayout_guarantee certified.layout

theorem summary_invariant_holds
    {available : AvailableSpace}
    (certified : CertifiedWithin available)
    {invariant : ExactLocalInvariant}
    (hMem : invariant ∈ certified.summary.localInvariants) :
    invariant.Holds certified.layout :=
  ExactLayoutSummary.invariant_mem_holds_of_certified certified hMem

end CertifiedWithin

end TypedLayout.Core
