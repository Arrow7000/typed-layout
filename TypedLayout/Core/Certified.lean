import TypedLayout.Core.Properties

namespace TypedLayout.Core

/--
Purely local proof-carrying wrapper for checked layouts.

Unlike `CertifiedWithin`, this does not mention any ambient available space. It
only packages the current exact-fragment local soundness proposition together
with the executable local witness truth for a checked layout.
-/
structure CertifiedLocalLayout where
  layout : CheckedLayout
  localSound : CheckedLayout.LocalSound layout
  localWitness : layout.localWitness? = true

namespace CertifiedLocalLayout

def kind (certified : CertifiedLocalLayout) : LayoutKind :=
  certified.layout.kind

def extent (certified : CertifiedLocalLayout) : ExactExtent :=
  certified.layout.extent

def extentBounds (certified : CertifiedLocalLayout) : ExtentBounds :=
  certified.extent.toBounds

def ofLocalSound
    (layout : CheckedLayout)
    (localSound : CheckedLayout.LocalSound layout) : CertifiedLocalLayout :=
  { layout := layout
  , localSound := localSound
  , localWitness := CheckedLayout.localWitness?_complete layout localSound
  }

def ofWitness
    (layout : CheckedLayout)
    (localWitness : layout.localWitness? = true) : CertifiedLocalLayout :=
  { layout := layout
  , localSound := CheckedLayout.localWitness?_sound layout localWitness
  , localWitness := localWitness
  }

def ofCheckedWithin
    {available : AvailableSpace}
    (checked : CheckedWithin available)
    (localSound : CheckedLayout.LocalSound checked.layout) : CertifiedLocalLayout :=
  ofLocalSound checked.layout localSound

def ofLocalSounds :
    ∀ (children : List CheckedLayout),
      CheckedLayout.LocalSounds children → List CertifiedLocalLayout
  | [], _ => []
  | child :: rest, hChildren => by
      rcases hChildren with ⟨hChild, hRest⟩
      exact ofLocalSound child hChild :: ofLocalSounds rest hRest

def children : CertifiedLocalLayout → List CertifiedLocalLayout
  | ⟨.leaf _, _, _⟩ => []
  | ⟨.row _ rawChildren, hSound, _⟩ =>
      ofLocalSounds rawChildren hSound.2.2
  | ⟨.column _ rawChildren, hSound, _⟩ =>
      ofLocalSounds rawChildren hSound.2.2
  | ⟨.padding _ child, hSound, _⟩ =>
      [ofLocalSound child hSound.2]
  | ⟨.frame _ child, hSound, _⟩ =>
      [ofLocalSound child hSound.2.2]

theorem ofLocalSounds_layouts :
    ∀ (children : List CheckedLayout)
      (hChildren : CheckedLayout.LocalSounds children),
      (ofLocalSounds children hChildren).map CertifiedLocalLayout.layout = children
  | [], _ => by
      simp [ofLocalSounds]
  | child :: rest, hChildren => by
      rcases hChildren with ⟨hChild, hRest⟩
      simp [ofLocalSounds, ofLocalSounds_layouts rest hRest, ofLocalSound]

theorem children_layouts (certified : CertifiedLocalLayout) :
    certified.children.map CertifiedLocalLayout.layout =
      match certified.layout with
      | .leaf _ => []
      | .row _ rawChildren => rawChildren
      | .column _ rawChildren => rawChildren
      | .padding _ child => [child]
      | .frame _ child => [child] := by
  cases certified with
  | mk layout hSound hWitness =>
      cases layout with
      | leaf extent =>
          simp [children]
      | row gap rawChildren =>
          simpa [children] using ofLocalSounds_layouts rawChildren hSound.2.2
      | column gap rawChildren =>
          simpa [children] using ofLocalSounds_layouts rawChildren hSound.2.2
      | padding insets child =>
          simp [children, ofLocalSound]
      | frame extent child =>
          simp [children, ofLocalSound]

end CertifiedLocalLayout

/--
Successful exact checks can be re-packaged as a small proof-carrying boundary:
fit-to-available evidence, propositional local soundness, and the executable
local witness truth for the checked layout all travel together.
-/
structure CertifiedWithin (available : AvailableSpace) where
  checked : CheckedWithin available
  localSound : CheckedLayout.LocalSound checked.layout
  localWitness : checked.layout.localWitness? = true

namespace CertifiedWithin

def layout {available : AvailableSpace} (certified : CertifiedWithin available) : CheckedLayout :=
  certified.checked.layout

def extent {available : AvailableSpace} (certified : CertifiedWithin available) : ExactExtent :=
  certified.layout.extent

def extentBounds {available : AvailableSpace} (certified : CertifiedWithin available) : ExtentBounds :=
  certified.extent.toBounds

def toLocal {available : AvailableSpace}
    (certified : CertifiedWithin available) : CertifiedLocalLayout :=
  CertifiedLocalLayout.ofLocalSound certified.layout certified.localSound

theorem fits {available : AvailableSpace} (certified : CertifiedWithin available) :
    certified.layout.extent.fitsWithin available.extent :=
  certified.checked.fits

theorem extentBounds_within_availableBounds {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    available.bounds.containsBounds certified.extentBounds :=
  certified.checked.extentBounds_within_availableBounds

def ofChecked {available : AvailableSpace}
    (checked : CheckedWithin available)
    (localSound : CheckedLayout.LocalSound checked.layout) : CertifiedWithin available :=
  { checked := checked
  , localSound := localSound
  , localWitness := CheckedLayout.localWitness?_complete checked.layout localSound
  }

def ofCheckWithin
    {available : AvailableSpace}
    {layout : Layout}
    {checked : CheckedWithin available}
    (h : checkWithin available layout = .exact checked) : CertifiedWithin available :=
  ofChecked checked <| by
    simpa [h] using (CheckedLayout.checkWithin_localSound available layout)

def ofCheck
    {available : AvailableSpace}
    {layout : Layout}
    {checked : CheckedWithin available}
    (h : check available layout = .exact checked) : CertifiedWithin available :=
  ofChecked checked (CheckedLayout.check_exact_localSound h)

end CertifiedWithin

namespace CertifiedLocalLayout

def ofCertifiedWithin
    {available : AvailableSpace}
    (certified : CertifiedWithin available) : CertifiedLocalLayout :=
  certified.toLocal

end CertifiedLocalLayout

def checkWithinCertified (available : AvailableSpace) (layout : Layout) :
    CheckResult (CertifiedWithin available) :=
  match h : checkWithin available layout with
  | .exact checked => .exact (CertifiedWithin.ofCheckWithin (checked := checked) h)
  | .incompatible error => .incompatible error

def checkCertified (available : AvailableSpace) (layout : Layout) :
    CheckResult (CertifiedWithin available) :=
  match h : check available layout with
  | .exact checked => .exact (CertifiedWithin.ofCheck (checked := checked) h)
  | .incompatible error => .incompatible error

end TypedLayout.Core
