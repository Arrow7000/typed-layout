import TypedLayout.Core.Properties

namespace TypedLayout.Core

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

theorem fits {available : AvailableSpace} (certified : CertifiedWithin available) :
    certified.layout.extent.fitsWithin available.extent :=
  certified.checked.fits

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
