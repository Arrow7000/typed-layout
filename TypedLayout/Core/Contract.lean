import TypedLayout.Core.Summary

namespace TypedLayout.Core

/--
Input-side view for the first exact-fragment contract layer.

This keeps the original exact available space while also exposing the bounded view
that future contract consumers can reason over uniformly.
-/
structure ExactContractInput where
  available : AvailableSpace
  bounds : ExtentBounds
  deriving DecidableEq, Repr

namespace ExactContractInput

def ofAvailable (available : AvailableSpace) : ExactContractInput :=
  { available := available
  , bounds := available.bounds
  }

theorem ofAvailable_bounds (available : AvailableSpace) :
    (ofAvailable available).bounds = available.bounds :=
  rfl

theorem ofAvailable_bounds_contains_available (available : AvailableSpace) :
    (ofAvailable available).bounds.contains available.extent := by
  simpa [ofAvailable, AvailableSpace.bounds] using
    (ExactExtent.fitsWithin_iff_upToBounds_contains).mp
      (show available.extent.fitsWithin available.extent from
        ⟨Nat.le_refl _, Nat.le_refl _⟩)

end ExactContractInput

/--
Output-side view for the first exact-fragment contract layer.

For the current exact fragment this remains an exact extent paired with its
singleton bounded view.
-/
structure ExactContractOutput where
  extent : ExactExtent
  bounds : ExtentBounds
  deriving DecidableEq, Repr

namespace ExactContractOutput

def ofExtent (extent : ExactExtent) : ExactContractOutput :=
  { extent := extent
  , bounds := extent.toBounds
  }

theorem ofExtent_bounds (extent : ExactExtent) :
    (ofExtent extent).bounds = extent.toBounds :=
  rfl

theorem ofExtent_bounds_contains_extent (extent : ExactExtent) :
    (ofExtent extent).bounds.contains extent := by
  simpa [ofExtent] using ExactExtent.toBounds_contains_self extent

end ExactContractOutput

/--
First explicit exact-fragment contract layer over certified exact checks.

This intentionally stays small: explicit input/output views, current guarantee
class, and the public local-invariant inventory already exposed by summaries.
-/
structure ExactLayoutContract where
  kind : LayoutKind
  input : ExactContractInput
  output : ExactContractOutput
  guarantee : GuaranteeClass
  localInvariants : List ExactLocalInvariant
  deriving DecidableEq, Repr

namespace ExactLayoutContract

def ofCertifiedWithin {available : AvailableSpace}
    (certified : CertifiedWithin available) : ExactLayoutContract :=
  { kind := certified.layout.kind
  , input := ExactContractInput.ofAvailable available
  , output := ExactContractOutput.ofExtent certified.extent
  , guarantee := .exact
  , localInvariants := certified.summary.localInvariants
  }

theorem ofCertifiedWithin_kind {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).kind = certified.layout.kind :=
  rfl

theorem ofCertifiedWithin_input_bounds {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).input.bounds = available.bounds :=
  rfl

theorem ofCertifiedWithin_output_extent {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).output.extent = certified.extent :=
  rfl

theorem ofCertifiedWithin_output_bounds {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).output.bounds = certified.extentBounds :=
  rfl

theorem ofCertifiedWithin_guarantee {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).guarantee = .exact :=
  rfl

theorem output_bounds_contains_extent {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).output.bounds.contains certified.extent := by
  simpa [ofCertifiedWithin] using
    ExactContractOutput.ofExtent_bounds_contains_extent certified.extent

theorem output_bounds_within_input_bounds {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    (ofCertifiedWithin certified).input.bounds.containsBounds
      (ofCertifiedWithin certified).output.bounds := by
  simpa [ofCertifiedWithin, ExactContractInput.ofAvailable, ExactContractOutput.ofExtent] using
    certified.extentBounds_within_availableBounds

theorem invariant_mem_holds
    {available : AvailableSpace}
    (certified : CertifiedWithin available)
    {invariant : ExactLocalInvariant}
    (hMem : invariant ∈ (ofCertifiedWithin certified).localInvariants) :
    invariant.Holds certified.layout := by
  simpa [ofCertifiedWithin] using certified.summary_invariant_holds hMem

end ExactLayoutContract

namespace CertifiedWithin

def contract {available : AvailableSpace}
    (certified : CertifiedWithin available) : ExactLayoutContract :=
  ExactLayoutContract.ofCertifiedWithin certified

theorem contract_guarantee {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    certified.contract.guarantee = .exact :=
  ExactLayoutContract.ofCertifiedWithin_guarantee certified

theorem contract_output_bounds_within_input_bounds {available : AvailableSpace}
    (certified : CertifiedWithin available) :
    certified.contract.input.bounds.containsBounds certified.contract.output.bounds :=
  ExactLayoutContract.output_bounds_within_input_bounds certified

theorem contract_invariant_holds
    {available : AvailableSpace}
    (certified : CertifiedWithin available)
    {invariant : ExactLocalInvariant}
    (hMem : invariant ∈ certified.contract.localInvariants) :
    invariant.Holds certified.layout :=
  ExactLayoutContract.invariant_mem_holds certified hMem

end CertifiedWithin

def checkWithinContract (available : AvailableSpace) (layout : Layout) :
    CheckResult ExactLayoutContract :=
  (checkWithinCertified available layout).map CertifiedWithin.contract

def checkContract (available : AvailableSpace) (layout : Layout) :
    CheckResult ExactLayoutContract :=
  (checkCertified available layout).map CertifiedWithin.contract

end TypedLayout.Core
