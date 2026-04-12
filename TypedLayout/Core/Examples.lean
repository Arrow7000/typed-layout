import TypedLayout.Core.Contract

namespace TypedLayout.Core.Examples

open TypedLayout.Core

def exactRowAvailable : AvailableSpace :=
  { extent := { width := 500, height := 40 } }

def exactRowLayout : Layout :=
  .row { amount := 10 }
    [ .leaf { width := 100, height := 20 }
    , .leaf { width := 150, height := 30 }
    , .leaf { width := 200, height := 25 }
    ]

def exactRowCheckedLayout : CheckedLayout :=
  .row { amount := 10 }
    [ .leaf { width := 100, height := 20 }
    , .leaf { width := 150, height := 30 }
    , .leaf { width := 200, height := 25 }
    ]

def exactRowExpectedExtent : ExactExtent :=
  { width := 470, height := 30 }

def roomyWidthBounds : AxisBounds :=
  AxisBounds.upTo 120

theorem roomyWidthBoundsContains100 :
    roomyWidthBounds.contains 100 := by
  native_decide

theorem roomyWidthBoundsCompatibleWithExact100 :
    roomyWidthBounds.compatibleWith (AxisBounds.exact 100) := by
  native_decide

theorem exactRowComputedExtent :
    ExactExtent.stack .horizontal { amount := 10 }
      [ { width := 100, height := 20 }
      , { width := 150, height := 30 }
      , { width := 200, height := 25 }
      ] = exactRowExpectedExtent := by
  native_decide

theorem exactRowExpectedFits : exactRowExpectedExtent.fitsWithin exactRowAvailable.extent := by
  native_decide

theorem exactRowExpectedExtentWithinAvailableBounds :
    exactRowAvailable.bounds.contains exactRowExpectedExtent := by
  exact (ExactExtent.fitsWithin_iff_upToBounds_contains).mp exactRowExpectedFits

theorem exactRowExtent :
    exactRowCheckedLayout.extent = exactRowExpectedExtent := by
  simpa [exactRowCheckedLayout, CheckedLayout.extent] using exactRowComputedExtent

theorem exactRowCheckGuarantee :
    (check exactRowAvailable exactRowLayout).isExact = true := by
  native_decide

theorem exactRowChildXOrigins :
    (exactRowCheckedLayout.evaluate.children.map (fun child => child.origin.x)) = [0, 110, 270] := by
  native_decide

theorem exactRowChildrenSeparated :
    AdjacentSeparatedAlong .horizontal { amount := 10 } exactRowCheckedLayout.evaluate.children := by
  simpa [CheckedLayout.evaluate, CheckedLayout.evaluateAt, exactRowCheckedLayout] using
    CheckedLayout.evaluateChildrenAlong_adjacentSeparated
      .horizontal Origin.zero { amount := 10 } 0
      [ .leaf { width := 100, height := 20 }
      , .leaf { width := 150, height := 30 }
      , .leaf { width := 200, height := 25 }
      ]

theorem exactRowChildrenSeparatedBool :
    adjacentSeparatedAlong? .horizontal { amount := 10 } exactRowCheckedLayout.evaluate.children = true := by
  native_decide

theorem exactRowChildrenFitWithin :
    exactRowCheckedLayout.evaluate.immediateChildrenFitWithin? = true := by
  native_decide

theorem exactRowChildrenFitWithinProp :
    ImmediateChildrenFitWithin exactRowCheckedLayout.evaluate := by
  simpa [CheckedLayout.evaluate, exactRowCheckedLayout] using
    CheckedLayout.evaluateAt_row_immediateChildrenFitWithin
      { amount := 10 }
      [ .leaf { width := 100, height := 20 }
      , .leaf { width := 150, height := 30 }
      , .leaf { width := 200, height := 25 }
      ]
      Origin.zero

theorem exactRowLocalWitness :
    exactRowCheckedLayout.localWitness? = true := by
  native_decide

theorem exactRowLocalSound :
    CheckedLayout.LocalSound exactRowCheckedLayout := by
  exact CheckedLayout.localWitness?_sound exactRowCheckedLayout exactRowLocalWitness

def exactRowCertified : CertifiedWithin exactRowAvailable :=
  match h : check exactRowAvailable exactRowLayout with
  | .exact checked => CertifiedWithin.ofCheck h
  | .incompatible error =>
      False.elim <| by
        have hExact := exactRowCheckGuarantee
        simp [CheckResult.isExact, h] at hExact

theorem exactRowCertifiedFits :
    exactRowCertified.layout.extent.fitsWithin exactRowAvailable.extent :=
  exactRowCertified.fits

theorem exactRowCertifiedLocalSound :
    CheckedLayout.LocalSound exactRowCertified.layout :=
  exactRowCertified.localSound

theorem exactRowCertifiedLocalWitness :
    exactRowCertified.layout.localWitness? = true :=
  exactRowCertified.localWitness

def exactRowSummary : ExactLayoutSummary :=
  exactRowCheckedLayout.summary

theorem exactRowSummaryGuarantee :
    exactRowSummary.guarantee = .exact := by
  simpa [exactRowSummary, CheckedLayout.summary] using
    CheckedLayout.summary_guarantee exactRowCheckedLayout

theorem exactRowSummaryLocalInvariants :
    exactRowSummary.localInvariants =
      [ .immediateChildrenFitWithin
      , .adjacentChildrenSeparated .horizontal { amount := 10 }
      ] := by
  native_decide

theorem exactRowSummaryChildExtents :
    exactRowSummary.children.map ExactLayoutSummary.extent =
      [ { width := 100, height := 20 }
      , { width := 150, height := 30 }
      , { width := 200, height := 25 }
      ] := by
  native_decide

theorem exactRowSummaryExtentBounds :
    exactRowSummary.extentBounds = exactRowExpectedExtent.toBounds := by
  native_decide

theorem exactRowSummaryBoundsWithinAvailable :
    exactRowAvailable.bounds.containsBounds exactRowSummary.extentBounds := by
  native_decide

theorem exactRowCertifiedSummaryLocalInvariants :
    exactRowCertified.summary.localInvariants =
      [ .immediateChildrenFitWithin
      , .adjacentChildrenSeparated .horizontal { amount := 10 }
      ] := by
  native_decide

theorem exactRowCertifiedBoundsWithinAvailable :
    exactRowAvailable.bounds.containsBounds exactRowCertified.extentBounds := by
  simpa [CertifiedWithin.extentBounds] using
    CertifiedWithin.extentBounds_within_availableBounds exactRowCertified

theorem exactRowCertifiedSummarySeparated :
    ExactLocalInvariant.Holds
      (.adjacentChildrenSeparated .horizontal { amount := 10 })
      exactRowCertified.layout := by
  have hMem :
      .adjacentChildrenSeparated .horizontal { amount := 10 } ∈
        exactRowCertified.summary.localInvariants := by
    simp [exactRowCertifiedSummaryLocalInvariants]
  exact CertifiedWithin.summary_invariant_holds exactRowCertified hMem

def exactRowContract : ExactLayoutContract :=
  exactRowCertified.contract

theorem exactRowCheckContractExact :
    (checkContract exactRowAvailable exactRowLayout).isExact = true := by
  native_decide

theorem exactRowContractKind :
    exactRowContract.kind = .row := by
  native_decide

theorem exactRowContractInputBounds :
    exactRowContract.input.bounds = exactRowAvailable.bounds := by
  simpa [exactRowContract, CertifiedWithin.contract] using
    ExactLayoutContract.ofCertifiedWithin_input_bounds exactRowCertified

theorem exactRowContractOutputExtent :
    exactRowContract.output.extent = exactRowExpectedExtent := by
  native_decide

theorem exactRowContractOutputBounds :
    exactRowContract.output.bounds = exactRowExpectedExtent.toBounds := by
  native_decide

theorem exactRowContractGuarantee :
    exactRowContract.guarantee = .exact := by
  simpa [exactRowContract, CertifiedWithin.contract] using
    CertifiedWithin.contract_guarantee exactRowCertified

theorem exactRowContractOutputBoundsWithinInputBounds :
    exactRowContract.input.bounds.containsBounds exactRowContract.output.bounds := by
  simpa [exactRowContract, CertifiedWithin.contract] using
    CertifiedWithin.contract_output_bounds_within_input_bounds exactRowCertified

theorem exactRowContractOutputBoundsContainOutputExtent :
    exactRowContract.output.bounds.contains exactRowExpectedExtent := by
  native_decide

theorem exactRowContractLocalInvariants :
    exactRowContract.localInvariants =
      [ .immediateChildrenFitWithin
      , .adjacentChildrenSeparated .horizontal { amount := 10 }
      ] := by
  native_decide

theorem exactRowContractSeparatedInvariantHolds :
    ExactLocalInvariant.Holds
      (.adjacentChildrenSeparated .horizontal { amount := 10 })
      exactRowCertified.layout := by
  have hMem :
      .adjacentChildrenSeparated .horizontal { amount := 10 } ∈
        exactRowContract.localInvariants := by
    simp [exactRowContractLocalInvariants]
  exact CertifiedWithin.contract_invariant_holds exactRowCertified hMem

def tooWideRowLayout : Layout :=
  .row { amount := 10 }
    [ .leaf { width := 150, height := 10 }
    , .leaf { width := 150, height := 10 }
    , .leaf { width := 150, height := 10 }
    ]

def tooWideRowExpectedExtent : ExactExtent :=
  { width := 470, height := 10 }

theorem tooWideRowComputedExtent :
    ExactExtent.stack .horizontal { amount := 10 }
      [ { width := 150, height := 10 }
      , { width := 150, height := 10 }
      , { width := 150, height := 10 }
      ] = tooWideRowExpectedExtent := by
  native_decide

theorem tooWideRowExpectedDoesNotFit : ¬ tooWideRowExpectedExtent.fitsWithin ({ width := 400, height := 40 }) := by
  native_decide

theorem tooWideRowError :
    (check { extent := { width := 400, height := 40 } } tooWideRowLayout).hasError
      (.doesNotFit .row { width := 400, height := 40 } { width := 470, height := 10 }) = true := by
  native_decide

def exactColumnCheckedLayout : CheckedLayout :=
  .column { amount := 5 }
    [ .leaf { width := 30, height := 20 }
    , .leaf { width := 40, height := 30 }
    , .leaf { width := 35, height := 10 }
    ]

theorem exactColumnExtent :
    exactColumnCheckedLayout.extent = { width := 40, height := 70 } := by
  native_decide

theorem exactColumnChildYOrigins :
    (exactColumnCheckedLayout.evaluate.children.map (fun child => child.origin.y)) = [0, 25, 60] := by
  native_decide

theorem exactColumnChildrenSeparated :
    AdjacentSeparatedAlong .vertical { amount := 5 } exactColumnCheckedLayout.evaluate.children := by
  simpa [CheckedLayout.evaluate, CheckedLayout.evaluateAt, exactColumnCheckedLayout] using
    CheckedLayout.evaluateAt_column_childrenAdjacentSeparated
      { amount := 5 }
      [ .leaf { width := 30, height := 20 }
      , .leaf { width := 40, height := 30 }
      , .leaf { width := 35, height := 10 }
      ]
      Origin.zero

theorem exactColumnChildrenSeparatedBool :
    adjacentSeparatedAlong? .vertical { amount := 5 } exactColumnCheckedLayout.evaluate.children = true := by
  native_decide

theorem exactColumnChildrenFitWithin :
    exactColumnCheckedLayout.evaluate.immediateChildrenFitWithin? = true := by
  native_decide

theorem exactColumnChildrenFitWithinProp :
    ImmediateChildrenFitWithin exactColumnCheckedLayout.evaluate := by
  simpa [CheckedLayout.evaluate, exactColumnCheckedLayout] using
    CheckedLayout.evaluateAt_column_immediateChildrenFitWithin
      { amount := 5 }
      [ .leaf { width := 30, height := 20 }
      , .leaf { width := 40, height := 30 }
      , .leaf { width := 35, height := 10 }
      ]
      Origin.zero

theorem exactColumnLocalWitness :
    exactColumnCheckedLayout.localWitness? = true := by
  native_decide

theorem exactColumnLocalSound :
    CheckedLayout.LocalSound exactColumnCheckedLayout := by
  exact CheckedLayout.localWitness?_sound exactColumnCheckedLayout exactColumnLocalWitness

def paddedLeafCheckedLayout : CheckedLayout :=
  .padding { left := 2, top := 1, right := 3, bottom := 1 }
    (.leaf { width := 10, height := 5 })

theorem paddedLeafChildFitsWithin :
    ImmediateChildrenFitWithin paddedLeafCheckedLayout.evaluate := by
  simpa [CheckedLayout.evaluate, paddedLeafCheckedLayout] using
    CheckedLayout.evaluateAt_padding_immediateChildrenFitWithin
      { left := 2, top := 1, right := 3, bottom := 1 }
      (.leaf { width := 10, height := 5 })
      Origin.zero

def paddedUnderflowLayout : Layout :=
  .padding { left := 3, top := 1, right := 3, bottom := 1 }
    (.leaf { width := 1, height := 1 })

theorem paddingUnderflowError :
    (check { extent := { width := 5, height := 4 } } paddedUnderflowLayout).hasError
      (.paddingInsetsOverflow
        { width := 5, height := 4 }
        { left := 3, top := 1, right := 3, bottom := 1 }) = true := by
  native_decide

def framedLeafLayout : Layout :=
  .frame { width := 120, height := 60 }
    (.leaf { width := 100, height := 50 })

def framedLeafCheckedLayout : CheckedLayout :=
  .frame { width := 120, height := 60 } (.leaf { width := 100, height := 50 })

theorem framedLeafCheckGuarantee :
    (check { extent := { width := 120, height := 60 } } framedLeafLayout).isExact = true := by
  native_decide

theorem framedLeafGeometry :
    framedLeafCheckedLayout.evaluate =
      { box := { origin := Origin.zero, extent := { width := 120, height := 60 } }
      , children :=
          [ { box := { origin := Origin.zero, extent := { width := 100, height := 50 } }
            , children := []
            } ]
      } := by
  simp [framedLeafCheckedLayout, CheckedLayout.evaluate, CheckedLayout.evaluateAt, Origin.zero]

theorem framedLeafChildFitsWithin :
    ImmediateChildrenFitWithin framedLeafCheckedLayout.evaluate := by
  have rawFits : ({ width := 100, height := 50 } : ExactExtent).fitsWithin ({ width := 120, height := 60 } : ExactExtent) := by
    native_decide
  have fits : (CheckedLayout.leaf { width := 100, height := 50 }).extent.fitsWithin ({ width := 120, height := 60 } : ExactExtent) := by
    simpa [CheckedLayout.extent] using rawFits
  simpa [CheckedLayout.evaluate, framedLeafCheckedLayout] using
    CheckedLayout.evaluateAt_frame_immediateChildrenFitWithin
      ({ width := 120, height := 60 } : ExactExtent)
      (.leaf { width := 100, height := 50 })
      Origin.zero
      fits

def framedLeafSummary : ExactLayoutSummary :=
  framedLeafCheckedLayout.summary

theorem framedLeafSummaryLocalInvariants :
    framedLeafSummary.localInvariants =
      [ .frameChildFitsWithin
      , .immediateChildrenFitWithin
      ] := by
  native_decide

theorem framedLeafLocalSound :
    CheckedLayout.LocalSound framedLeafCheckedLayout := by
  refine ⟨?_, framedLeafChildFitsWithin, trivial⟩
  native_decide

theorem framedLeafSummaryFrameChildFits :
    ExactLocalInvariant.Holds .frameChildFitsWithin framedLeafCheckedLayout := by
  have hMem : .frameChildFitsWithin ∈ framedLeafSummary.localInvariants := by
    simp [framedLeafSummaryLocalInvariants]
  exact CheckedLayout.summary_invariant_holds framedLeafLocalSound hMem

def framedLeafAvailable : AvailableSpace :=
  { extent := { width := 120, height := 60 } }

def framedLeafCertified : CertifiedWithin framedLeafAvailable :=
  match h : check { extent := { width := 120, height := 60 } } framedLeafLayout with
  | .exact checked => by
      simpa [framedLeafAvailable] using (CertifiedWithin.ofCheck h)
  | .incompatible error =>
      False.elim <| by
        have hExact := framedLeafCheckGuarantee
        simp [CheckResult.isExact, h] at hExact

def framedLeafContract : ExactLayoutContract :=
  framedLeafCertified.contract

theorem framedLeafContractLocalInvariants :
    framedLeafContract.localInvariants =
      [ .frameChildFitsWithin
      , .immediateChildrenFitWithin
      ] := by
  native_decide

theorem framedLeafContractFrameChildFits :
    ExactLocalInvariant.Holds .frameChildFitsWithin framedLeafCertified.layout := by
  have hMem : .frameChildFitsWithin ∈ framedLeafContract.localInvariants := by
    simp [framedLeafContractLocalInvariants]
  exact CertifiedWithin.contract_invariant_holds framedLeafCertified hMem

def nestedFrameRowLayout : Layout :=
  .frame { width := 200, height := 80 }
    (.padding { left := 10, top := 5, right := 10, bottom := 5 }
      (.row { amount := 8 }
        [ .leaf { width := 60, height := 20 }
        , .leaf { width := 40, height := 30 }
        ]))

def nestedFrameRowCheckedLayout : CheckedLayout :=
  .frame { width := 200, height := 80 }
    (.padding { left := 10, top := 5, right := 10, bottom := 5 }
      (.row { amount := 8 }
        [ .leaf { width := 60, height := 20 }
        , .leaf { width := 40, height := 30 }
        ]))

theorem nestedFrameRowCheckExact :
    (check { extent := { width := 200, height := 80 } } nestedFrameRowLayout).isExact = true := by
  native_decide

theorem nestedFrameRowGeometryRoot :
    nestedFrameRowCheckedLayout.evaluate.box =
      { origin := Origin.zero, extent := { width := 200, height := 80 } } := by
  native_decide

theorem nestedFrameRowInnerOrigins :
    nestedFrameRowCheckedLayout.evaluate.children.map (fun child => child.origin) =
      [ Origin.zero ] := by
  native_decide

theorem nestedFrameRowLeafOrigins :
    nestedFrameRowCheckedLayout.evaluate.children.map
      (fun child => child.children.map (fun grand => grand.children.map (fun leaf => leaf.origin))) =
      [[[ { x := 10, y := 5 }, { x := 78, y := 5 } ]]] := by
  native_decide

theorem nestedFrameRowFullGeometry :
    nestedFrameRowCheckedLayout.evaluate =
      { box := { origin := Origin.zero, extent := { width := 200, height := 80 } }
      , children :=
          [ { box := { origin := Origin.zero, extent := { width := 128, height := 40 } }
            , children :=
                [ { box := { origin := { x := 10, y := 5 }, extent := { width := 108, height := 30 } }
                  , children :=
                      [ { box := { origin := { x := 10, y := 5 }, extent := { width := 60, height := 20 } }
                        , children := []
                        }
                      , { box := { origin := { x := 78, y := 5 }, extent := { width := 40, height := 30 } }
                        , children := []
                        }
                      ]
                  } ]
            } ]
      } := by
  native_decide

theorem nestedFrameRowPaddingChildFits :
    ImmediateChildrenFitWithin nestedFrameRowCheckedLayout.evaluate := by
  have fits :
      (CheckedLayout.padding { left := 10, top := 5, right := 10, bottom := 5 }
        (.row { amount := 8 }
          [ .leaf { width := 60, height := 20 }
          , .leaf { width := 40, height := 30 }
          ])).extent.fitsWithin ({ width := 200, height := 80 } : ExactExtent) := by
    native_decide
  simpa [nestedFrameRowCheckedLayout, CheckedLayout.evaluate] using
    CheckedLayout.evaluateAt_frame_immediateChildrenFitWithin
      ({ width := 200, height := 80 } : ExactExtent)
      (CheckedLayout.padding { left := 10, top := 5, right := 10, bottom := 5 }
        (.row { amount := 8 }
          [ .leaf { width := 60, height := 20 }
          , .leaf { width := 40, height := 30 }
          ]))
      Origin.zero
      fits

theorem nestedFrameRowLocalWitness :
    nestedFrameRowCheckedLayout.localWitness? = true := by
  native_decide

theorem nestedFrameRowLocalSound :
    CheckedLayout.LocalSound nestedFrameRowCheckedLayout := by
  exact CheckedLayout.localWitness?_sound nestedFrameRowCheckedLayout nestedFrameRowLocalWitness

end TypedLayout.Core.Examples
