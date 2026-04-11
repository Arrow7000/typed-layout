import TypedLayout.Core.Eval

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

theorem exactRowComputedExtent :
    ExactExtent.stack .horizontal { amount := 10 }
      [ { width := 100, height := 20 }
      , { width := 150, height := 30 }
      , { width := 200, height := 25 }
      ] = exactRowExpectedExtent := by
  native_decide

theorem exactRowExpectedFits : exactRowExpectedExtent.fitsWithin exactRowAvailable.extent := by
  native_decide

theorem exactRowExtent :
    exactRowCheckedLayout.extent = exactRowExpectedExtent := by
  simpa [exactRowCheckedLayout, CheckedLayout.extent] using exactRowComputedExtent

theorem exactRowCheckGuarantee :
    (check exactRowAvailable exactRowLayout).guaranteeClass = .exact := by
  let computedExtent : ExactExtent :=
    ExactExtent.ofAxis Axis.horizontal
      (({ width := 100, height := 20 } : ExactExtent).main Axis.horizontal + 10 +
        ({ width := 150, height := 30 } : ExactExtent).main Axis.horizontal + 10 +
        ({ width := 200, height := 25 } : ExactExtent).main Axis.horizontal)
      (max (({ width := 100, height := 20 } : ExactExtent).cross Axis.horizontal)
        (max (({ width := 150, height := 30 } : ExactExtent).cross Axis.horizontal)
          (({ width := 200, height := 25 } : ExactExtent).cross Axis.horizontal)))
  have fits : computedExtent.fitsWithin exactRowAvailable.extent := by
    simpa [exactRowExpectedExtent, exactRowComputedExtent] using exactRowExpectedFits
  have fits' : computedExtent.width ≤ 500 ∧ computedExtent.height ≤ 40 := by
    simpa [ExactExtent.fitsWithin] using fits
  simp [CheckResult.guaranteeClass, check, checkWithin, checkChildrenWithin, exactRowAvailable,
    exactRowLayout, CheckedWithin.childLayouts, CheckedLayout.extent, ExactExtent.stack,
    ExactExtent.stackedMain, ExactExtent.stackedCross, ExactExtent.fitsWithin, computedExtent, fits']

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
    (check { extent := { width := 400, height := 40 } } tooWideRowLayout).error? =
      some (.doesNotFit .row { width := 400, height := 40 } { width := 470, height := 10 }) := by
  let computedExtent : ExactExtent :=
    ExactExtent.ofAxis Axis.horizontal
      (({ width := 150, height := 10 } : ExactExtent).main Axis.horizontal + 10 +
        ({ width := 150, height := 10 } : ExactExtent).main Axis.horizontal + 10 +
        ({ width := 150, height := 10 } : ExactExtent).main Axis.horizontal)
      (({ width := 150, height := 10 } : ExactExtent).cross Axis.horizontal)
  have computedExtentEq : computedExtent = { width := 470, height := 10 } := by
    simpa [computedExtent, tooWideRowExpectedExtent] using tooWideRowComputedExtent
  simp [CheckResult.error?, check, checkWithin, checkChildrenWithin, tooWideRowLayout,
    CheckedWithin.childLayouts, CheckedLayout.extent, ExactExtent.stack,
    ExactExtent.stackedMain, ExactExtent.stackedCross, ExactExtent.fitsWithin,
    computedExtent, computedExtentEq]

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

def paddedUnderflowLayout : Layout :=
  .padding { left := 3, top := 1, right := 3, bottom := 1 }
    (.leaf { width := 1, height := 1 })

theorem paddingUnderflowError :
    (check { extent := { width := 5, height := 4 } } paddedUnderflowLayout).error? =
      some
        (.paddingInsetsOverflow
          { width := 5, height := 4 }
          { left := 3, top := 1, right := 3, bottom := 1 }) := by
  simp [CheckResult.error?, check, checkWithin, paddedUnderflowLayout, ExactExtent.inset?, Insets.horizontal]

def framedLeafLayout : Layout :=
  .frame { width := 120, height := 60 }
    (.leaf { width := 100, height := 50 })

def framedLeafCheckedLayout : CheckedLayout :=
  .frame { width := 120, height := 60 } (.leaf { width := 100, height := 50 })

theorem framedLeafCheckGuarantee :
    (check { extent := { width := 120, height := 60 } } framedLeafLayout).guaranteeClass = .exact := by
  simp [CheckResult.guaranteeClass, check, checkWithin, framedLeafLayout, ExactExtent.fitsWithin]

theorem framedLeafGeometry :
    framedLeafCheckedLayout.evaluate =
      { box := { origin := Origin.zero, extent := { width := 120, height := 60 } }
      , children :=
          [ { box := { origin := Origin.zero, extent := { width := 100, height := 50 } }
            , children := []
            } ]
      } := by
  simp [framedLeafCheckedLayout, CheckedLayout.evaluate, CheckedLayout.evaluateAt, Origin.zero]

end TypedLayout.Core.Examples
