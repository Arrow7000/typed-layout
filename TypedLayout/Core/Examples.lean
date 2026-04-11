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

def exactRowChecked : CheckedLayout :=
  .row { amount := 10 }
    [ .leaf { width := 100, height := 20 }
    , .leaf { width := 150, height := 30 }
    , .leaf { width := 200, height := 25 }
    ]

theorem exactRowExtent :
    exactRowChecked.extent = { width := 470, height := 30 } := by
  simp [exactRowChecked, CheckedLayout.extent]

theorem exactRowCheck :
    check exactRowAvailable exactRowLayout = .exact exactRowChecked := by
  simp [check, checkWithin, checkChildrenWithin, exactRowAvailable, exactRowLayout, exactRowChecked,
    CheckedLayout.extent, ExactExtent.fitsWithin]

theorem exactRowChildXOrigins :
    (exactRowChecked.evaluate.children.map (fun child => child.origin.x)) = [0, 110, 270] := by
  simp [CheckedLayout.evaluate, CheckedLayout.evaluateAt, CheckedLayout.evaluateChildrenAlong,
    CheckedLayout.mainExtent, CheckedLayout.extent, ExactExtent.main, exactRowChecked, Origin.zero,
    Origin.translateAxis, Origin.translate]

def tooWideRowLayout : Layout :=
  .row { amount := 10 }
    [ .leaf { width := 150, height := 10 }
    , .leaf { width := 150, height := 10 }
    , .leaf { width := 150, height := 10 }
    ]

theorem tooWideRowRejected :
    check { extent := { width := 400, height := 40 } } tooWideRowLayout =
      .incompatible (.doesNotFit .row { width := 400, height := 40 } { width := 470, height := 10 }) := by
  simp [check, checkWithin, checkChildrenWithin, tooWideRowLayout, CheckedLayout.extent,
    ExactExtent.fitsWithin]

def exactColumnChecked : CheckedLayout :=
  .column { amount := 5 }
    [ .leaf { width := 30, height := 20 }
    , .leaf { width := 40, height := 30 }
    , .leaf { width := 35, height := 10 }
    ]

theorem exactColumnExtent :
    exactColumnChecked.extent = { width := 40, height := 70 } := by
  simp [exactColumnChecked, CheckedLayout.extent]

theorem exactColumnChildYOrigins :
    (exactColumnChecked.evaluate.children.map (fun child => child.origin.y)) = [0, 25, 60] := by
  simp [CheckedLayout.evaluate, CheckedLayout.evaluateAt, CheckedLayout.evaluateChildrenAlong,
    CheckedLayout.mainExtent, CheckedLayout.extent, ExactExtent.main, exactColumnChecked, Origin.zero,
    Origin.translateAxis, Origin.translate]

def paddedUnderflowLayout : Layout :=
  .padding { left := 3, top := 1, right := 3, bottom := 1 }
    (.leaf { width := 1, height := 1 })

theorem paddingUnderflowRejected :
    check { extent := { width := 5, height := 4 } } paddedUnderflowLayout =
      .incompatible
        (.paddingInsetsOverflow
          { width := 5, height := 4 }
          { left := 3, top := 1, right := 3, bottom := 1 }) := by
  simp [check, checkWithin, paddedUnderflowLayout, ExactExtent.inset?, Insets.horizontal]

def framedLeafLayout : Layout :=
  .frame { width := 120, height := 60 }
    (.leaf { width := 100, height := 50 })

def framedLeafChecked : CheckedLayout :=
  .frame { width := 120, height := 60 }
    (.leaf { width := 100, height := 50 })

theorem framedLeafCheck :
    check { extent := { width := 120, height := 60 } } framedLeafLayout = .exact framedLeafChecked := by
  simp [check, checkWithin, framedLeafLayout, framedLeafChecked,
    ExactExtent.fitsWithin]

theorem framedLeafGeometry :
    framedLeafChecked.evaluate =
      { origin := Origin.zero
      , extent := { width := 120, height := 60 }
      , children :=
          [ { origin := Origin.zero
            , extent := { width := 100, height := 50 }
            , children := []
            } ]
      } := by
  simp [CheckedLayout.evaluate, CheckedLayout.evaluateAt, framedLeafChecked, Origin.zero]

end TypedLayout.Core.Examples
