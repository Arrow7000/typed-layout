import TypedLayout.Core.Eval

namespace TypedLayout.Core

def ChildrenFitWithin (parent : Box) : List GeometryTree → Prop
  | [] => True
  | child :: rest => child.box.fitsWithin parent ∧ ChildrenFitWithin parent rest

def ImmediateChildrenFitWithin (tree : GeometryTree) : Prop :=
  ChildrenFitWithin tree.box tree.children

namespace Box

theorem fitsWithin_refl (box : Box) : box.fitsWithin box := by
  unfold Box.fitsWithin Box.right Box.bottom
  omega

theorem fitsWithin_trans {inner middle outer : Box}
    (h₁ : inner.fitsWithin middle)
    (h₂ : middle.fitsWithin outer) :
    inner.fitsWithin outer := by
  rcases h₁ with ⟨left₁, top₁, right₁, bottom₁⟩
  rcases h₂ with ⟨left₂, top₂, right₂, bottom₂⟩
  exact ⟨Nat.le_trans left₂ left₁, Nat.le_trans top₂ top₁,
    Nat.le_trans right₁ right₂, Nat.le_trans bottom₁ bottom₂⟩

theorem sameOriginFitsWithin_of_extentFits
    (origin : Origin)
    {inner outer : ExactExtent}
    (h : inner.fitsWithin outer) :
    ({ origin := origin, extent := inner } : Box).fitsWithin { origin := origin, extent := outer } := by
  rcases h with ⟨widthFits, heightFits⟩
  unfold Box.fitsWithin Box.right Box.bottom
  simp [widthFits, heightFits]

theorem translatedInsetFitsWithinExpanded
    (origin : Origin)
    (inner : ExactExtent)
    (insets : Insets) :
    ({ origin := origin.translate insets.left insets.top, extent := inner } : Box).fitsWithin
      { origin := origin, extent := inner.expand insets } := by
  unfold Box.fitsWithin Box.right Box.bottom Origin.translate ExactExtent.expand
  simp
  omega

end Box

def stackEnvelopeExtent
    (axis : Axis)
    (gap : Gap)
    (cursor : Nat)
    (children : List CheckedLayout) : ExactExtent :=
  ExactExtent.ofAxis axis
    (cursor + ExactExtent.stackedMain axis gap (children.map CheckedLayout.extent))
    (ExactExtent.stackedCross axis (children.map CheckedLayout.extent))

def stackEnvelopeBox
    (axis : Axis)
    (gap : Gap)
    (origin : Origin)
    (cursor : Nat)
    (children : List CheckedLayout) : Box :=
  { origin := origin, extent := stackEnvelopeExtent axis gap cursor children }

namespace GeometryTree

def immediateChildrenFitWithin? (tree : GeometryTree) : Bool :=
  tree.children.all (fun child => decide (child.box.fitsWithin tree.box))

theorem childrenFitWithin?_sound
    (parent : Box)
    (children : List GeometryTree) :
    children.all (fun child => decide (child.box.fitsWithin parent)) = true →
      ChildrenFitWithin parent children := by
  induction children with
  | nil =>
      intro _
      simp [ChildrenFitWithin]
  | cons child rest ih =>
      intro h
      simp only [List.all_cons, ChildrenFitWithin, Bool.and_eq_true] at h ⊢
      exact ⟨of_decide_eq_true h.1, ih h.2⟩

theorem immediateChildrenFitWithin?_sound (tree : GeometryTree) :
    tree.immediateChildrenFitWithin? = true → ImmediateChildrenFitWithin tree := by
  intro h
  exact childrenFitWithin?_sound tree.box tree.children h

theorem childrenFitWithin?_complete
    (parent : Box)
    (children : List GeometryTree) :
    ChildrenFitWithin parent children →
      children.all (fun child => decide (child.box.fitsWithin parent)) = true := by
  induction children with
  | nil =>
      intro _
      simp
  | cons child rest ih =>
      intro h
      rcases h with ⟨headFits, restFits⟩
      simp [headFits, ih restFits]

theorem immediateChildrenFitWithin?_complete (tree : GeometryTree) :
    ImmediateChildrenFitWithin tree → tree.immediateChildrenFitWithin? = true := by
  intro h
  exact childrenFitWithin?_complete tree.box tree.children h

theorem childrenFitWithin_nil (parent : Box) : ChildrenFitWithin parent [] := by
  trivial

theorem childrenFitWithin_cons {parent : Box} {child : GeometryTree} {rest : List GeometryTree} :
    child.box.fitsWithin parent →
      ChildrenFitWithin parent rest →
      ChildrenFitWithin parent (child :: rest) := by
  intro headFits restFits
  exact ⟨headFits, restFits⟩

theorem childrenFitWithin_forallMem {parent : Box} {children : List GeometryTree} :
    ChildrenFitWithin parent children →
      ∀ child ∈ children, child.box.fitsWithin parent := by
  intro h child childMem
  induction children generalizing child with
  | nil =>
      cases childMem
  | cons head tail ih =>
      simp [ChildrenFitWithin] at h
      simp at childMem
      rcases h with ⟨headFits, tailFits⟩
      cases childMem with
      | inl childEq =>
          cases childEq
          exact headFits
      | inr tailMem =>
          exact ih tailFits child tailMem

theorem immediateChildrenFitWithin_leaf (extent : ExactExtent) (origin : Origin) :
    ImmediateChildrenFitWithin
      { box := { origin := origin, extent := extent }, children := [] } := by
  simp [ImmediateChildrenFitWithin, ChildrenFitWithin]

end GeometryTree

namespace CheckedLayout

mutual

def LocalSound : CheckedLayout → Prop
  | .leaf _ => True
  | .row gap children =>
      ImmediateChildrenFitWithin (CheckedLayout.row gap children).evaluate ∧
        AdjacentSeparatedAlong .horizontal gap (CheckedLayout.row gap children).evaluate.children ∧
        LocalSounds children
  | .column gap children =>
      ImmediateChildrenFitWithin (CheckedLayout.column gap children).evaluate ∧
        AdjacentSeparatedAlong .vertical gap (CheckedLayout.column gap children).evaluate.children ∧
        LocalSounds children
  | .padding insets child =>
      ImmediateChildrenFitWithin (CheckedLayout.padding insets child).evaluate ∧
        LocalSound child
  | .frame extent child =>
      child.extent.fitsWithin extent ∧
        ImmediateChildrenFitWithin (CheckedLayout.frame extent child).evaluate ∧
        LocalSound child

def LocalSounds : List CheckedLayout → Prop
  | [] => True
  | child :: rest => LocalSound child ∧ LocalSounds rest

end

mutual

def localWitness? : CheckedLayout → Bool
  | .leaf _ => true
  | .row gap children =>
      let tree := (CheckedLayout.row gap children).evaluate
      tree.immediateChildrenFitWithin? &&
        adjacentSeparatedAlong? .horizontal gap tree.children &&
        localWitnesses? children
  | .column gap children =>
      let tree := (CheckedLayout.column gap children).evaluate
      tree.immediateChildrenFitWithin? &&
        adjacentSeparatedAlong? .vertical gap tree.children &&
        localWitnesses? children
  | .padding insets child =>
      let tree := (CheckedLayout.padding insets child).evaluate
      tree.immediateChildrenFitWithin? && localWitness? child
  | .frame extent child =>
      let tree := (CheckedLayout.frame extent child).evaluate
      decide (child.extent.fitsWithin extent) && tree.immediateChildrenFitWithin? && localWitness? child

def localWitnesses? : List CheckedLayout → Bool
  | [] => true
  | child :: rest => localWitness? child && localWitnesses? rest

end

mutual

theorem localWitness?_sound : ∀ layout : CheckedLayout,
    localWitness? layout = true → LocalSound layout
  | .leaf _, _ => by
      trivial
  | .row gap children, h => by
      have h' :
          (((CheckedLayout.row gap children).evaluate.immediateChildrenFitWithin? = true) ∧
              (adjacentSeparatedAlong? .horizontal gap
                (CheckedLayout.row gap children).evaluate.children = true)) ∧
            localWitnesses? children = true := by
        simpa [localWitness?, Bool.and_eq_true] using h
      exact ⟨GeometryTree.immediateChildrenFitWithin?_sound _ h'.1.1,
        ⟨adjacentSeparatedAlong?_sound .horizontal gap _ h'.1.2,
          localWitnesses?_sound children h'.2⟩⟩
  | .column gap children, h => by
      have h' :
          (((CheckedLayout.column gap children).evaluate.immediateChildrenFitWithin? = true) ∧
              (adjacentSeparatedAlong? .vertical gap
                (CheckedLayout.column gap children).evaluate.children = true)) ∧
            localWitnesses? children = true := by
        simpa [localWitness?, Bool.and_eq_true] using h
      exact ⟨GeometryTree.immediateChildrenFitWithin?_sound _ h'.1.1,
        ⟨adjacentSeparatedAlong?_sound .vertical gap _ h'.1.2,
          localWitnesses?_sound children h'.2⟩⟩
  | .padding insets child, h => by
      have h' :
          ((CheckedLayout.padding insets child).evaluate.immediateChildrenFitWithin? = true) ∧
            localWitness? child = true := by
        simpa [localWitness?, Bool.and_eq_true] using h
      exact ⟨GeometryTree.immediateChildrenFitWithin?_sound _ h'.1,
        localWitness?_sound child h'.2⟩
  | .frame extent child, h => by
      have h' :
          ((decide (child.extent.fitsWithin extent) = true) ∧
              ((CheckedLayout.frame extent child).evaluate.immediateChildrenFitWithin? = true)) ∧
            localWitness? child = true := by
        simpa [localWitness?, Bool.and_eq_true] using h
      exact ⟨of_decide_eq_true h'.1.1,
        ⟨GeometryTree.immediateChildrenFitWithin?_sound _ h'.1.2,
          localWitness?_sound child h'.2⟩⟩

theorem localWitnesses?_sound : ∀ children : List CheckedLayout,
    localWitnesses? children = true → LocalSounds children
  | [], _ => by
      trivial
  | child :: rest, h => by
      have h' : localWitness? child = true ∧ localWitnesses? rest = true := by
        simpa [localWitnesses?, Bool.and_eq_true] using h
      exact ⟨localWitness?_sound child h'.1, localWitnesses?_sound rest h'.2⟩

theorem localWitness?_complete : ∀ layout : CheckedLayout,
    LocalSound layout → localWitness? layout = true
  | .leaf _, _ => by
      simp [localWitness?]
  | .row gap children, h => by
      rcases h with ⟨hWithin, hAdj, hChildren⟩
      have hWithin' :
          (CheckedLayout.row gap children).evaluate.immediateChildrenFitWithin? = true :=
        GeometryTree.immediateChildrenFitWithin?_complete _ hWithin
      have hAdj' :
          adjacentSeparatedAlong? .horizontal gap
            (CheckedLayout.row gap children).evaluate.children = true :=
        adjacentSeparatedAlong_complete .horizontal gap _ hAdj
      have hChildren' : localWitnesses? children = true :=
        localWitnesses?_complete children hChildren
      simp [localWitness?, hWithin', hAdj', hChildren']
  | .column gap children, h => by
      rcases h with ⟨hWithin, hAdj, hChildren⟩
      have hWithin' :
          (CheckedLayout.column gap children).evaluate.immediateChildrenFitWithin? = true :=
        GeometryTree.immediateChildrenFitWithin?_complete _ hWithin
      have hAdj' :
          adjacentSeparatedAlong? .vertical gap
            (CheckedLayout.column gap children).evaluate.children = true :=
        adjacentSeparatedAlong_complete .vertical gap _ hAdj
      have hChildren' : localWitnesses? children = true :=
        localWitnesses?_complete children hChildren
      simp [localWitness?, hWithin', hAdj', hChildren']
  | .padding insets child, h => by
      rcases h with ⟨hWithin, hChild⟩
      have hWithin' :
          (CheckedLayout.padding insets child).evaluate.immediateChildrenFitWithin? = true :=
        GeometryTree.immediateChildrenFitWithin?_complete _ hWithin
      have hChild' : localWitness? child = true :=
        localWitness?_complete child hChild
      simp [localWitness?, hWithin', hChild']
  | .frame extent child, h => by
      rcases h with ⟨hFit, hWithin, hChild⟩
      have hFit' : decide (child.extent.fitsWithin extent) = true := by
        simp [hFit]
      have hWithin' :
          (CheckedLayout.frame extent child).evaluate.immediateChildrenFitWithin? = true :=
        GeometryTree.immediateChildrenFitWithin?_complete _ hWithin
      have hChild' : localWitness? child = true :=
        localWitness?_complete child hChild
      simp [localWitness?, hFit', hWithin', hChild']

theorem localWitnesses?_complete : ∀ children : List CheckedLayout,
    LocalSounds children → localWitnesses? children = true
  | [], _ => by
      simp [localWitnesses?]
  | child :: rest, h => by
      rcases h with ⟨hChild, hRest⟩
      have hChild' : localWitness? child = true :=
        localWitness?_complete child hChild
      have hRest' : localWitnesses? rest = true :=
        localWitnesses?_complete rest hRest
      simp [localWitnesses?, hChild', hRest']

end

theorem stackEnvelopeExtent_tail_fitsWithin_cons
    (axis : Axis)
    (gap : Gap)
    (cursor : Nat)
    (child next : CheckedLayout)
    (tail : List CheckedLayout) :
    (stackEnvelopeExtent axis gap (cursor + child.mainExtent axis + gap.amount) (next :: tail)).fitsWithin
      (stackEnvelopeExtent axis gap cursor (child :: next :: tail)) := by
  cases axis with
  | horizontal =>
      unfold stackEnvelopeExtent ExactExtent.fitsWithin
      simp [CheckedLayout.mainExtent, ExactExtent.main, ExactExtent.cross, ExactExtent.ofAxis,
        ExactExtent.stackedMain_cons_cons, ExactExtent.stackedCross_cons]
      constructor
      · omega
      · exact ExactExtent.stackedCross_tail_le_cons .horizontal child.extent (List.map CheckedLayout.extent (next :: tail))
  | vertical =>
      unfold stackEnvelopeExtent ExactExtent.fitsWithin
      simp [CheckedLayout.mainExtent, ExactExtent.main, ExactExtent.cross, ExactExtent.ofAxis,
        ExactExtent.stackedMain_cons_cons, ExactExtent.stackedCross_cons]
      constructor
      · exact ExactExtent.stackedCross_tail_le_cons .vertical child.extent (List.map CheckedLayout.extent (next :: tail))
      · omega

theorem stackEnvelopeBox_tail_fitsWithin_cons
    (axis : Axis)
    (gap : Gap)
    (origin : Origin)
    (cursor : Nat)
    (child next : CheckedLayout)
    (tail : List CheckedLayout) :
    (stackEnvelopeBox axis gap origin (cursor + child.mainExtent axis + gap.amount) (next :: tail)).fitsWithin
      (stackEnvelopeBox axis gap origin cursor (child :: next :: tail)) := by
  unfold stackEnvelopeBox
  exact Box.sameOriginFitsWithin_of_extentFits origin
    (stackEnvelopeExtent_tail_fitsWithin_cons axis gap cursor child next tail)

theorem firstEvaluatedChildFitsWithinStackEnvelope
    (axis : Axis)
    (gap : Gap)
    (origin : Origin)
    (cursor : Nat)
    (child : CheckedLayout)
    (rest : List CheckedLayout) :
    ((child.evaluateAt (origin.translateAxis axis cursor)).box).fitsWithin
      (stackEnvelopeBox axis gap origin cursor (child :: rest)) := by
  rw [CheckedLayout.evaluateAt_box child (origin.translateAxis axis cursor)]
  unfold stackEnvelopeBox stackEnvelopeExtent
  cases axis with
  | horizontal =>
      unfold Box.fitsWithin Box.right Box.bottom Origin.translateAxis Origin.translate
      simp [ExactExtent.cross, ExactExtent.ofAxis,
        ExactExtent.stackedCross_cons]
      constructor
      · cases rest with
        | nil =>
            simp [ExactExtent.stackedMain, ExactExtent.main]
            omega
        | cons next tail =>
            simp [ExactExtent.stackedMain_cons_cons, ExactExtent.main]
            omega
      · exact ExactExtent.cross_le_stackedCross_of_mem .horizontal child.extent
          (child.extent :: List.map CheckedLayout.extent rest) (by simp)
  | vertical =>
      unfold Box.fitsWithin Box.right Box.bottom Origin.translateAxis Origin.translate
      simp [ExactExtent.cross, ExactExtent.ofAxis,
        ExactExtent.stackedCross_cons]
      constructor
      · exact ExactExtent.cross_le_stackedCross_of_mem .vertical child.extent
          (child.extent :: List.map CheckedLayout.extent rest) (by simp)
      · cases rest with
        | nil =>
            simp [ExactExtent.stackedMain, ExactExtent.main]
            omega
        | cons next tail =>
            simp [ExactExtent.stackedMain_cons_cons, ExactExtent.main]
            omega

theorem evaluateChildrenAlong_childrenFitWithinParent
    (axis : Axis)
    (gap : Gap)
    (origin : Origin)
    (cursor : Nat)
    (children : List CheckedLayout)
    (parent : Box)
    (hEnv : (stackEnvelopeBox axis gap origin cursor children).fitsWithin parent) :
    ChildrenFitWithin parent (CheckedLayout.evaluateChildrenAlong axis origin gap cursor children) := by
  revert parent
  induction children generalizing cursor with
  | nil =>
      intro parent hEnv
      simp [ChildrenFitWithin, CheckedLayout.evaluateChildrenAlong]
  | cons child rest ih =>
      intro parent hEnv
      cases rest with
      | nil =>
          simpa [ChildrenFitWithin, CheckedLayout.evaluateChildrenAlong] using
            GeometryTree.childrenFitWithin_cons
              (Box.fitsWithin_trans
                (firstEvaluatedChildFitsWithinStackEnvelope axis gap origin cursor child [])
                hEnv)
              (GeometryTree.childrenFitWithin_nil parent)
      | cons next tail =>
          have hTail :
              (stackEnvelopeBox axis gap origin (cursor + child.mainExtent axis + gap.amount) (next :: tail)).fitsWithin parent := by
            exact Box.fitsWithin_trans
              (stackEnvelopeBox_tail_fitsWithin_cons axis gap origin cursor child next tail)
              hEnv
          simpa [ChildrenFitWithin, CheckedLayout.evaluateChildrenAlong] using
            GeometryTree.childrenFitWithin_cons
              (Box.fitsWithin_trans
                (firstEvaluatedChildFitsWithinStackEnvelope axis gap origin cursor child (next :: tail))
                hEnv)
              (ih (cursor + child.mainExtent axis + gap.amount) parent hTail)

theorem evaluateAt_row_childrenAdjacentSeparated
    (gap : Gap)
    (children : List CheckedLayout)
    (origin : Origin) :
    AdjacentSeparatedAlong .horizontal gap ((CheckedLayout.row gap children).evaluateAt origin).children := by
  simpa [evaluateAt] using evaluateChildrenAlong_adjacentSeparated .horizontal origin gap 0 children

theorem evaluateAt_column_childrenAdjacentSeparated
    (gap : Gap)
    (children : List CheckedLayout)
    (origin : Origin) :
    AdjacentSeparatedAlong .vertical gap ((CheckedLayout.column gap children).evaluateAt origin).children := by
  simpa [evaluateAt] using evaluateChildrenAlong_adjacentSeparated .vertical origin gap 0 children

theorem evaluateAt_row_immediateChildrenFitWithin
    (gap : Gap)
    (children : List CheckedLayout)
    (origin : Origin) :
    ImmediateChildrenFitWithin ((CheckedLayout.row gap children).evaluateAt origin) := by
  have hEnv :
      (stackEnvelopeBox .horizontal gap origin 0 children).fitsWithin
        ((CheckedLayout.row gap children).evaluateAt origin).box := by
    rw [CheckedLayout.evaluateAt_box (CheckedLayout.row gap children) origin]
    simpa [stackEnvelopeBox, stackEnvelopeExtent, CheckedLayout.extent, ExactExtent.stack] using
      (Box.fitsWithin_refl { origin := origin, extent := (CheckedLayout.row gap children).extent })
  simpa [ImmediateChildrenFitWithin, CheckedLayout.evaluateAt] using
    evaluateChildrenAlong_childrenFitWithinParent .horizontal gap origin 0 children
      ((CheckedLayout.row gap children).evaluateAt origin).box hEnv

theorem evaluateAt_column_immediateChildrenFitWithin
    (gap : Gap)
    (children : List CheckedLayout)
    (origin : Origin) :
    ImmediateChildrenFitWithin ((CheckedLayout.column gap children).evaluateAt origin) := by
  have hEnv :
      (stackEnvelopeBox .vertical gap origin 0 children).fitsWithin
        ((CheckedLayout.column gap children).evaluateAt origin).box := by
    rw [CheckedLayout.evaluateAt_box (CheckedLayout.column gap children) origin]
    simpa [stackEnvelopeBox, stackEnvelopeExtent, CheckedLayout.extent, ExactExtent.stack] using
      (Box.fitsWithin_refl { origin := origin, extent := (CheckedLayout.column gap children).extent })
  simpa [ImmediateChildrenFitWithin, CheckedLayout.evaluateAt] using
    evaluateChildrenAlong_childrenFitWithinParent .vertical gap origin 0 children
      ((CheckedLayout.column gap children).evaluateAt origin).box hEnv

theorem evaluateAt_padding_immediateChildrenFitWithin
    (insets : Insets)
    (child : CheckedLayout)
    (origin : Origin) :
    ImmediateChildrenFitWithin ((CheckedLayout.padding insets child).evaluateAt origin) := by
  simp [ImmediateChildrenFitWithin, ChildrenFitWithin, CheckedLayout.evaluateAt]
  rw [CheckedLayout.evaluateAt_box child (origin.translate insets.left insets.top)]
  have h := Box.translatedInsetFitsWithinExpanded origin child.extent insets
  simpa [CheckedLayout.extent] using h

theorem evaluateAt_frame_immediateChildrenFitWithin
    (extent : ExactExtent)
    (child : CheckedLayout)
    (origin : Origin)
    (h : child.extent.fitsWithin extent) :
    ImmediateChildrenFitWithin ((CheckedLayout.frame extent child).evaluateAt origin) := by
  simp [ImmediateChildrenFitWithin, ChildrenFitWithin, CheckedLayout.evaluateAt]
  rw [CheckedLayout.evaluateAt_box child origin]
  have h' := Box.sameOriginFitsWithin_of_extentFits origin h
  simpa [CheckedLayout.extent] using h'

mutual

theorem checkWithin_localSound :
    ∀ (available : AvailableSpace) (layout : Layout),
      match checkWithin available layout with
      | .exact checked => CheckedLayout.LocalSound checked.layout
      | .incompatible _ => True
  | available, .leaf extent => by
      by_cases fits : extent.fitsWithin available.extent
      · simp [checkWithin, fits, CheckedLayout.LocalSound]
      · simp [checkWithin, fits]
  | available, .row gap children => by
      cases hChildren : checkChildrenWithin available children with
      | incompatible error =>
          simp [checkWithin, hChildren]
      | exact checkedChildren =>
          by_cases fits :
              (CheckedLayout.row gap (CheckedWithin.childLayouts checkedChildren)).extent.fitsWithin
                available.extent
          · have hChildrenSound :
                CheckedLayout.LocalSounds (CheckedWithin.childLayouts checkedChildren) := by
              simpa [hChildren] using checkChildrenWithin_localSounds available children
            have hWithin :
                ImmediateChildrenFitWithin
                  (CheckedLayout.row gap (CheckedWithin.childLayouts checkedChildren)).evaluate := by
              simpa [CheckedLayout.evaluate] using
                evaluateAt_row_immediateChildrenFitWithin gap
                  (CheckedWithin.childLayouts checkedChildren) Origin.zero
            have hAdj :
                AdjacentSeparatedAlong .horizontal gap
                  (CheckedLayout.row gap (CheckedWithin.childLayouts checkedChildren)).evaluate.children := by
              simpa [CheckedLayout.evaluate] using
                evaluateAt_row_childrenAdjacentSeparated gap
                  (CheckedWithin.childLayouts checkedChildren) Origin.zero
            have hLocal :
                CheckedLayout.LocalSound
                  (CheckedLayout.row gap (CheckedWithin.childLayouts checkedChildren)) :=
              ⟨hWithin, ⟨hAdj, hChildrenSound⟩⟩
            simpa [checkWithin, hChildren, fits] using hLocal
          · simp [checkWithin, hChildren, fits]
  | available, .column gap children => by
      cases hChildren : checkChildrenWithin available children with
      | incompatible error =>
          simp [checkWithin, hChildren]
      | exact checkedChildren =>
          by_cases fits :
              (CheckedLayout.column gap (CheckedWithin.childLayouts checkedChildren)).extent.fitsWithin
                available.extent
          · have hChildrenSound :
                CheckedLayout.LocalSounds (CheckedWithin.childLayouts checkedChildren) := by
              simpa [hChildren] using checkChildrenWithin_localSounds available children
            have hWithin :
                ImmediateChildrenFitWithin
                  (CheckedLayout.column gap (CheckedWithin.childLayouts checkedChildren)).evaluate := by
              simpa [CheckedLayout.evaluate] using
                evaluateAt_column_immediateChildrenFitWithin gap
                  (CheckedWithin.childLayouts checkedChildren) Origin.zero
            have hAdj :
                AdjacentSeparatedAlong .vertical gap
                  (CheckedLayout.column gap (CheckedWithin.childLayouts checkedChildren)).evaluate.children := by
              simpa [CheckedLayout.evaluate] using
                evaluateAt_column_childrenAdjacentSeparated gap
                  (CheckedWithin.childLayouts checkedChildren) Origin.zero
            have hLocal :
                CheckedLayout.LocalSound
                  (CheckedLayout.column gap (CheckedWithin.childLayouts checkedChildren)) :=
              ⟨hWithin, ⟨hAdj, hChildrenSound⟩⟩
            simpa [checkWithin, hChildren, fits] using hLocal
          · simp [checkWithin, hChildren, fits]
  | available, .padding insets child => by
      cases hInset : available.extent.inset? insets with
      | none =>
          simp [checkWithin, hInset]
      | some innerExtent =>
          cases hChild : checkWithin { extent := innerExtent } child with
          | incompatible error =>
              simp [checkWithin, hInset, hChild]
          | exact checkedChild =>
              by_cases fits :
                  (CheckedLayout.padding insets checkedChild.layout).extent.fitsWithin available.extent
              · have hChildSound : CheckedLayout.LocalSound checkedChild.layout := by
                  simpa [hChild] using
                    checkWithin_localSound ({ extent := innerExtent } : AvailableSpace) child
                have hWithin :
                    ImmediateChildrenFitWithin
                      (CheckedLayout.padding insets checkedChild.layout).evaluate := by
                  simpa [CheckedLayout.evaluate] using
                    evaluateAt_padding_immediateChildrenFitWithin insets checkedChild.layout Origin.zero
                have hLocal :
                    CheckedLayout.LocalSound (CheckedLayout.padding insets checkedChild.layout) :=
                  ⟨hWithin, hChildSound⟩
                simpa [checkWithin, hInset, hChild, fits] using hLocal
              · simp [checkWithin, hInset, hChild, fits]
  | available, .frame extent child => by
      by_cases frameFits : extent.fitsWithin available.extent
      · cases hChild : checkWithin { extent := extent } child with
        | incompatible error =>
            simp [checkWithin, frameFits, hChild]
        | exact checkedChild =>
            have hChildSound : CheckedLayout.LocalSound checkedChild.layout := by
              simpa [hChild] using checkWithin_localSound ({ extent := extent } : AvailableSpace) child
            have hWithin :
                ImmediateChildrenFitWithin (CheckedLayout.frame extent checkedChild.layout).evaluate := by
              simpa [CheckedLayout.evaluate] using
                evaluateAt_frame_immediateChildrenFitWithin extent checkedChild.layout Origin.zero
                  checkedChild.fits
            have hLocal : CheckedLayout.LocalSound (CheckedLayout.frame extent checkedChild.layout) :=
              ⟨checkedChild.fits, ⟨hWithin, hChildSound⟩⟩
            simpa [checkWithin, frameFits, hChild] using hLocal
      · simp [checkWithin, frameFits]

theorem checkChildrenWithin_localSounds :
    ∀ (available : AvailableSpace) (children : List Layout),
      match checkChildrenWithin available children with
      | .exact checkedChildren => CheckedLayout.LocalSounds (CheckedWithin.childLayouts checkedChildren)
      | .incompatible _ => True
  | available, [] => by
      simp [checkChildrenWithin, CheckedWithin.childLayouts, CheckedLayout.LocalSounds]
  | available, child :: rest => by
      cases hChild : checkWithin available child with
      | incompatible error =>
          simp [checkChildrenWithin, hChild]
      | exact checkedChild =>
          cases hRest : checkChildrenWithin available rest with
          | incompatible error =>
              simp [checkChildrenWithin, hChild, hRest]
          | exact checkedRest =>
              have hChildSound : CheckedLayout.LocalSound checkedChild.layout := by
                simpa [hChild] using checkWithin_localSound available child
              have hRestSound : CheckedLayout.LocalSounds (CheckedWithin.childLayouts checkedRest) := by
                simpa [hRest] using checkChildrenWithin_localSounds available rest
              have hLocal :
                  CheckedLayout.LocalSounds (CheckedWithin.childLayouts (checkedChild :: checkedRest)) := by
                simpa [CheckedWithin.childLayouts, CheckedLayout.LocalSounds] using
                  (show CheckedLayout.LocalSound checkedChild.layout ∧
                      CheckedLayout.LocalSounds (CheckedWithin.childLayouts checkedRest) from
                    ⟨hChildSound, hRestSound⟩)
              simpa [checkChildrenWithin, hChild, hRest] using hLocal

end

theorem check_localSound
    (available : AvailableSpace)
    (layout : Layout) :
    match check available layout with
    | .exact checked => CheckedLayout.LocalSound checked.layout
    | .incompatible _ => True := by
  simpa [check] using checkWithin_localSound available layout

theorem check_localWitness
    (available : AvailableSpace)
    (layout : Layout) :
    match check available layout with
    | .exact checked => checked.layout.localWitness? = true
    | .incompatible _ => True := by
  cases h : check available layout with
  | incompatible error =>
      trivial
  | exact checked =>
      have hLocal : CheckedLayout.LocalSound checked.layout := by
        simpa [h] using check_localSound available layout
      exact localWitness?_complete checked.layout hLocal

theorem check_exact_localSound
    {available : AvailableSpace}
    {layout : Layout}
    {checked : CheckedWithin available}
    (h : check available layout = .exact checked) :
    CheckedLayout.LocalSound checked.layout := by
  simpa [h] using check_localSound available layout

theorem check_exact_localWitness
    {available : AvailableSpace}
    {layout : Layout}
    {checked : CheckedWithin available}
    (h : check available layout = .exact checked) :
    checked.layout.localWitness? = true := by
  simpa [h] using check_localWitness available layout

end CheckedLayout

end TypedLayout.Core
