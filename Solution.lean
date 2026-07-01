import ChallengeDefs
import KTV.Johnson.MainTheorems

open scoped BigOperators

namespace KTV.Johnson.MathlibOnly

universe uMain

noncomputable def toKTVModel
    {Row Col : Type uMain} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (M : FixedMarginModel Row Col) :
    KTV.Johnson.FixedMarginModel Row Col where
  rowTarget := M.rowTarget
  colTarget := M.colTarget

theorem toKTVModel_isState_iff
    {Row Col : Type uMain} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (M : FixedMarginModel Row Col) (X : BinaryMatrix Row Col) :
    (toKTVModel M).IsState X ↔ M.IsState X := by
  unfold toKTVModel KTV.Johnson.FixedMarginModel.IsState
    FixedMarginModel.IsState KTV.Johnson.rowSum rowSum KTV.Johnson.colSum colSum
  rfl

noncomputable def stateEquiv
    {Row Col : Type uMain} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (M : FixedMarginModel Row Col) :
    FixedMarginState M ≃ KTV.Johnson.FixedMarginState (toKTVModel M) where
  toFun X := ⟨X.1, (toKTVModel_isState_iff M X.1).2 X.2⟩
  invFun X := ⟨X.1, (toKTVModel_isState_iff M X.1).1 X.2⟩
  left_inv X := by
    ext r c
    rfl
  right_inv X := by
    ext r c
    rfl

theorem ktv_swapStep_eq
    {Row Col : Type uMain} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (X : BinaryMatrix Row Col) (r₁ r₂ : Row) (c₁ c₂ : Col) :
    KTV.Johnson.swapStep X r₁ r₂ c₁ c₂ = swapStep X r₁ r₂ c₁ c₂ := by
  unfold KTV.Johnson.swapStep swapStep KTV.Johnson.switchableRowsCols
    switchableRowsCols KTV.Johnson.swapToggle swapToggle
    KTV.Johnson.boolFlip boolFlip
  rfl

theorem stateEquiv_stepOnState
    {Row Col : Type uMain} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (M : FixedMarginModel Row Col)
    (i : OrderedDistinctPair Row × OrderedDistinctPair Col)
    (X : FixedMarginState M) :
    stateEquiv M (fixedMarginOrderedDistinctRectangleStepOnState M i X) =
      (KTV.Johnson.FixedMarginSwapProposalData.allOrderedDistinctRectangles
        (toKTVModel M)).stepOnState i (stateEquiv M X) := by
  classical
  let Y := swapStep X.1 i.1.1.1 i.1.1.2 i.2.1.1 i.2.1.2
  have hYK :
      (toKTVModel M).IsState Y := by
    change
      (toKTVModel M).IsState
        (swapStep X.1 i.1.1.1 i.1.1.2 i.2.1.1 i.2.1.2)
    rw [← ktv_swapStep_eq]
    exact
      KTV.Johnson.swapStep_preserves_fixedMargins
        (toKTVModel M) X.1 i.1.1.1 i.1.1.2 i.2.1.1 i.2.1.2
        ((toKTVModel_isState_iff M X.1).2 X.2)
  have hY : M.IsState Y :=
    (toKTVModel_isState_iff M Y).1 hYK
  apply Subtype.ext
  simp [stateEquiv, fixedMarginOrderedDistinctRectangleStepOnState, Y, hY,
    KTV.Johnson.FixedMarginSwapProposalData.stepOnState,
    KTV.Johnson.FixedMarginSwapProposalData.allOrderedDistinctRectangles,
    KTV.Johnson.FixedMarginSwapProposalData.ofRectangles,
    ktv_swapStep_eq]

theorem transport_swapOperator_eq
    {Row Col : Type uMain} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    [Nonempty (OrderedDistinctPair Row)]
    [Nonempty (OrderedDistinctPair Col)]
    (M : FixedMarginModel Row Col) :
    KTV.Johnson.transportOperator (stateEquiv M).symm
      (KTV.Johnson.fixedMarginOrderedDistinctRectangleSwapOperator
        (toKTVModel M)) =
      fixedMarginOrderedDistinctRectangleSwapOperator M := by
  classical
  funext f X
  unfold KTV.Johnson.transportOperator KTV.Johnson.pushFunction
    KTV.Johnson.pullFunction
  have hAvg :=
    congrFun
      (KTV.Johnson.fixedMarginOrderedDistinctRectangleSwapKernel_apply_eq_averageOperator
        (M := toKTVModel M)
        (fun Y : KTV.Johnson.FixedMarginState (toKTVModel M) =>
          f ((stateEquiv M).symm Y)))
      (stateEquiv M X)
  change
    KTV.Johnson.fixedMarginOrderedDistinctRectangleSwapOperator (toKTVModel M)
        (fun Y : KTV.Johnson.FixedMarginState (toKTVModel M) =>
          f ((stateEquiv M).symm Y)) (stateEquiv M X) =
      fixedMarginOrderedDistinctRectangleSwapOperator M f X
  unfold KTV.Johnson.fixedMarginOrderedDistinctRectangleSwapOperator
  rw [hAvg]
  unfold KTV.Johnson.averageOperator fixedMarginOrderedDistinctRectangleSwapOperator
  apply congrArg (fun z => z / (Fintype.card
    (OrderedDistinctPair Row × OrderedDistinctPair Col) : Rat))
  apply Finset.sum_congr rfl
  intro i _
  have hStep := congrArg (fun Y => (stateEquiv M).symm Y)
    (stateEquiv_stepOnState M i X)
  simpa using congrArg f hStep.symm

theorem transport_lazyOperator_eq
    {Row Col : Type uMain} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    [Nonempty (OrderedDistinctPair Row)]
    [Nonempty (OrderedDistinctPair Col)]
    (M : FixedMarginModel Row Col) :
    KTV.Johnson.transportOperator (stateEquiv M).symm
      (KTV.Johnson.fixedMarginOrderedDistinctRectangleLazySwapOperator
        (toKTVModel M)) =
      fixedMarginOrderedDistinctRectangleLazySwapOperator M := by
  classical
  funext f X
  unfold KTV.Johnson.transportOperator KTV.Johnson.pushFunction
  have hLazy :=
    congrFun
      (KTV.Johnson.fixedMarginOrderedDistinctRectangleLazySwapOperator_apply_eq_operatorConvexCombination
        (M := toKTVModel M)
        (KTV.Johnson.pullFunction (stateEquiv M).symm f))
      (stateEquiv M X)
  change
    KTV.Johnson.fixedMarginOrderedDistinctRectangleLazySwapOperator (toKTVModel M)
        (KTV.Johnson.pullFunction (stateEquiv M).symm f) (stateEquiv M X) =
      fixedMarginOrderedDistinctRectangleLazySwapOperator M f X
  rw [hLazy]
  have hSwapPoint :
      KTV.Johnson.fixedMarginOrderedDistinctRectangleSwapOperator (toKTVModel M)
          (KTV.Johnson.pullFunction (stateEquiv M).symm f) (stateEquiv M X) =
        fixedMarginOrderedDistinctRectangleSwapOperator M f X := by
    simpa [KTV.Johnson.transportOperator, KTV.Johnson.pushFunction] using
      congrFun (congrFun (transport_swapOperator_eq M) f) X
  unfold KTV.Johnson.operatorConvexCombination
  rw [hSwapPoint]
  unfold KTV.Johnson.pullFunction
    fixedMarginOrderedDistinctRectangleLazySwapOperator
  simp only [Equiv.symm_apply_apply]
  ring

theorem binaryFixedMarginLazySwapChain_spectralGap_card
    {Row Col : Type uMain} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    [Nonempty (OrderedDistinctPair Row)]
    [Nonempty (OrderedDistinctPair Col)]
    (M : FixedMarginModel Row Col) [Nonempty (FixedMarginState M)] :
    OperatorSpectralGapAtLeast
      (Ω := FixedMarginState M)
      (fixedMarginOrderedDistinctRectangleLazySwapOperator M)
      (((1 : Rat) / ((Fintype.card Col).choose 2 : Rat)) *
        ((1 : Rat) / ((Fintype.card Row).choose 2 : Rat))) := by
  classical
  letI : Nonempty (KTV.Johnson.FixedMarginState (toKTVModel M)) :=
    ⟨stateEquiv M (Classical.choice (inferInstance :
      Nonempty (FixedMarginState M)))⟩
  have hKTV :
      KTV.Johnson.OperatorSpectralGapAtLeast
        (Ω := KTV.Johnson.FixedMarginState (toKTVModel M))
        (KTV.Johnson.fixedMarginOrderedDistinctRectangleLazySwapOperator
          (toKTVModel M))
        (((1 : Rat) / ((Fintype.card Col).choose 2 : Rat)) *
          ((1 : Rat) / ((Fintype.card Row).choose 2 : Rat))) :=
    KTV.Johnson.fixedMarginOrderedDistinctRectangleLazySwapOperator_gap_card
      (toKTVModel M)
  have hTransport :=
    KTV.Johnson.operatorSpectralGapAtLeast_transport
      (Ω := KTV.Johnson.FixedMarginState (toKTVModel M))
      (Ω' := FixedMarginState M)
      (e := (stateEquiv M).symm)
      hKTV
  rw [transport_lazyOperator_eq M] at hTransport
  simpa [OperatorSpectralGapAtLeast, KTV.Johnson.OperatorSpectralGapAtLeast,
    finiteInner, KTV.Johnson.finiteInner,
    finiteMeanZero, KTV.Johnson.finiteMeanZero,
    finiteOperatorDirichlet, KTV.Johnson.finiteOperatorDirichlet] using
    hTransport

end KTV.Johnson.MathlibOnly
