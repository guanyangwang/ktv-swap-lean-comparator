import Mathlib

open scoped BigOperators

namespace KTV.Johnson.MathlibOnly

universe uRow uCol

/-!
Mathlib-only definitions needed to state the fixed-margin lazy swap-chain
spectral-gap theorem.
-/

abbrev BinaryMatrix (Row : Type uRow) (Col : Type uCol) :=
  Row → Col → Bool

def rowSum {Row : Type uRow} {Col : Type uCol}
    [Fintype Col] (X : BinaryMatrix Row Col) (r : Row) : Nat :=
  (Finset.univ.filter fun c : Col => X r c = true).card

def colSum {Row : Type uRow} {Col : Type uCol}
    [Fintype Row] (X : BinaryMatrix Row Col) (c : Col) : Nat :=
  (Finset.univ.filter fun r : Row => X r c = true).card

structure FixedMarginModel (Row : Type uRow) (Col : Type uCol)
    [Fintype Row] [DecidableEq Row] [Fintype Col] [DecidableEq Col] where
  rowTarget : Row → Nat
  colTarget : Col → Nat

def FixedMarginModel.IsState {Row : Type uRow} {Col : Type uCol}
    [Fintype Row] [DecidableEq Row] [Fintype Col] [DecidableEq Col]
    (M : FixedMarginModel Row Col) (X : BinaryMatrix Row Col) : Prop :=
  (∀ r, rowSum X r = M.rowTarget r) ∧
    ∀ c, colSum X c = M.colTarget c

abbrev FixedMarginState {Row : Type uRow} {Col : Type uCol}
    [Fintype Row] [DecidableEq Row] [Fintype Col] [DecidableEq Col]
    (M : FixedMarginModel Row Col) :=
  {X : BinaryMatrix Row Col // M.IsState X}

noncomputable instance instFintypeFixedMarginState
    {Row : Type uRow} {Col : Type uCol}
    [Fintype Row] [DecidableEq Row] [Fintype Col] [DecidableEq Col]
    (M : FixedMarginModel Row Col) : Fintype (FixedMarginState M) := by
  classical
  unfold FixedMarginState
  infer_instance

noncomputable instance instDecidableEqFixedMarginState
    {Row : Type uRow} {Col : Type uCol}
    [Fintype Row] [DecidableEq Row] [Fintype Col] [DecidableEq Col]
    (M : FixedMarginModel Row Col) : DecidableEq (FixedMarginState M) := by
  classical
  infer_instance

abbrev OrderedDistinctPair (α : Type*) :=
  {p : α × α // p.1 ≠ p.2}

def boolFlip (b : Bool) : Bool :=
  !b

def switchableRowsCols {Row : Type uRow} {Col : Type uCol}
    (X : BinaryMatrix Row Col) (r₁ r₂ : Row) (c₁ c₂ : Col) : Prop :=
  r₁ ≠ r₂ ∧ c₁ ≠ c₂ ∧
    ((X r₁ c₁ = true ∧ X r₁ c₂ = false ∧
        X r₂ c₁ = false ∧ X r₂ c₂ = true) ∨
      (X r₁ c₁ = false ∧ X r₁ c₂ = true ∧
        X r₂ c₁ = true ∧ X r₂ c₂ = false))

def swapToggle {Row : Type uRow} {Col : Type uCol}
    [DecidableEq Row] [DecidableEq Col]
    (X : BinaryMatrix Row Col) (r₁ r₂ : Row) (c₁ c₂ : Col) :
    BinaryMatrix Row Col :=
  fun r c =>
    if (r = r₁ ∧ c = c₁) ∨ (r = r₁ ∧ c = c₂) ∨
        (r = r₂ ∧ c = c₁) ∨ (r = r₂ ∧ c = c₂) then
      boolFlip (X r c)
    else
      X r c

noncomputable def swapStep {Row : Type uRow} {Col : Type uCol}
    [DecidableEq Row] [DecidableEq Col]
    (X : BinaryMatrix Row Col) (r₁ r₂ : Row) (c₁ c₂ : Col) :
    BinaryMatrix Row Col := by
  classical
  exact if switchableRowsCols X r₁ r₂ c₁ c₂ then
    swapToggle X r₁ r₂ c₁ c₂
  else
    X

noncomputable def fixedMarginOrderedDistinctRectangleStepOnState
    {Row : Type uRow} {Col : Type uCol}
    [Fintype Row] [DecidableEq Row] [Fintype Col] [DecidableEq Col]
    (M : FixedMarginModel Row Col)
    (i : OrderedDistinctPair Row × OrderedDistinctPair Col)
    (X : FixedMarginState M) : FixedMarginState M := by
  classical
  let rp := i.1
  let cp := i.2
  let Y := swapStep X.1 rp.1.1 rp.1.2 cp.1.1 cp.1.2
  exact if hY : M.IsState Y then ⟨Y, hY⟩ else X

noncomputable def fixedMarginOrderedDistinctRectangleSwapOperator
    {Row : Type uRow} {Col : Type uCol}
    [Fintype Row] [DecidableEq Row] [Fintype Col] [DecidableEq Col]
    [Nonempty (OrderedDistinctPair Row)]
    [Nonempty (OrderedDistinctPair Col)]
    (M : FixedMarginModel Row Col) :
    (FixedMarginState M → Rat) → (FixedMarginState M → Rat) :=
  fun f X =>
    (∑ i : OrderedDistinctPair Row × OrderedDistinctPair Col,
        f (fixedMarginOrderedDistinctRectangleStepOnState M i X)) /
      (Fintype.card (OrderedDistinctPair Row × OrderedDistinctPair Col) : Rat)

noncomputable def fixedMarginOrderedDistinctRectangleLazySwapOperator
    {Row : Type uRow} {Col : Type uCol}
    [Fintype Row] [DecidableEq Row] [Fintype Col] [DecidableEq Col]
    [Nonempty (OrderedDistinctPair Row)]
    [Nonempty (OrderedDistinctPair Col)]
    (M : FixedMarginModel Row Col) :
    (FixedMarginState M → Rat) → (FixedMarginState M → Rat) :=
  fun f X =>
    ((1 : Rat) / 2) * f X +
      ((1 : Rat) / 2) *
        fixedMarginOrderedDistinctRectangleSwapOperator M f X

noncomputable def finiteInner {Ω : Type*} [Fintype Ω]
    (f g : Ω → Rat) : Rat :=
  ∑ x : Ω, f x * g x

def finiteMeanZero {Ω : Type*} [Fintype Ω] (f : Ω → Rat) : Prop :=
  ∑ x : Ω, f x = 0

noncomputable def finiteOperatorDirichlet {Ω : Type*} [Fintype Ω]
    (T : (Ω → Rat) → (Ω → Rat)) (f : Ω → Rat) : Rat :=
  finiteInner f f - finiteInner f (T f)

def OperatorSpectralGapAtLeast {Ω : Type*} [Fintype Ω]
    (T : (Ω → Rat) → (Ω → Rat)) (gap : Rat) : Prop :=
  ∀ f : Ω → Rat, finiteMeanZero f →
    gap * finiteInner f f ≤ finiteOperatorDirichlet T f

end KTV.Johnson.MathlibOnly
