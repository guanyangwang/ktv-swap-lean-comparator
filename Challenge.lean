import ChallengeDefs

namespace KTV.Johnson.MathlibOnly

universe uMain

/--
Comparator challenge for the Mathlib-only statement surface.  The imported
dependency file contains only `import Mathlib`; this file contributes only the
statement hole.
-/
theorem binaryFixedMarginLazySwapChain_spectralGap_card
    {Row Col : Type uMain}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    [Nonempty (OrderedDistinctPair Row)]
    [Nonempty (OrderedDistinctPair Col)]
    (M : FixedMarginModel Row Col) [Nonempty (FixedMarginState M)] :
    OperatorSpectralGapAtLeast
      (Ω := FixedMarginState M)
      (fixedMarginOrderedDistinctRectangleLazySwapOperator M)
      (((1 : Rat) / ((Fintype.card Col).choose 2 : Rat)) *
        ((1 : Rat) / ((Fintype.card Row).choose 2 : Rat))) := by
  sorry

end KTV.Johnson.MathlibOnly
