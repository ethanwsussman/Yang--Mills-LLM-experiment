import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.DilationOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def ScalingCommutesWithSmoothingIter : Prop :=
  ∀ (L n k j : ℕ) (hL : 0 < L) (hj : j ≤ k), Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    1 ≤ j → ∀ l ≤ j, ∀ U ∈ fieldSpace L n k 0,
      transportTotal (scaleEdge hL hj l) (smoothingIter L n k l U) =
        smoothingIter L (scaledExponent n k j) j l (transportTotal (scaleEdge hL hj 0) U)
end YangMills.Construction.Tower
end
