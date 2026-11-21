import YangMills.Construction.SixteenPointsOnASmallTorus.LevelsOfACopyDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def reflectedMomentErrorStatement : Prop :=
  ForAllLargeFloors fun T Kr y => ∀ Cs : ℕ → ℝ, (∀ p, 0 ≤ Cs p) → ∃ C : ℝ, 0 ≤ C ∧ ∀ Ξ : ℝ, y + 2 * T.B ≤ Ξ →
    ForAllInitialStages T y fun β hL z₀ => ∀ (K κ s : ℕ) (ρ H : ℝ) (Λ : NNReal)
      (h : TestFunctions.EuclideanFourSpace → ℝ),
      IsAdmissibleFlow (T.stepParameters y) Ξ β K → 2 ≤ κ → 0 < ρ → ρ ≤ cellLength T.side K κ / 4 →
      IsLocalizedSource (cellLength T.side K κ) ρ H Λ h → radiusLevel (T.stepParameters y) β K ρ = some s →
      ResponseInTheExpansion.StagesOnFlowUpTo T Kr y β hL z₀ s →
      ResponseInTheExpansion.momentError hL T.lam (ResponseInTheExpansion.couplingsAlongFlow (T.stepParameters y) β) z₀
          T.gasRate Cs (radiusInStageUnits T.side K ρ) s (twoCellSide T.side κ s) Finset.univ
          (reflectedWeightsAtStage T y β hL z₀ K κ s (twoCellSide T.side κ s) h) ≤ C
end YangMills.Construction.SmallTorusCopies
end
