import YangMills.Construction.FreeEnergiesOfTheFlow.MomentsOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses TorusFields RenormalizationStepParameters FreeEnergies
def scoredTowerColdResponseEq : Prop :=
  HoldsOnParameterFamilies fun Tb y => ∀ (β : ℝ) (k : ℕ) (T : StageTower (Tb.stepParameters y)) (S : ScoredStageTower T),
    S.FollowsFlow β k →
    ∀ (n : ℕ) [NeZero n], (Tb.stepParameters y).n₀ ≤ n → ∀ (z : TorusSite n) (W : TorusField n),
      IsCold (Tb.stepParameters y).threshold W →
      ∀ (f : FinePlaquetteFunction) (h : PlaquetteWeight (fineSide (Tb.stepParameters y).side k n)),
        (∀ p : TorusPlaquette (fineSide (Tb.stepParameters y).side k n), p.2.1 < p.2.2 → fineWeight f _ p = h p) →
        (S.setup k).cold n z W (fineWeight f _) =
          coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) S.coeffs k n z W h
end YangMills.Construction.ResponseInTheExpansion
end
