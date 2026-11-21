import YangMills.Construction.FreeEnergiesOfTheFlow.MomentsOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusLumps FreeEnergies WeightedResponses
def scoredTowerCoeffsAreChainStatement : Prop :=
  HoldsOnParameterFamilies fun Tb y => ∀ (β : ℝ) (k : ℕ) (T : StageTower (Tb.stepParameters y)) (S : ScoredStageTower T),
    S.FollowsFlow β k → IsChainResponseCoeff (Tb.stepParameters y) S.params β k S.coeffs
end YangMills.Construction.ResponseInTheExpansion
end
