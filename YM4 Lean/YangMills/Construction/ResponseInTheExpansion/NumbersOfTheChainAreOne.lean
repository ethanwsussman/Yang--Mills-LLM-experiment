import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open RenormalizationStepParameters WeightedResponses
def chainResponseCoeffsUnique : Prop :=
  HoldsOnParameterFamilies fun Tb y => ∀ K K' : ResponseParameters, K.Admissible (Tb.stepParameters y) →
    K'.Admissible (Tb.stepParameters y) →
    ∀ (β : ℝ) (k : ℕ) (al al' : ℕ → ℝ), (∀ j ≤ k, y ≤ flowCouplings (Tb.stepParameters y) β j) →
      IsChainResponseCoeff (Tb.stepParameters y) K β k al → IsChainResponseCoeff (Tb.stepParameters y) K' β k al' →
      ∀ j ≤ k, al j = al' j
end YangMills.Construction.ResponseInTheExpansion
end
