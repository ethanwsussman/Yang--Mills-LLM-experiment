import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChainResponses
open YangMills.Construction.ResponseInTheExpansion YangMills.Construction.WeightedResponses
def chainResponseCoeffNearOneStatement : Prop :=
  HoldsOnParameterFamilies fun Tb y => ∀ Kr : ResponseParameters, Kr.Admissible (Tb.stepParameters y) →
    ∀ (β : ℝ) (k : ℕ) (al : ℕ → ℝ),
    (∀ j ≤ k, y ≤ flowCouplings (Tb.stepParameters y) β j) → IsChainResponseCoeff (Tb.stepParameters y) Kr β k al →
      |al k - 1| ≤ 1 / 4
end YangMills.Construction.ChainResponses
end
