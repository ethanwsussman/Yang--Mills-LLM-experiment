import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
def CouplingFloorExists : Prop :=
  ∀ (c : ℝ) (L : ℕ) (rt : ℝ), 0 < c → ∃ y₀ : ℝ, ∀ x : ℝ, y₀ ≤ x →
    L ≤ clusterRange x ∧ (2 ^ 16 + 2 ^ 7 * rt) * (clusterRange x : ℝ) ^ 4 ≤ c * x
end YangMills.Construction.TorusLumps
end
