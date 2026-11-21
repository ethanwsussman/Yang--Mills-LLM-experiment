import YangMills.Construction.LawByMomentsOfTheFlow.TestFunctionsAcrossTheLevels
import YangMills.Construction.ResponseInTheExpansion.TorusBoundOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelTestFunctions
open TorusLumps WeightedResponses
def CouplingFlowAboveWindow : Prop :=
  ∀ ℓ : StepParameters, AdmissibleStep ℓ → ∀ g : ℝ, 0 < g → ℓ.y₁ ≤ (g ^ 2)⁻¹ →
    ∀ (β : ℝ) (K : ℕ), couplingWindowTop ℓ g ≤ β →
    IsFirstPassage ℓ (couplingWindowTop ℓ g) β K →
    (∀ j ≤ K, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) ∧
    ∀ u v : ℕ, u ≤ v → v ≤ K → |(couplingFlow ℓ β v).1 - (couplingFlow ℓ β u).1| ≤ 2 * ℓ.B * ((v : ℝ) - (u : ℝ))
end YangMills.Construction.LevelTestFunctions
end
