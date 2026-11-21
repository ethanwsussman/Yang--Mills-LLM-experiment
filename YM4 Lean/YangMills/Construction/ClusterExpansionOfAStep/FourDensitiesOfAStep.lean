import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.FormsOfAFamily
import YangMills.Construction.ColdStepAtMirrorFrames.DensityHypothesesAtParameters
import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusLumps ColdStepAtMirrorFrames
def ExpansionDensityBoundsOfColdStep : Prop :=
  ∀ ℓ : TorusLumps.StepParameters, ℓ.Admissible → ℓ.n₁ = (ℓ.side : ℝ) ^ (1 / 640 : ℝ) →
    ∀ (t : ℕ) (a ρA ρ lam x δ₂ Ct Cs CE e₀ : ℝ) (p : ℝ → ℝ) (f : LocalFamily) (u s τ : TopLevelFamily)
      (g : LocalDensity), 0 ≤ e₀ →
      ColdStepDensityConditions a ρA ρ lam x ℓ.threshold ℓ.rt (ℓ.rt / 2 ^ 10) δ₂ ℓ.E ℓ.E₃ Ct Cs CE ℓ.side t ℓ.n₀
        p f u s τ →
      IsSmallDensity ℓ e₀ g →
      ExpansionDensityBounds ℓ Cs CE (Ct * x * Real.exp (-(δ₂ / 8 * frameRadius x))) (2 * e₀) x
        (densityOfTopFamily ℓ.side t u) (densityOfTopFamily ℓ.side t s) (densityOfTopFamily ℓ.side t τ) g
end YangMills.Construction.ClusterExpansionOfAStep
end
