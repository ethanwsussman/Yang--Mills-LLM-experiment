import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionAlongAMotion
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.Estimates
namespace YangMills.Construction.ColdStepAtMirrorFrames
def SecondOrderAlongMotionFormula : Prop :=
  ∀ (F : BlockFrame) (j : ℕ) (T : Finset (F.Site j × Fin 4)) (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (α : (Fin 2 → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions) (u₀ u₁ : F.Site j → Fin 4 → ℝ)
    (X₀ X₁ : imaginaryQuaternions),
    (∀ b, b ∈ T) → ContDiffThreeAlongBonds G W →
    (∀ (c : Fin 1 → F.Site j × Fin 4) (X : Fin 1 → imaginaryQuaternions), AreUnitVectors X → bondDeriv G W c X = 0) →
    (∀ x b, α 0 x b = 0) → (∀ x b, ContDiffAt ℝ 3 (fun τ => α τ x b) 0) →
    (∀ x b, motionComponent α ![0] x b = u₀ x b • X₀) → (∀ x b, motionComponent α ![1] x b = u₁ x b • X₁) →
    iteratedFDeriv ℝ 2 (fun τ => G (leftTranslate (α τ) W)) 0 ![Pi.single 0 1, Pi.single 1 1] =
      ∑ b ∈ T, ∑ b' ∈ T, bondDeriv G W ![b, b'] ![X₀, X₁] * u₀ b.1 b.2 * u₁ b'.1 b'.2
end YangMills.Construction.ColdStepAtMirrorFrames
end
