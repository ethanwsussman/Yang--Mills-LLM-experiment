import YangMills.Construction.ColdChainAtEveryLevel.MixedDerivativesOfABoundedExtension
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Analytic
open Metric
def mixedDerivativeOfSecondDifferencesStatement : Prop :=
  ∀ (m k : ℕ) (G : (Fin m → ℂ) → ℂ) (ρ M : ℝ) (v : Fin (k + 2) → Fin m → ℂ) (i₁ i₂ : Fin (k + 2)), i₁ ≠ i₂ → 0 < ρ →
    0 ≤ M → AnalyticOnNhd ℂ G (ball 0 ρ) →
    (∀ t ∈ ball (0 : Fin m → ℂ) ρ, ∃ δ : ℝ, 0 < δ ∧ ∀ τ₁ τ₂ : ℂ, ‖τ₁‖ < δ → ‖τ₂‖ < δ →
      ‖G (t + τ₁ • v i₁ + τ₂ • v i₂) - G (t + τ₁ • v i₁) - G (t + τ₂ • v i₂) + G t‖ ≤ M * ‖τ₁‖ * ‖τ₂‖) →
    ‖iteratedFDeriv ℂ (k + 2) G 0 v‖ ≤
      YangMills.Construction.Analytic.cauchyHalvingConstant k * M / ρ ^ k *
        ∏ l ∈ (Finset.univ.erase i₁).erase i₂, ‖v l‖
end Analytic
end YangMills.Construction
end
