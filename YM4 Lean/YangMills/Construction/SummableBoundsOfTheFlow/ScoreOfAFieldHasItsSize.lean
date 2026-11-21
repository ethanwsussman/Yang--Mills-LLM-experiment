import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongAField
import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace BondIntegration
def fieldScoreSizeStatement : Prop :=
  ∀ (ρ : ℝ) (p : ℝ → ℝ) (Cr : ℕ → ℕ → ℕ → ℝ) (lam W W₀ : ℝ), 0 < ρ → IsCutoff ρ p → 0 < lam → 0 ≤ W → 0 ≤ W₀ →
    ∃ Cq : ℕ → ℝ, (∀ q, 0 ≤ Cq q) ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x κ C A u : ℝ) (d : ι → ι → ℝ) (Ψ : BondField ι → ℝ) (b : ι)
        (w : ι → ℝ) (z : BondVector → BondVector),
        1 ≤ x → 0 ≤ κ → 0 ≤ A → 0 ≤ u → IsPseudoMetricOnBonds d → ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) Ψ →
        HasUniformlyConvexLaw ρ lam x κ C d Ψ → (∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W) →
        (∀ (j q N : ℕ) (b' : ι), 1 ≤ j → 1 ≤ q →
          MeasureTheory.Integrable (fun η => |iteratedDeriv j p ‖η b'‖| ^ q * ballDensity (cutoffFactor ρ p) Ψ η) ∧
          ballExpectation (cutoffFactor ρ p) Ψ (fun η => |iteratedDeriv j p ‖η b'‖| ^ q) ≤ Cr j q N * (x ^ N)⁻¹) →
        (∀ b', 0 ≤ w b') → ∑ b', w b' ≤ W₀ →
        (∀ (η : BondField ι) (e : BondVector), (∀ b, ‖η b‖ < ρ) →
          |bondPartialDeriv Ψ b η e| ≤ A * Real.sqrt x * (x * ∑ b', w b' * ‖η b'‖ ^ 2 + 1) * ‖e‖) →
        (∀ (η : BondField ι) (b' : ι) (e e' : BondVector), (∀ b, ‖η b‖ < ρ) →
          |secondDerivAlong Ψ η (bondVariation b e) (bondVariation b' e')| ≤ A * x * Real.exp (-(2 * κ * d b' b)) * ‖e‖ * ‖e'‖) →
        (∀ v : BondVector, ‖v‖ < ρ → ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) z v ∧ ‖z v‖ ≤ u ∧ ‖fderiv ℝ z v‖ ≤ u ∧
          ∀ e e' : BondVector, ‖fderiv ℝ (fun v' => fderiv ℝ z v' e') v e‖ ≤ u * ‖e‖ * ‖e'‖) →
        ContDiffOn ℝ 1 (fieldScore p Ψ b z) {η | ∀ b, ‖η b‖ < ρ} ∧
        HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ ((2 * A + 4) * Real.sqrt x * u) (fun b' => d b' b) (fieldScore p Ψ b z)
end BondIntegration
end YangMills.Construction
end
