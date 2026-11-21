import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open ColdStepAtMirrorFrames
namespace Estimates
def cutoffDerivMomentsStatement : Prop :=
  ∀ (ρ : ℝ) (p : ℝ → ℝ) (lam C W : ℝ), 0 < ρ → IsCutoff ρ p → 0 < lam → 0 ≤ C → 0 ≤ W →
    ∀ j q N : ℕ, 1 ≤ j → 1 ≤ q → ∃ K₀ : ℝ, 0 ≤ K₀ ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x κ : ℝ) (d : ι → ι → ℝ) (Ψ : BondField ι → ℝ)
        (K : ι → ι → ℝ), 1 ≤ x → 0 ≤ κ → IsPseudoMetricOnBonds d →
        IsUniformlyConvexDecaying ρ (x * lam / 4) κ d Ψ K →
        (∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W) →
        (∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * lam / 4) * ‖e‖) →
        (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ (b : ι) (e : BondVector),
          |bondPartialDeriv Ψ b η e| ≤ C * x * ‖e‖) →
        ∀ b : ι, Integrable (fun η => |iteratedDeriv j p ‖η b‖| ^ q * ballDensity (cutoffFactor ρ p) Ψ η) ∧
          ballExpectation (cutoffFactor ρ p) Ψ (fun η => |iteratedDeriv j p ‖η b‖| ^ q) ≤ K₀ * (x ^ N)⁻¹
end Estimates
end YangMills.Construction
end
