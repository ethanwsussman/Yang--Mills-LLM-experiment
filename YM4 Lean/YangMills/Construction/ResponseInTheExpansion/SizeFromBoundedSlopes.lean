import YangMills.Construction.ColdStepAtMirrorFrames.MomentOfASquareBound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace WeightedResponses
def LocalSizeOfBoundedPartials : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {ρ x lam κ W : ℝ} {d : ι → ι → ℝ}
    {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} {p : ℝ → ℝ}, 0 < ρ → 0 < x → 0 < lam → 0 ≤ κ →
    0 ≤ W → IsCutoff ρ p → IsPseudoMetricOnBonds d → IsUniformlyConvexDecaying ρ (x * lam / 4) κ d Ψ K →
    (∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W) →
    (∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * lam / 4) * ‖e‖) →
    ∀ {J : BondField ι → ℝ} {Dd dZ : ι → ℝ} {h : ℝ}, ContDiffOn ℝ 1 J {η | ∀ b, ‖η b‖ < ρ} → (∀ b, 0 ≤ Dd b) →
    0 ≤ h → (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |J η - J 0| ≤ ∑ b, ‖η b‖ * Dd b) →
    (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm J b η ≤ Dd b) →
    x ^ (-(1 / 2) : ℝ) * ∑ b, Dd b ≤ h →
    (∀ b, Dd b ≤ Real.sqrt x * h * Real.exp (-(2 * κ * dZ b))) →
    HasLocalSize ρ (cutoffFactor ρ p) Ψ (fun q => lpMomentConstant lam (1 / 2) W q * 1) x κ h dZ J
end WeightedResponses
end YangMills.Construction
end
