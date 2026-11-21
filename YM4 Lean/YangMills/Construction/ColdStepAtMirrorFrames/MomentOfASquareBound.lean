import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.Interpolation
namespace YangMills.Construction.ColdStepAtMirrorFrames
def lpMomentConstant (lam W₀ W : ℝ) (q : ℕ) : ℝ :=
  2 * (1 + 4 * W₀ / lam * (1 + ∏ k ∈ Finset.range q, (4 * (k : ℝ) + 8 * W)))
def momentBoundOfQuadraticBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ x lam κ W W₀ : ℝ) (d : ι → ι → ℝ)
    (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ) (p : ℝ → ℝ),
    0 < ρ → 0 < x → 0 < lam → 0 ≤ κ → 0 ≤ W → 0 ≤ W₀ → IsCutoff ρ p → IsPseudoMetricOnBonds d →
    IsUniformlyConvexDecaying ρ (x * lam / 4) κ d Ψ K →
    (∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W) →
    (∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * lam / 4) * ‖e‖) →
    ∀ (H : BondField ι → ℝ) (B A : ℝ) (w : ι → ℝ) (q : ℕ), 1 ≤ q → 0 ≤ B → 0 ≤ A → (∀ b, 0 ≤ w b) →
      ∑ b, w b ≤ W₀ * A → ContinuousOn H {η | ∀ b, ‖η b‖ < ρ} →
      (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |H η| ≤ B * (x * ∑ b, w b * ‖η b‖ ^ 2 + A)) →
      MomentBound (cutoffFactor ρ p) Ψ H q (lpMomentConstant lam W₀ W q * (B * A))
end YangMills.Construction.ColdStepAtMirrorFrames
end
