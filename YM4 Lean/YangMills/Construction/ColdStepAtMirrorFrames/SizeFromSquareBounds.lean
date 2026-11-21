import YangMills.Construction.ColdStepAtMirrorFrames.MomentOfASquareBound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages YangMills.Construction.Interpolation
def IsQuadraticallyBoundedOnBalls {ι : Type} [Fintype ι] (ρ x W₀ B a : ℝ) (H : BondField ι → ℝ) : Prop :=
  ∃ (w : ι → ℝ) (A : ℝ), 0 ≤ A ∧ A ≤ a ∧ (∀ b, 0 ≤ w b) ∧ ∑ b, w b ≤ W₀ * A ∧
    ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |H η| ≤ B * (x * ∑ b, w b * ‖η b‖ ^ 2 + A)
def LocalSizeOfQuadraticBounds : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ x lam κ W W₀ : ℝ) (d : ι → ι → ℝ)
    (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ) (p : ℝ → ℝ),
    0 < ρ → 0 < x → 0 < lam → 0 ≤ κ → 0 ≤ W → 0 ≤ W₀ → IsCutoff ρ p → IsPseudoMetricOnBonds d →
    IsUniformlyConvexDecaying ρ (x * lam / 4) κ d Ψ K →
    (∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W) →
    (∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * lam / 4) * ‖e‖) →
    ∀ (H : BondField ι → ℝ) (B h : ℝ) (dZ : ι → ℝ), 0 ≤ B → 0 ≤ h →
      ContDiffOn ℝ 1 H {η | ∀ b, ‖η b‖ < ρ} →
      IsQuadraticallyBoundedOnBalls ρ x W₀ B h H →
      (∀ b, IsQuadraticallyBoundedOnBalls ρ x W₀ (Real.sqrt x * B) (h * Real.exp (-(2 * κ * dZ b))) (bondGradNorm H b)) →
      HasLocalSize ρ (cutoffFactor ρ p) Ψ (fun q => lpMomentConstant lam W₀ W q * B) x κ h dZ H
end YangMills.Construction.ColdStepAtMirrorFrames
end
