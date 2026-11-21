import YangMills.Construction.ColdStepAtMirrorFrames.MomentOfASquareBound
import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
def localSizeOfQuadraticBoundsStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ x lam κ W W₀ C h H₀ : ℝ) (d : ι → ι → ℝ)
    (Φ : BondField ι → ℝ) (p : ℝ → ℝ) (dZ w : ι → ℝ) (H : BondField ι → ℝ),
    0 < ρ → 1 ≤ x → 0 < lam → 0 ≤ κ → 0 ≤ W → 0 ≤ W₀ → 0 ≤ h → IsCutoff ρ p → IsPseudoMetricOnBonds d →
    HasUniformlyConvexLaw ρ lam x κ C d Φ →
    (∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W) →
    (∀ b, 0 ≤ w b) → ∑ b, w b ≤ W₀ →
    (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) H η) →
    (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |H η - H₀| ≤ h * (x * ∑ b, w b * ‖η b‖ ^ 2 + 1)) →
    (∀ (η : BondField ι) (b : ι), (∀ b, ‖η b‖ < ρ) →
      bondGradNorm H b η ≤ Real.sqrt x * h * Real.exp (-(2 * κ * dZ b)) * (x * ∑ b, w b * ‖η b‖ ^ 2 + 1)) →
    HasLocalSize ρ (cutoffFactor ρ p) Φ (lpMomentConstant lam W₀ W) x κ h dZ H
end Interpolation
end YangMills.Construction
end
