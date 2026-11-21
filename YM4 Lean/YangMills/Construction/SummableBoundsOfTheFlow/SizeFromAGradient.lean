import YangMills.Construction.ColdStepAtMirrorFrames.MomentOfASquareBound
import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
def localSizeOfGradientBoundStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ x lam κ W C g : ℝ) (d : ι → ι → ℝ)
    (Φ : BondField ι → ℝ) (p : ℝ → ℝ) (dZ : ι → ℝ) (T : BondField ι → ℝ),
    0 < ρ → 1 ≤ x → 0 < lam → 0 ≤ κ → 0 ≤ W → 0 ≤ g → IsCutoff ρ p → IsPseudoMetricOnBonds d →
    HasUniformlyConvexLaw ρ lam x κ C d Φ →
    (∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W) → ∑ b, Real.exp (-(2 * κ * dZ b)) ≤ W →
    (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) T η) →
    (∀ (η : BondField ι) (b : ι) (e : BondVector), (∀ b, ‖η b‖ < ρ) → ‖e‖ = 1 →
      |fderiv ℝ T η (bondVariation b e)| ≤ g * Real.exp (-(2 * κ * dZ b))) →
    HasLocalSize ρ (cutoffFactor ρ p) Φ (lpMomentConstant lam W W) x κ ((W + 1) * g * x ^ (-(1 / 2 : ℝ))) dZ T
end Interpolation
end YangMills.Construction
end
