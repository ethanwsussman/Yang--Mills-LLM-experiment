import YangMills.Construction.TwoPoints.ThreePropertiesOfAForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
def IsLocalKernelNear (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (ξ : AmbientSpace)
    (F : AmbientSpace → ℂ) : Prop :=
  ∀ k₁ ∈ ccInfIn (euclidOpenBall (0 : AmbientSpace) (euclidNorm ξ / 32)),
    ∀ k₂ ∈ ccInfIn (euclidOpenBall ξ (euclidNorm ξ / 32)),
      complexifyForm S k₁ k₂ =
        lebesgueIntegral fun z₂ : AmbientSpace =>
          lebesgueIntegral fun z₁ : AmbientSpace => k₁ z₁ * k₂ z₂ * F (z₂ - z₁)
def LocalFormKernel.Statement : Prop :=
  ∀ (scale : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ), IsDisjointForm S →
    IsAdmissibleForm scale S → ∀ ξ : AmbientSpace, ξ ≠ 0 → ∃ F : AmbientSpace → ℂ,
      AnalyticOnNhd ℝ F (euclidOpenBall ξ (2 * (euclidNorm ξ / 32))) ∧ IsLocalKernelNear S ξ F
end YangMills.Construction.TwoPoints
end
