import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
open YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.Estimates
def radialDirectionalDeriv (p : ℝ → ℝ) (e v : BondVector) : ℝ := deriv p ‖v‖ * ‖v‖⁻¹ * ⟪v, e⟫
def cutoffDerivSum (p : ℝ → ℝ) (u : ℝ) : ℝ :=
  |iteratedDeriv 1 p u| + |iteratedDeriv 2 p u| + |iteratedDeriv 3 p u|
def radialDirectionalDerivBoundStatement : Prop :=
  ∀ (ρ : ℝ) (p : ℝ → ℝ), 0 < ρ → IsCutoff ρ p → ∃ K : ℝ, 0 ≤ K ∧ ∀ e v : BondVector, ‖v‖ < ρ →
    ContDiffAt ℝ 2 (radialDirectionalDeriv p e) v ∧
      |radialDirectionalDeriv p e v| ≤ K * ‖e‖ * cutoffDerivSum p ‖v‖ ∧
      ‖fderiv ℝ (radialDirectionalDeriv p e) v‖ ≤ K * ‖e‖ * cutoffDerivSum p ‖v‖ ∧
      ‖fderiv ℝ (fderiv ℝ (radialDirectionalDeriv p e)) v‖ ≤ K * ‖e‖ * cutoffDerivSum p ‖v‖
end YangMills.Construction.Estimates
end
