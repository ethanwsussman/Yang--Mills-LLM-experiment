import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open ColdStepAtMirrorFrames
def cutoffRadialDeriv (p : ℝ → ℝ) (e v : BondVector) : ℝ := deriv p ‖e‖ * (inner ℝ e v / ‖e‖)
def cutoffIntegrationByPartsStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : ℝ) (p : ℝ → ℝ) (Ψ g : BondField ι → ℝ)
    (u : BondField ι), 0 < ρ → IsCutoff ρ p → ContDiff ℝ 1 Ψ → ContDiff ℝ 1 g →
    ∫ η, fderiv ℝ g η u * ballDensity (cutoffFactor ρ p) Ψ η =
      ∫ η, g η * (fderiv ℝ Ψ η u + ∑ b, cutoffRadialDeriv p (η b) (u b)) * ballDensity (cutoffFactor ρ p) Ψ η
end YangMills.Construction.WeightedResponses
end
