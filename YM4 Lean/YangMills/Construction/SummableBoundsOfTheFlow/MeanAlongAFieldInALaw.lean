import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongAField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BondIntegration
open MeasureTheory ColdStepAtMirrorFrames
def integrationByPartsAlongFieldStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : ℝ) (p : ℝ → ℝ) (Ψ G : BondField ι → ℝ) (b : ι)
    (v : BondVector → BondVector) (C : ℝ), 0 < R → IsCutoff R p → ContDiff ℝ 1 Ψ →
    ContDiffOn ℝ 1 G {η | ∀ b, ‖η b‖ < R} → ContDiff ℝ 1 v → (∀ u, ‖v u‖ ≤ C) →
    (∀ u, ‖fderiv ℝ v u‖ ≤ C) →
    Integrable (fun η => fieldDerivative b v G η * ballDensity (cutoffFactor R p) Ψ η) →
    Integrable (fun η => G η * fieldScore p Ψ b v η * ballDensity (cutoffFactor R p) Ψ η) →
    Integrable (fun η => G η * radialCutoffSlope p (η b) (v (η b)) * ballDensity (cutoffFactor R p) Ψ η) →
    ∫ η, fieldDerivative b v G η * ballDensity (cutoffFactor R p) Ψ η =
      ∫ η, G η * fieldScore p Ψ b v η * ballDensity (cutoffFactor R p) Ψ η
end YangMills.Construction.BondIntegration
end
