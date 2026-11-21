import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.ColdStepAtMirrorFrames MeasureTheory
namespace YangMills.Construction
namespace BondIntegration
def bondDivergence (z : BondVector → BondVector) (v : BondVector) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ z v (EuclideanSpace.single i 1)) i
def IntegralByPartsAtBond : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι) (z : BondVector → BondVector)
    (u : BondField ι → ℝ) (C : ℝ), ContDiff ℝ 1 z → (∀ v, ‖z v‖ ≤ C) →
    (∀ v, ‖fderiv ℝ z v‖ ≤ C) → Differentiable ℝ u → Integrable u →
    (∀ e : BondVector, Integrable fun η => fderiv ℝ u η (bondVariation b e)) →
    ∫ η, (fderiv ℝ u η (bondVariation b (z (η b))) + bondDivergence z (η b) * u η) = 0
end BondIntegration
end YangMills.Construction
end
