import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfTheImageForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusLumps StepSettings RenormalizationStepParameters
def ImageHasHullExpansionRegularity : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.params = T.stepParameters y →
    R.anchorRadius = T.ρA → R.barrierFn = T.cutoff → y ≤ R.coupling → R.HasExpansions → R.IsSymmetricWeight →
    R.nextCoupling = R.shiftedCoupling T.lam → |R.nextCoupling - R.coupling| ≤ 2 * R.params.B →
    ∀ h : CoarseLabelFacts R,
      HullExpansionRegularity R.params R.nextCoupling (coarseLabelSpace R h) (coarseWeightExpansion R) (coarseFactorExpansion R)
        (R.stateDensity T.lam)
end YangMills.Construction.ClusterExpansionOfAStep
end
