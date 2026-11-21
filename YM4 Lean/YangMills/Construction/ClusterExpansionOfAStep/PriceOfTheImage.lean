import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfTheImageForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open YangMills.Construction.StepSettings YangMills.Construction.RenormalizationStepParameters YangMills.Construction.TorusLumps
def ImageHasHullExpansionPrice : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.IsWellPosed →
      R.nextCoupling = R.shiftedCoupling T.lam → |R.nextCoupling - R.coupling| ≤ 2 * R.params.B →
      ∀ h : CoarseLabelFacts R,
        HullExpansionPrice R.params R.nextCoupling (coarseLabelSpace R h) (coarseFactorExpansion R) (R.stateDensity T.lam)
end YangMills.Construction.ClusterExpansionOfAStep
end
