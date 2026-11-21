import YangMills.Construction.ClusterExpansionOfAStep.ColdRenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.CoupledDensitiesOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames StepSettings RenormalizationStepParameters TorusLumps
def ImageColdExpansion.ImageHasColdExpansion : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.ColdStepHolds →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.IsSymmetricWeight →
      ColdExpansion R.params (R.depth + 1) (R.shiftedCoupling T.lam) (kernelImage R.params R.coupling R.functional)
          (R.renormalizedDensity T.lam) ∧
        |R.shiftedCoupling T.lam - R.coupling| ≤ 2 * R.params.B
end YangMills.Construction
end
