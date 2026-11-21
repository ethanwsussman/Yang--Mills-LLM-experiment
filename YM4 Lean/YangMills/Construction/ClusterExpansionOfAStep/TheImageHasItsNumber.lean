import YangMills.Construction.ClusterExpansionOfAStep.ColdRenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.CoupledDensitiesOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
def ImageCarriesItsNumber : Prop :=
  ∃ rt₀ : RenormalizationStepParameters.ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → T.ColdStepHolds →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSettings.StepSetup, R.OnParameters T y → R.IsSymmetricWeight →
      TorusLumps.ColdExpansionHypotheses R.params R.depth R.coupling (R.couplingShift T.lam) T.Cs T.CE
        (T.Ct * R.coupling * Real.exp (-(T.δc / 8 * R.frameReach)))
        (2 * Real.exp (-(T.gasRate * R.coupling / 2))) (TorusLumps.maxOfFirstFour T.N)
        (TorusLumps.kernelImage R.params R.coupling R.functional)
        (StepSettings.coldInteractionDensity R T.lam) (StepSettings.coldExpansionDensity R)
        (StepSettings.coldFrameDensity R) R.blockDensity
        (ShareFamilies.levelShareFamily T.coupling T.side (R.depth + 1))
end YangMills.Construction.ClusterExpansionOfAStep
end
