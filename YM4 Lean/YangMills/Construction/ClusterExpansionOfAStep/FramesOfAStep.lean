import YangMills.Construction.ClusterExpansionOfAStep.ConstantsOfTheColdChain
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepSettings
open ColdChain
def StepSetup.ColdChainFits (R : StepSetup) : Prop :=
  ∃ (δ lam σA cg : ℝ) (N : ℕ → ℝ),
    ColdChainConstants R.params.coupling δ R.params.side lam R.anchorRadius σA cg N ∧
      2 * R.params.threshold ≤ σA ∧ R.params.threshold ≤ 1
end YangMills.Construction.StepSettings
end
