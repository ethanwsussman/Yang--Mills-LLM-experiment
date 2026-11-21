import YangMills.Construction.ClusterExpansionOfAStep.EnergyNearAClass
import YangMills.Construction.ClusterExpansionOfAStep.GroundsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open StepSettings RenormalizationStepParameters TorusFields StepGas
namespace ClusterExpansionOfAStep
def TrivialFieldColdGround : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → (coldCaseGround R (trivialField n)).IsColdCase ∧
      (coldCaseGround R (trivialField n)).groundSetting.IsCoreOf ⟨∅, ∅⟩ ∧
      ((coldCaseGround R (trivialField n)).groundSetting.IsAdmissible →
        (coldCaseGround R (trivialField n)).groundSetting.IsMarked ⟨∅, ∅⟩) ∧
      (coldCaseGround R (trivialField n)).groundSetting.coarse = trivialField n ∧
      (coldCaseGround R (trivialField n)).groundSetting.support = ∅
end ClusterExpansionOfAStep
end YangMills.Construction
end
