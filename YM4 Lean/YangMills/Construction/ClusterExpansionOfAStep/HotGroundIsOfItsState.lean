import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.GroundOfItsState
import YangMills.Construction.ClusterExpansionOfAStep.GroundsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
def HotGroundIsOverState : Prop :=
  ∀ R : StepSettings.StepSetup, R.IsWellPosed → ∀ (n : ℕ) [NeZero n]
    (V : TorusFields.TorusField n) (q : StepSettings.CoarseState R n),
    (StepGas.hotCaseGround R V q).IsHotCase →
      (StepGas.hotCaseGround R V q).groundSetting.IsAdmissible →
      (StepGas.hotCaseGround R V q).IsOverState
end YangMills.Construction.ClusterExpansionOfAStep
end
