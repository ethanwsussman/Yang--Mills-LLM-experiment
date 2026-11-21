import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.GroundsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepGas
open StepSettings TorusLumps TorusFields
def ColdCaseGroundActivityEq : Prop :=
  ∀ (S : StepSetup) (n : ℕ) [NeZero n] (V : TorusField n) (lam : ℝ) (Y : TorusSite n), Odd S.params.side → 2 ≤ n →
    (coldCaseGround S V).groundSetting.blockActivity lam Y = (coldChartSetting S V).blockActivity lam Y
end YangMills.Construction.StepGas
end
