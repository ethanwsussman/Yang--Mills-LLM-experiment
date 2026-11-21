import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.LocalityOfTheDensities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepSettings
open YangMills.Construction.StepGas YangMills.Construction.TorusFields
def SettingsAgreeOfGroundsAgree : Prop :=
  ∀ (R : StepSetup) (n n' : ℕ) [NeZero n] [NeZero n'] (G : GasGround R n) (G' : GasGround R n')
    (Y : TorusSite n) (Y' : TorusSite n') (m : ℕ), Odd R.params.side → 2 ≤ n → 2 ≤ n' →
    GroundsAgreeNear G G' Y Y' m →
    SettingsAgreeAwayFromFrames G.groundSetting G'.groundSetting Y Y' m
end YangMills.Construction.StepSettings
end
