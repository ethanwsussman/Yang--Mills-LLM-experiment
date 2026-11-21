import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.GroundsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.MirrorOfABox
import YangMills.Construction.ResponseInTheExpansion.CurvatureOfALevelOnTheDraws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ResponseInTheExpansion
def coldMirrorSettingAgreementStatement : Prop :=
  ∀ (R : StepSettings.StepSetup) (n m : ℕ) [NeZero n] [NeZero (4 * m)] (V : TorusFields.TorusField n)
    (q : StepSettings.CoarseState R n) (γ : StepGas.GasFamily R n) (o : TorusFields.TorusSite n),
    R.params.Admissible → 2 ≤ n → R.params.side ∣ n → 2 ≤ m → 0 < R.frameReach → R.frameReach + 1 < m →
    4 * R.frameReach + 5 < n → 2 * m + 2 < n →
    TorusLumps.IsHullState R.params R.nextRange V q.1 → Disjoint q.1 (ResponseInTheExpansion.supBall o m) →
    (∀ θ, γ.Occupies θ → Disjoint θ.core (ResponseInTheExpansion.supBall o m)) →
    TorusFields.IsCold (9 / 8 * R.params.threshold) (TorusMirror.mirrorField m o V) ∧
      StepSettings.SettingsAgreeNear ((StepGas.hotCaseGround R V q).settingOf γ)
        (StepSettings.coldChartSetting R (TorusMirror.mirrorField m o V)) o 0 (m - R.frameReach - 1)
end ResponseInTheExpansion
end YangMills.Construction
end
