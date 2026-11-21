import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.LocalityOfTheDensities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FlatTops
open StepSettings TorusFields
def TrivialFieldSettingsAgree : Prop :=
  ∀ (R : StepSetup) (n n' : ℕ) [NeZero n] [NeZero n'] (m : ℕ), Odd R.params.side → 2 ≤ n → 2 ≤ n' →
    2 * m + 2 < n → 2 * m + 2 < n' →
    SettingsAgreeAwayFromFrames (coldChartSetting R (trivialField n)) (coldChartSetting R (trivialField n')) 0 0 m
end YangMills.Construction.FlatTops
end
