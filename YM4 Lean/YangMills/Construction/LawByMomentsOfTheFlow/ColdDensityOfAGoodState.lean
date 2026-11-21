import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses StepSettings
def coldDensityIntegrableStatement : Prop :=
  ForAllPoints fun Λ _ _ X₀ S => X₀ ≤ S.scaleCoupling → ∀ (d n : ℕ) [NeZero n], d < S.logIndex →
    n = S.levelSide (S.lastSeparated + d + 1) →
    ∀ (V : TorusField n) (Y : Finset (TorusSite n)), S.IsGoodConfig (S.lastSeparated + d + 1) n V Y →
    Integrable (chartDensity (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
      (S.smoothedField (S.lastSeparated + d + 1) n V))) ∧
    0 < ∫ η, chartDensity (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
      (S.smoothedField (S.lastSeparated + d + 1) n V)) η
end YangMills.Construction.MomentLaw
end
