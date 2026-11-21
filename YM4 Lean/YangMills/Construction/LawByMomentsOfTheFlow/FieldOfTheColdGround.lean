import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open Classical in
def coldGroundFieldStatement : Prop :=
  ∀ (R : StepSettings.StepSetup) (n : ℕ) [NeZero n] (V : TorusFields.TorusField n), Odd R.params.side → 2 ≤ n →
    coldSettingOver R V =
        ({ StepSettings.coldChartSetting R V with fine := (StepSettings.coldChartSetting R V).field 0 } :
          StepSettings.ChartSetting R n) ∧
    (∀ η, WeightedResponses.chartDensity
        ({ StepSettings.coldChartSetting R V with fine := (StepSettings.coldChartSetting R V).field 0 } :
          StepSettings.ChartSetting R n) η =
      WeightedResponses.chartDensity (StepSettings.coldChartSetting R V) η) ∧
    (coldSettingOver R V).free = StepCosts.chartBonds R.params.side n ∧
    (∀ (η : StepSettings.FreeCoords (coldSettingOver R V).free) (b : (coldSettingOver R V).free),
      (coldSettingOver R V).field η b.1.1 b.1.2 =
        if BlockAverages.IsCrossingBond (F := TorusLumps.stepBlockFrame R.params.side n)
            (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 0 b.1.1, b.1.2)
        then BlockAverages.expUnit (StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach V b.1 +
            ColdStepAtMirrorFrames.toImaginary (η b)) * V (TorusLumps.parentBlock R.params.side b.1.1) b.1.2
        else BlockAverages.expUnit (StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach V b.1 +
            ColdStepAtMirrorFrames.toImaginary (η b))) ∧
    ∀ (η : StepSettings.FreeCoords (coldSettingOver R V).free) (b : TorusFields.TorusBond (n * R.params.side)),
      b ∉ (coldSettingOver R V).free → (coldSettingOver R V).field η b.1 b.2 = 1
end YangMills.Construction.MomentLaw
end
