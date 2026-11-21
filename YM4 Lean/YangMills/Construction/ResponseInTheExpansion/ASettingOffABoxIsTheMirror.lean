import YangMills.Construction.ClusterExpansionOfAStep.ColdRenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.MirrorOfABox
import YangMills.Construction.ResponseInTheExpansion.MirrorLawOfAStep
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ResponseInTheExpansion
open TorusFields WeightedResponses RenormalizationStepParameters StepSettings TorusLumps TorusMirror StepCosts StepMarks
def settingNearColdMirrorStatement : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.ColdStepHolds →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
      ∀ (n m m' : ℕ) [NeZero n] [NeZero (4 * m)] (s : ChartSetting R n) (o : TorusSite n), T.n₀ ≤ n → T.n₀ ≤ 4 * m →
        s.IsAdmissible →
        IsCold (9 / 8 * T.threshold) (mirrorField m o s.coarse) →
        SettingsAgreeNear s (coldChartSetting R (mirrorField m o s.coarse)) o 0 m' → (R.range : ℝ) / (4 * (T.side : ℝ)) ≤ m' →
        ∀ (Z : Finset (TorusBond (n * R.params.side))) (F : (↥Z × Fin 3 → ℝ) → ℝ) (B : ℝ),
          (∀ b ∈ Z, b ∈ chartBonds R.params.side n ∧ supDist (parentBlock R.params.side b.1) o ≤ m' / 4) →
          Measurable F → (∀ v, |F v| ≤ B) →
          |weightedMean (chartDensity s) (fun η => F (imaginaryComponentsOn Z
              (frameDeviation R.params R.anchorRadius R.depth R.frameReach s.coarse (s.field η)))) -
            reflectedStepMean R m o s.coarse
              (fun c => F (imaginaryComponentsOn Z (reflectedCoordinateAt R.params.side R.depth m o c)))| ≤
          2 * B * Real.exp (-(T.rt * m' / 2 ^ 3))
end ResponseInTheExpansion
end YangMills.Construction
end
