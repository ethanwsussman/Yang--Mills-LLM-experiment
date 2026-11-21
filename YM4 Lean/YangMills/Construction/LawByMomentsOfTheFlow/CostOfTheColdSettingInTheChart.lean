import YangMills.Construction.ColdStepAtMirrorFrames.FramesAgainstTheLeastField
import YangMills.Construction.LawByMomentsOfTheFlow.ChartOfTheColdSetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open RenormalizationStepParameters StepSettings TorusFields ColdStepAtMirrorFrames BlockAverages
def coldSettingChartCostStatement : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusField n, IsCold (9 / 8 * T.threshold) V → ∀ u : ℕ, u = R.depth →
      ∀ k : BondField (ChartBondIndex R.params.side u n), (∀ b, ‖k b‖ < R.ballRadius) →
        ∑ Y : TorusSite n, (coldSettingOver R V).blockCostAt Y (chartFreeCoords R u V k) =
          chartedEnergyAt R.params.coupling
            (frameCoordField false R.params.coupling R.anchorRadius R.frameReach
              (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V))
            (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V) k
end YangMills.Construction.MomentLaw
end
