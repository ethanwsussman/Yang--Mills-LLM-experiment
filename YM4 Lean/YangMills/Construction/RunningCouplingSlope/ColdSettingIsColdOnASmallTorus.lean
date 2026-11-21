import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RenormalizationStepParameters StepSettings TorusFields
namespace Slope
def ColdChartFieldIsColdOnSmallTorus : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ y : ℝ, T.floorMin ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → n ≤ 4 * R.frameReach + 5 → ∀ V : TorusField n, IsCold (9 / 8 * T.threshold) V →
      ∀ η : FreeCoords (coldChartSetting R V).free, (coldChartSetting R V).InBalls η →
        IsCold (T.threshold / 4) ((coldChartSetting R V).field η)
end Slope
end YangMills.Construction
end
