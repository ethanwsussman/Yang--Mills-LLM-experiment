import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open TorusFields StepSettings RenormalizationStepParameters BlockOffsets
def BlockCostsAgree : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ (y : ℝ) (R : StepSetup), T.floorMin ≤ y → R.params = T.stepParameters y →
    ∀ (n n' : ℕ) [NeZero n] [NeZero n'], T.n₀ ≤ n → T.n₀ ≤ n' →
      ∀ (s : ChartSetting R n) (s' : ChartSetting R n')
      (Y : TorusSite n) (Y' : TorusSite n') (m k : ℕ) (η : FreeCoords s.free) (η' : FreeCoords s'.free),
      s.IsAdmissible → s'.IsAdmissible → SettingsAgreeNear s s' Y Y' m → 4 ≤ k → k ≤ m →
      CoordsAgreeNear s s' Y Y' k η η' → s.InBalls η → s'.InBalls η' →
      |s.blockCostAt Y η - s'.blockCostAt Y' η'| ≤
          (T.side : ℝ) ^ 4 * T.threshold ^ 2 * T.N 0 *
            Real.exp (-T.δ₁ * ((T.side * k - T.side - 2 ^ 16 : ℕ) : ℝ)) ∧
        s.logJacobianAt Y η = s'.logJacobianAt Y' η' ∧ (s.freeBondsOf Y).card = (s'.freeBondsOf Y').card
end ClusterExpansionOfAStep
end YangMills.Construction
end
