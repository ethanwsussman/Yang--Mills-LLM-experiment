import YangMills.Construction.ClusterExpansionOfAStep.EnergyNearAClass
import YangMills.Construction.ClusterExpansionOfAStep.ShareOfAChainSplits
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames StepSettings RenormalizationStepParameters TorusFields TorusLumps
def FrameFieldNearMinimizer : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ s : ChartSetting R n, s.IsAdmissible →
      ∀ c : SettingCore R n, s.IsCoreOf c → s.IsMarked c →
        ∀ (x : TorusSite (n * R.params.side)) (i : Fin 4), parentBlock R.params.side x ∉ s.storedBlockSet c →
          parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) ∉ s.storedBlockSet c →
          ‖(s.field 0 x i : ℍ[ℝ]) -
              minimizingField R.params.coupling R.anchorRadius R.params.side R.depth s.region s.coarse x i‖ ≤
            2 * T.N 0 * T.threshold * Real.exp (-(T.δ₁ * (R.frameReach : ℝ)))
end YangMills.Construction.ClusterExpansionOfAStep
end
