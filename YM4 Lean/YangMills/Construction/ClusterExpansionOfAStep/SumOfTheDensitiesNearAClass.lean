import YangMills.Construction.ClusterExpansionOfAStep.EnergyNearAClass
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepSettings
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.RenormalizationStepParameters
def DensitySumNearComponentsBound : Prop :=
  ∃ rateCeiling : ChainParameters → ℝ, (∀ c, 0 < rateCeiling c) ∧
  ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rateCeiling T.toChainParameters →
    ∃ CE y₀ : ℝ, 0 < CE ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ (s : ChartSetting R n) (c : SettingCore R n), s.IsAdmissible →
      s.IsCoreOf c → s.IsMarked c → ∀ 𝒦 ⊆ s.storedComponents c,
        0 < s.localIntegral (blocksNear R.params.side R.range (𝒦.biUnion id)) ∧
        |∑ Y ∈ blocksNear R.params.side R.range (𝒦.biUnion id), s.blockActivity T.lam Y -
            Real.log (s.localIntegral (blocksNear R.params.side R.range (𝒦.biUnion id)))| ≤
          CE * (R.range : ℝ) ^ 4 * Real.log R.coupling *
            ((blocksNear R.params.side R.range (𝒦.biUnion id)).card : ℝ)
end YangMills.Construction.StepSettings
end
