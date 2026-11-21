import YangMills.Construction.ClusterExpansionOfAStep.ShareOfAChainSplits
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames RenormalizationStepParameters StepSettings TorusFields TorusLumps TorusShares
def SettingRegionsRegular : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ s : ChartSetting R n, s.IsAdmissible →
      IsLocallyOrthantClosed s.region 1024 ∧ IsColdOn s.region (9 / 8 * T.threshold) s.coarse ∧
      IsLocallyOrthantClosed (sitesInBlocks R.params.side s.region) 1024 ∧
      IsColdOn (sitesInBlocks R.params.side s.region) (9 / 8 * T.threshold)
        (minimizingField R.params.coupling R.anchorRadius R.params.side R.depth s.region s.coarse) ∧
      ∀ W : TorusField (n * R.params.side),
        IsLocallyOrthantClosed (Finset.univ \ thickening lumpRange (torusHotSites R.params W)) 1024
end YangMills.Construction.ClusterExpansionOfAStep
end
