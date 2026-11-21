import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.NearAClassOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters StepSettings StepCosts
def ClusterExpansionOfAStep.CutActivitiesAwayFromNear : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ CE y₀ : ℝ, 0 < CE ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
      ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ (s : ChartSetting R n) (c : SettingCore R n), s.IsAdmissible →
        s.IsCoreOf c → ∀ 𝒦 ⊆ s.storedComponents c,
          |∑ Y ∈ Finset.univ \ blocksNear R.params.side R.range (𝒦.biUnion id),
              ((s.restrictedSplit T.lam (s.freeNear (blocksNear R.params.side R.range (𝒦.biUnion id)))).activity
                  T.lam Y +
                (R.coupling * s.blockCostAt Y 0 - s.blockDensityAt Y 0 - s.logJacobianAt Y 0) -
                R.gaussianLogMass T.lam * (ClusterExpansionOfAStep.freeBondsAt s.free Y).card)| ≤
            CE * (R.range : ℝ) ^ 4 * Real.log R.coupling *
              ((blocksNear R.params.side R.range (𝒦.biUnion id)).card : ℝ)
end YangMills.Construction
end
