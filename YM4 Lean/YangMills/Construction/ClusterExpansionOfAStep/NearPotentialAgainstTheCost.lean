import YangMills.Construction.ClusterExpansionOfAStep.CountsOfAClassAtAStep
import YangMills.Construction.ClusterExpansionOfAStep.EnergyNearAClass
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open StepSettings RenormalizationStepParameters TorusLumps TorusFields
def NearPotentialLeEnergy : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ CE y₀ : ℝ, 0 < CE ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ (s : ChartSetting R n) (c : SettingCore R n), s.IsAdmissible → s.IsCoreOf c →
      ∀ 𝒦 ⊆ s.storedComponents c, ∀ Yk : Finset (TorusSite (n * R.params.side)), Yk ⊆ s.support →
        Yk ⊆ 𝒦.biUnion id →
        (∀ z ∈ s.support \ Yk, ∀ y ∈ sitesInBlocks R.params.side (blocksNear R.params.side R.range (𝒦.biUnion id)),
          (R.range : ℝ) / 4 ≤ supDist y z) →
        ∀ η : FreeCoords s.free, s.InBalls η →
          -(s.localPotential (blocksNear R.params.side R.range (𝒦.biUnion id)) fun b => η b.1) ≤
            -(R.coupling * s.energyNear (blocksNear R.params.side R.range (𝒦.biUnion id)) η) +
              ∑ z ∈ nearSites R.range Yk, R.siteDensity (n * R.params.side) z (s.field 0) s.support s.labelling +
              CE * (R.range : ℝ) ^ 4 * Real.log R.coupling *
                ((blocksNear R.params.side R.range (𝒦.biUnion id)).card : ℝ)
end YangMills.Construction.ClusterExpansionOfAStep
end
