import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.EnergyNearAClass
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open StepSettings RenormalizationStepParameters TorusFields TorusLumps StepCosts
variable {R : StepSetup} {n : ℕ}
def StepSettings.ChartSetting.AwayFromCore [NeZero n] (s : ChartSetting R n) (c : SettingCore R n)
    (Y : TorusSite n) : Prop :=
  ∀ Z ∈ s.storedBlockSet c, ∀ y ∈ sitesInBlocks R.params.side {Y}, ∀ z ∈ sitesInBlocks R.params.side {Z},
    (R.range : ℝ) / 8 < supDist y z
namespace ClusterExpansionOfAStep
def ActivityNearLevelShare : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ C y₀ : ℝ, 0 < C ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
      ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ s : ChartSetting R n, s.IsAdmissible →
        (∀ (c : SettingCore R n) (Y : TorusSite n), s.IsCoreOf c → s.IsMarked c → s.AwayFromCore c Y →
          |s.blockActivity T.lam Y +
              R.coupling * levelShare R.params.coupling R.params.side (R.depth + 1) s.region Y s.coarse| ≤
            C * Real.log R.coupling ∧
          ∀ X : Finset s.free, s.freeBondsOf Y ⊆ X →
            |(s.restrictedSplit T.lam X).activity T.lam Y +
                R.coupling * levelShare R.params.coupling R.params.side (R.depth + 1) s.region Y s.coarse| ≤
              C * Real.log R.coupling) ∧
        (s.IsCoreOf ⟨∅, ∅⟩ → s.IsMarked ⟨∅, ∅⟩ → s.coarse = trivialField n → s.support = ∅ →
          ∀ Y : TorusSite n, |s.blockActivity T.lam Y| ≤ C * Real.log R.coupling)
end ClusterExpansionOfAStep
end YangMills.Construction
end
