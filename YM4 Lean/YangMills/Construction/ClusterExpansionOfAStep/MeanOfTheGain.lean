import YangMills.Construction.ClusterExpansionOfAStep.SizeOfADensity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames StepSettings RenormalizationStepParameters TorusFields
def GainMeanLogBound : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧
    ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∃ C y₀ : ℝ, 0 < C ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
      ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ s : ChartSetting R n, s.IsAdmissible →
        ∀ (c : SettingCore R n) (Y : TorusSite n), s.IsCoreOf c → s.IsMarked c → s.AwayFromCore c Y →
          ∀ X : Finset s.free, s.freeBondsOf Y ⊆ X → ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
            |weightedMean ((s.restrictedSplit T.lam X).interpolatedDensity T.lam τ)
              (fun η => (s.restrictedSplit T.lam X).interaction Y η - gaussianPart T.lam Y η)| ≤
              C * Real.log R.coupling
end YangMills.Construction.ClusterExpansionOfAStep
end
