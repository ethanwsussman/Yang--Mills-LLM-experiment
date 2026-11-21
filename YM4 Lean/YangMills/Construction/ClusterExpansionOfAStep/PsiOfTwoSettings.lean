import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepSettings
open BlockAverages LumpContours TorusFields TorusLumps RenormalizationStepParameters BlockOffsets
def blockInteractionLocalityBound : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ C y₀ : ℝ, 0 < C ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → ∀ (n n' : ℕ) [NeZero n] [NeZero n'],
      T.n₀ ≤ n → T.n₀ ≤ n' → ∀ (s : ChartSetting R n) (s' : ChartSetting R n') (Y : TorusSite n)
        (Y' : TorusSite n') (m k : ℕ) (η : FreeCoords s.free) (η' : FreeCoords s'.free),
        s.IsAdmissible → s'.IsAdmissible →
        SettingsAgreeNear s s' Y Y' m → 4 ≤ k → k ≤ m → (R.range : ℝ) / (2 ^ 8 * T.side) ≤ k →
        CoordsAgreeNear s s' Y Y' k η η' → s.InBalls η → s'.InBalls η' →
        |(s.blockInteraction Y η - s.blockGaussian T.lam Y η) -
            (s'.blockInteraction Y' η' - s'.blockGaussian T.lam Y' η')| ≤
            C * Real.exp (-(4 * T.rt * k)) ∧
          |s.blockInteraction Y η - s.blockGaussian T.lam Y η| ≤ C * R.coupling
end YangMills.Construction.StepSettings
end
