import YangMills.Construction.ClusterExpansionOfAStep.HessianFloorOfTheCostForm
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open StepSettings RenormalizationStepParameters TorusFields
variable {R : StepSetup} {n : ℕ}
def directionalDeriv {free : Finset (TorusBond n)} (u : FreeCoords free → ℝ) (η : FreeCoords free) (b : free)
    (X : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  deriv (fun τ : ℝ => u (Function.update η b (η b + τ • X))) 0
def SettingGradientsClose : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
      ∀ (n n' : ℕ) [NeZero n] [NeZero n'], T.n₀ ≤ n → T.n₀ ≤ n' → ∀ (s : ChartSetting R n)
        (s' : ChartSetting R n') (Y : TorusSite n) (Y' : TorusSite n') (m k : ℕ) (η : FreeCoords s.free)
        (η' : FreeCoords s'.free),
        s.IsAdmissible → s'.IsAdmissible → SettingsAgreeNear s s' Y Y' m → k ≤ m →
        (R.range : ℝ) / (2 ^ 8 * T.side) ≤ k →
        BlockOffsets.CoordsAgreeNear s s' Y Y' k η η' → s.InBalls η → s'.InBalls η' →
        ∀ (q : NearBondIndex) (h : nearBond R.params.side Y q ∈ s.free)
          (h' : nearBond R.params.side Y' q ∈ s'.free)
          (X : EuclideanSpace ℝ (Fin 3)), IsNearIndex R.params.side (k / 2) q → ‖X‖ = 1 →
          R.coupling * |directionalDeriv s.costSum η ⟨_, h⟩ X - directionalDeriv s'.costSum η' ⟨_, h'⟩ X| ≤
              Real.exp (-(4 * T.rt * k)) ∧
          ((R.range : ℝ) / (4 * T.side) ≤ k → ∀ ν : ℝ, 0 ≤ ν → ν ≤ 1 →
            |directionalDeriv (s.partPotential ν) η ⟨_, h⟩ X -
                directionalDeriv (s'.partPotential ν) η' ⟨_, h'⟩ X| ≤
              Real.exp (-(4 * T.rt * k)))
end ClusterExpansionOfAStep
end YangMills.Construction
end
