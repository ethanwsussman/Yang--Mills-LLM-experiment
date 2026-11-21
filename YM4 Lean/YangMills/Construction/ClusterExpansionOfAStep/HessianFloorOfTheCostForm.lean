import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.StepSettings
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusLumps TorusFields StepCosts RenormalizationStepParameters
variable {R : StepSetup} {n : ℕ}
def ChartSetting.costSum [NeZero n] (s : ChartSetting R n) (η : FreeCoords s.free) : ℝ :=
  ∑ Y : TorusSite n, blockCost R.params R.depth (s.field η) s.coarse s.bases Y
structure ChartSetting.HasCostDecay [NeZero n] (s : ChartSetting R n) (lam C : ℝ) : Prop where
  contDiffOn : ∃ U : Set (FreeCoords s.free), IsOpen U ∧ (∀ η, s.InBalls η → η ∈ U) ∧
    ContDiffOn ℝ 3 s.costSum U
  hessian_ge : ∀ η, s.InBalls η → ∀ v : FreeCoords s.free,
    lam / 2 * ∑ b, ‖v b‖ ^ 2 ≤ deriv (deriv fun τ : ℝ => s.costSum (η + τ • v)) 0
  decay : ∃ M : s.free → s.free → ℝ,
    (∀ η, s.InBalls η → ∀ b b' X X', ‖X‖ = 1 → ‖X'‖ = 1 →
      |mixedSecondDeriv s.costSum η b b' X X'| ≤ M b b') ∧
    (∀ b b', M b b' ≤ C) ∧
    ∀ b, ∑ b', M b b' * (Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) ≤
      lam / 16
  firstDeriv_le : ∀ η, s.InBalls η → ∀ b X, ‖X‖ = 1 →
    |deriv (fun τ : ℝ => s.costSum (Function.update η b (η b + τ • X))) 0| ≤ C
end YangMills.Construction.StepSettings
namespace YangMills.Construction.ClusterExpansionOfAStep
open StepSettings RenormalizationStepParameters TorusFields
def CostHessianFloor : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ C y₀ : ℝ, 0 < C ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n →
      ∀ s : ChartSetting R n, s.IsAdmissible → s.HasCostDecay T.lam C
end YangMills.Construction.ClusterExpansionOfAStep
end
