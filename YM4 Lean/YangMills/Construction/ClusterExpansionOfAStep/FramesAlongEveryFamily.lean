import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.FrameAnalyticity
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
open YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepCosts
def FrameAnalyticAlongFamilies : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ (x y : ℝ), y₀ ≤ x →
    ∀ (t n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ (V : TorusField n), IsCold (5 / 4 * T.threshold) V →
      ∀ b ∈ chartBonds T.side n, ∀ (j : ℕ) (c : Fin j → TorusBond n) (X : Fin j → imaginaryQuaternions),
        AnalyticAt ℝ (fun τ : Fin j → ℝ =>
          frameCoord (T.stepParameters y) T.ρA t (boxRadius x) (perturb c X τ V) b) 0
end YangMills.Construction.FrameAnalyticity
end
