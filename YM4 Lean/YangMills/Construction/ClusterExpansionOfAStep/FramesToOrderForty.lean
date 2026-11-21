import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters StepCosts
def ClusterExpansionOfAStep.FrameDerivativesBounded : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ (K : ℕ → ℝ) (y₀ : ℝ), (∀ j, 0 < K j) ∧ ∀ (x y : ℝ), y₀ ≤ x →
    ∀ (t n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ (V : TorusField n), IsCold (5 / 4 * T.threshold) V →
      ∀ b ∈ chartBonds T.side n, ∀ (j : ℕ) (c : Fin j → TorusBond n) (X : Fin j → imaginaryQuaternions),
        1 ≤ j → j ≤ 40 → AreUnitVectors X →
        ContDiffAt ℝ 40 (fun τ : Fin j → ℝ =>
          frameCoord (T.stepParameters y) T.ρA t (boxRadius x) (perturb c X τ V) b) 0 ∧
        ‖mixedDeriv (fun V' : TorusField n => frameCoord (T.stepParameters y) T.ρA t (boxRadius x) V' b) V c X‖ ≤
          16 ^ j * K j ∧
        (4 * boxRadius x + 5 < n →
          (∃ l, ∀ h, BondOffsetInBox (boxRadius x) h → c l ≠ bondFrom (parentBlock T.side b.1) h) →
          mixedDeriv (fun V' : TorusField n => frameCoord (T.stepParameters y) T.ρA t (boxRadius x) V' b) V c X = 0)
end YangMills.Construction
end
