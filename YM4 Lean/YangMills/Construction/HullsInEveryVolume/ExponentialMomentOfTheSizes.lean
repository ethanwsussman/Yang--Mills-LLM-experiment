import YangMills.Construction.HullsInEveryVolume.HullDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
def totalSizeExpMomentStatement : Prop :=
  ∃ CE : RenormalizationStepParameters.ParameterAssignment → ℝ, EventuallyInParameters fun P R y => ∀ (g β : ℝ) (K m : ℕ)
    (T : WeightedResponses.StageTower (P.stepParameters y)) (u n : ℕ) [NeZero n], HullChainAtLevel P y g β K m T u n →
    Integrable (fun w => Real.exp (totalSize T R.s₁ u n w)) (WeightedResponses.markedSampleLaw T β u n) ∧
      ∫ w, Real.exp (totalSize T R.s₁ u n w) ∂(WeightedResponses.markedSampleLaw T β u n) ≤
        Real.exp (CE P * Real.log (stageCoupling T u) * (n : ℝ) ^ 4)
end YangMills.Construction.HullTrees
end
