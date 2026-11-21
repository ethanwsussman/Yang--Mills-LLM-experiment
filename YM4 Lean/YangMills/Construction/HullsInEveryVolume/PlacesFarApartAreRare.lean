import YangMills.Construction.HullsInEveryVolume.HullDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
def separatedUnitsRareStatement : Prop :=
  ∃ CE : RenormalizationStepParameters.ParameterAssignment → ℝ, EventuallyInParameters fun P _ y => ∀ (g β : ℝ) (K m : ℕ)
    (T : WeightedResponses.StageTower (P.stepParameters y)) (u n : ℕ) [NeZero n], HullChainAtLevel P y g β K m T u n →
    ∀ A : Finset (TorusFields.TorusSite n), A.Nonempty → Separated (2 ^ 17 + 8 * stageRange T u) A →
      (WeightedResponses.markedSampleLaw T β u n).real {w | ∀ z ∈ A, IsUnit T u n w z} ≤
        2 ^ (1 + A.card) * Real.exp (CE P * Real.log (stageCoupling T u) * (n : ℝ) ^ 4 -
          unitDecayRate P * stageCoupling T u * (A.card : ℝ))
end YangMills.Construction.HullTrees
end
