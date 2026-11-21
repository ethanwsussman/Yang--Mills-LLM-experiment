import YangMills.Construction.HullsInEveryVolume.HullDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
def siteSizeMomentStatement : Prop :=
  EventuallyInParameters fun P R y => ∀ g : ℝ, ∃ C : ℝ, 1 ≤ C ∧ ∀ (β : ℝ) (K m : ℕ)
    (T : WeightedResponses.StageTower (P.stepParameters y)) (u n : ℕ) [NeZero n],
    HullChainAtLevel P y g β K m T u n → ∀ (z : TorusFields.TorusSite n) (k : ℕ), 1 ≤ k →
      Integrable (fun w => siteSize T R.s₁ u n w z ^ k) (WeightedResponses.markedSampleLaw T β u n) ∧
      ∫ w, siteSize T R.s₁ u n w z ^ k ∂(WeightedResponses.markedSampleLaw T β u n) ≤
        C ^ k * (k.factorial : ℝ) ^ 6 * Real.exp (-(hullDecayRate P * stageCoupling T u / 4))
end YangMills.Construction.HullTrees
end
