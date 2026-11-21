import YangMills.Construction.HullsInEveryVolume.HullDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction.HullTrees
def stageStateDensityStatement : Prop :=
  HullTrees.EventuallyInParameters fun Tb _ y => ∀ (g β : ℝ) (K m : ℕ) (T : WeightedResponses.StageTower (Tb.stepParameters y)) (u n : ℕ) [NeZero n],
    HullTrees.HullChainAtLevel Tb y g β K m T u n →
    ∀ F : WeightedResponses.StageState T u n → ℝ, Measurable F → (∃ C : ℝ, ∀ q, |F q| ≤ C) →
      ∫ w, F (WeightedResponses.stageState T u n w) ∂(WeightedResponses.markedSampleLaw T β u n) =
        (∫ W, (open Classical in ∑ Y ∈ Finset.univ.filter
              (TorusLumps.IsHullState (Tb.stepParameters y) (HullTrees.stageRange T u) W),
            ∫ ω, F (W, ⟨Y, ω⟩) * (T.stage u).labelWeight n W Y ω ∂(Measure.pi fun _ : Y => (T.stage u).labels.μ))
            ∂(TorusFields.fieldHaar n)) /
          ∫ W, TorusLumps.wilsonWeight β (WeightedResponses.fineSide (Tb.stepParameters y).side u n) W
            ∂(TorusFields.fieldHaar (WeightedResponses.fineSide (Tb.stepParameters y).side u n))
end YangMills.Construction.HullTrees
end
