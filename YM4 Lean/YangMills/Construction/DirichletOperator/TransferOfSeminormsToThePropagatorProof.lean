import YangMills.Construction.DirichletOperator.PropagatorBoundsForDivergenceSourcesProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.PropagatorSeminorms
theorem finite_fineBond (R : RegionSequence.NestedRegions) : Finite R.FineBond := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineBond <;> assumption
theorem weightedDist_nonneg (R : RegionSequence.NestedRegions) (x x' : R.Point) :
    0 ≤ R.weightedDist x x' := by apply _root_.YangMills.Construction.DivSourceEstimate.weightedDist_nonneg <;> assumption
theorem pNorm_nonneg {R : RegionSequence.NestedRegions}
    (p : RegionSequence.NestedRegions.NormExponent) (g : R.FineBond → ℝ) :
    0 ≤ (RegionSequence.NestedRegions.formCutSpace R).pNorm p g := by apply _root_.YangMills.Construction.DivSourceEstimate.pNorm_nonneg <;> assumption
end YangMills.Construction.PropagatorSeminorms
