import YangMills.Construction.DirichletOperator.ApproximateInverseAndLocalDefectsProof
import YangMills.Construction.DirichletOperator.BoundsOnTheDefectsOfTheCutOffProof
import YangMills.Construction.DirichletOperator.FactsOfTheCellsOfACube
import YangMills.Construction.DirichletOperator.FormDecayingFromAPointOfACube
import YangMills.Construction.DirichletOperator.PropagatorBoundsForSourcesInFormsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
namespace PartitionCubes.LocalPartBound
section CutNorms
theorem finite_fineBond (hT : Torus.TorusLengthsStatement) (𝒯 : NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
variable {𝒯 : NestedRegions}
end CutNorms
section Centres
variable {𝒮 : NestedRegions}
theorem scale_pos (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem weightedDist_nonneg (y y' : 𝒮.Point) : 0 ≤ 𝒮.weightedDist y y' := by apply _root_.YangMills.Construction.DivSourceEstimate.weightedDist_nonneg <;> assumption
theorem mem_cellOf_self (y : 𝒮.Point) : y ∈ 𝒮.cellOf y := by apply _root_.YangMills.Construction.CubeTorusComparison.CutoffDefects.mem_cellOf_self <;> assumption
end Centres
end PartitionCubes.LocalPartBound
end YangMills.Construction
