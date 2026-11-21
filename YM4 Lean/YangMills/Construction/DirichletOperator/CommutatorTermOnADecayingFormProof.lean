import YangMills.Construction.DirichletOperator.ApproximateInverseAndLocalDefectsProof
import YangMills.Construction.DirichletOperator.CommutatorSourceAtTheCellsOfACubeProof
import YangMills.Construction.DirichletOperator.FormDecayingFromAPointOfACube
import YangMills.Construction.DirichletOperator.PropagatorBoundsForSourcesInFormsProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
open YangMills.Construction.PartitionCubes
open YangMills.Construction.RemainderEstimates
noncomputable section
namespace YangMills.Construction.CubeDefect.OnDecayingForm
theorem scaleSpacing_pos (𝒯 : NestedRegions) (n : ℤ) : 0 < scaleSpacing 𝒯.L 𝒯.ξ n := by apply _root_.YangMills.Construction.PartitionCubes.FirstTypeMaps.scaleSpacing_pos <;> assumption
theorem finite_fineBond (h : TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem weightedDist_nonneg (𝒯 : NestedRegions) (p q : 𝒯.Point) :
    0 ≤ 𝒯.weightedDist p q := by apply _root_.YangMills.Construction.DivSourceEstimate.weightedDist_nonneg <;> assumption
section Norms
variable {𝒯 : NestedRegions}
end Norms
end YangMills.Construction.CubeDefect.OnDecayingForm
