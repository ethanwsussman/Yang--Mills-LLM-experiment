import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.TermsOfTheRemainder
import YangMills.Construction.DirichletOperator.ChangedLongitudinalSourceAtTheCellsOfACubeProof
import YangMills.Construction.DirichletOperator.DivergenceSourceOnTheTorusOfACubeProof
import YangMills.Construction.DirichletOperator.FactsOfTheCellsOfACube
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
open RemainderEstimates
noncomputable section
namespace CubeOuterSource
theorem scaleSpacing_pos (𝒯 : NestedRegions) (n : ℤ) : 0 < scaleSpacing 𝒯.L 𝒯.ξ n := by apply _root_.YangMills.Construction.PartitionCubes.FirstTypeMaps.scaleSpacing_pos <;> assumption
theorem scale_le_scale_succ (𝒯 : NestedRegions) (n : ℕ) : 𝒯.scale n ≤ 𝒯.scale (n + 1) := by apply _root_.YangMills.Construction.CubeSourceProof.scale_le_scale_succ <;> assumption
theorem finite_fineBond (h : TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem weightedDist_nonneg (𝒯 : NestedRegions) (p q : 𝒯.Point) :
    0 ≤ 𝒯.weightedDist p q := by apply _root_.YangMills.Construction.DivSourceEstimate.weightedDist_nonneg <;> assumption
theorem weightedDist_comm (𝒯 : NestedRegions) (p q : 𝒯.Point) :
    𝒯.weightedDist p q = 𝒯.weightedDist q p := by apply _root_.YangMills.Construction.PartitionCubes.WeightedDistFromCube.weightedDist_comm <;> assumption
variable {𝒮 : NestedRegions} {M : ℕ}
theorem supBond_nonneg (f : 𝒮.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
theorem abs_le_supBond [Finite 𝒮.FineBond] (f : 𝒮.FineBond → ℝ) (b : 𝒮.FineBond) :
    |f b| ≤ supBond f :=
  le_ciSup (f := fun b => ‖f b‖) (finite_range _).bddAbove b
end CubeOuterSource
end
end YangMills.Construction
