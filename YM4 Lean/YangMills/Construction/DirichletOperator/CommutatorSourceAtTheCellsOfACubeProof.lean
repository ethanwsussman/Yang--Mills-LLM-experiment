import YangMills.Construction.DirichletOperator.ChangedLongitudinalSourceAtTheCellsOfACubeProof
import YangMills.Construction.DirichletOperator.FactsOfTheCellsOfACube
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes YangMills.Construction.RemainderEstimates
noncomputable section
namespace YangMills.Construction.CubeAdjointDefect.CommutatorAtCells
theorem cast_L_pos (𝒯 : NestedRegions) : (0 : ℝ) < 𝒯.L := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.blockFactor_pos <;> assumption
theorem scaleSpacing_pos (𝒯 : NestedRegions) (n : ℤ) : 0 < scaleSpacing 𝒯.L 𝒯.ξ n := by apply _root_.YangMills.Construction.PartitionCubes.FirstTypeMaps.scaleSpacing_pos <;> assumption
theorem finite_fineBond (h : TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem weightedDist_nonneg (𝒯 : NestedRegions) (p q : 𝒯.Point) :
    0 ≤ 𝒯.weightedDist p q := by apply _root_.YangMills.Construction.DivSourceEstimate.weightedDist_nonneg <;> assumption
end YangMills.Construction.CubeAdjointDefect.CommutatorAtCells
