import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.ChangeOfTheLongitudinalOperatorInNorm
import YangMills.Construction.DirichletOperator.SourcesOfTheAdjointDefectOfACube
import YangMills.Construction.DirichletOperator.AdjointDefectOfACubeThroughItsGreenOperator
import YangMills.Construction.DirichletOperator.GreenOperatorOfACubeAgainstSourcesAtItsCells
import YangMills.Construction.DirichletOperator.RegularityOfTheLocalOperatorsProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes YangMills.Construction.RemainderEstimates
open YangMills.Construction.CubeAdjointDefect (cellWeightedSum commutatorSource outerSource)
open YangMills.Construction.CubeGreenSources (greenOfSources)
open YangMills.Construction.CubeOperators (cutoffSize cubeDivOne)
noncomputable section
namespace YangMills.Construction.CubeAdjointGreen
theorem finite_fineBond (hl : YangMills.Construction.Torus.TorusLengthsStatement)
    (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
section Suprema
variable {𝒯 : NestedRegions}
theorem supBond_nonneg (f : 𝒯.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
theorem supTensor_nonneg {r : ℕ} (J : 𝒯.Tensor r) : 0 ≤ supTensor J :=
  Real.iSup_nonneg fun _ => supBond_nonneg _
theorem norm_le_supBond [Finite 𝒯.FineBond] (f : 𝒯.FineBond → ℝ) (b : 𝒯.FineBond) :
    ‖f b‖ ≤ supBond f :=
  le_ciSup (f := fun b => ‖f b‖) (Set.finite_range _).bddAbove b
end Suprema
theorem scale_pos (𝒯 : NestedRegions) (n : ℕ) : 0 < 𝒯.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
variable {𝒮 : NestedRegions} {M : ℕ}
end YangMills.Construction.CubeAdjointGreen
