import YangMills.Construction.PassageToTheLimit.TransportedLatticeFunctionalsAreBoundedFormsProof
import YangMills.Construction.DirichletOperator.CommutatorOfTheLongitudinalOperatorOfACube
import YangMills.Construction.DirichletOperator.LengthsOnACubeOfTheFirstKindProof
import YangMills.Construction.DirichletOperator.RestrictionsToTheCellsOfACubeProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
open Dirichlet Torus RegionSequence.NestedRegions PartitionCubes
open RegionSequence.OperatorEstimates (kernelOf)
open CubeTorus (torusSetting levelSpacing chosenConstants)
noncomputable section
namespace CubeCommutator
section Matrices
variable {ι : Type} [Fintype ι]
end Matrices
section Bonds
variable (𝒯 : RegionSequence.NestedRegions)
theorem finite_fineBond : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineBond <;> assumption
variable {𝒯}
theorem bondInner_eq_sum [Fintype 𝒯.FineBond] (A B : 𝒯.FineBond → ℝ) :
    bondInner A B = 𝒯.ξ ^ 4 * ∑ b, A b * B b := by
  simp only [bondInner, finsum_eq_sum_of_fintype]
end Bonds
section Cut
variable {𝒯 : RegionSequence.NestedRegions}
end Cut
section Lengths
variable {𝒯 : RegionSequence.NestedRegions}
theorem supNorm_torusProj_le {S : ℝ} (w : Fin 4 → ℝ) : supNorm (torusProj 4 S w) ≤ ‖w‖ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.supNorm_proj_le <;> assumption
theorem torusProj_add {S : ℝ} (u w : Fin 4 → ℝ) :
    torusProj 4 S (u + w) = torusProj 4 S u + torusProj 4 S w := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_add <;> assumption
theorem torusProj_zero {S : ℝ} : torusProj 4 S 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.torusProj_zero <;> assumption
theorem lOneNorm_sub_centre_le (hl : LengthAxioms 4 𝒯.side) {w x : 𝒯.Point}
    (hx : x ∈ 𝒯.cellOf w) : lOneNorm (x - w) ≤ 2 * 𝒯.levelScale w := by
  have h₁ : supNorm (x - w) ≤ 𝒯.levelScale w / 2 := hx
  have h₂ := hl.lOneNorm_le_supNorm (x - w)
  push_cast at h₂
  linarith
end Lengths
section Numbers
end Numbers
section Cells
variable {𝒯 : RegionSequence.NestedRegions}
end Cells
end CubeCommutator
end
end YangMills.Construction
