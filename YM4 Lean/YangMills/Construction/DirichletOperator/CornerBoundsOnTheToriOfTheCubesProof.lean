import YangMills.Construction.DirichletOperator.AveragedFormOnAScaledLattice
import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubes
import YangMills.Construction.DirichletOperator.FunctionsAndMapsOfTheCubes
import YangMills.Construction.DirichletOperator.NormsOnAScaledLattice
import YangMills.Construction.RegionSequence.CellsAndAdjoints
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.CornerGreen
open Dirichlet RegionSequence RegionSequence.NestedRegions PartitionCubes BareDilation
section Pull
variable {L j N : ℕ} {𝒯 : NestedRegions} {S : PeriodicLattice.Scales 4 L j N} {r : ℝ}
end Pull
section Numbers
theorem holderSite_nonneg_of_pos {𝒯 : NestedRegions} {α lam : ℝ} (hl : 0 < lam)
    (f : 𝒯.FineSite → ℝ) : 0 ≤ holderSite α lam f := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨x, x', h₁, _, rfl⟩
  exact mul_nonneg (Real.rpow_nonneg (div_pos hl h₁).le _) (norm_nonneg _)
theorem supBond_nonneg' {𝒯 : NestedRegions} (f : 𝒯.FineBond → ℝ) : 0 ≤ supBond f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem ltwoBond_nonneg' {𝒯 : NestedRegions} (f : 𝒯.FineBond → ℝ) :
    0 ≤ ltwoBond f := Real.sqrt_nonneg _
theorem ltwoTensor_nonneg' {𝒯 : NestedRegions} {k : ℕ} (J : 𝒯.Tensor k) :
    0 ≤ ltwoTensor J := Real.sqrt_nonneg _
end Numbers
section Estimates
variable {𝒮 : NestedRegions} {M : ℕ} {L j N : ℕ} {S : PeriodicLattice.Scales 4 L j N}
  {r : ℝ}
end Estimates
end YangMills.Construction.CornerGreen
