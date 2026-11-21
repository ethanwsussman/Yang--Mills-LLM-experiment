import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.InequalitiesOnCubesOfTheFirstKindProof
import YangMills.Construction.DirichletOperator.RegularityOfTheLocalOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
open CubeTorus (torusSetting levelSpacing tensorModulusAt TensorAnchorSupported)
namespace CubeOperators
variable {𝒮 : NestedRegions} {M : ℕ}
section Nonneg
variable {𝒯 : NestedRegions}
theorem supSite_nonneg (f : 𝒯.FineSite → ℝ) : 0 ≤ supSite f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem supBond_nonneg (f : 𝒯.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
theorem supTensor_nonneg {r : ℕ} (T : 𝒯.Tensor r) : 0 ≤ supTensor T :=
  Real.iSup_nonneg fun _ => supBond_nonneg _
theorem holderSite_nonneg (α s : ℝ) (f : 𝒯.FineSite → ℝ) :
    0 ≤ holderSite α s f := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.holderSite_nonneg <;> assumption
theorem holderBond_nonneg (α s : ℝ) (f : 𝒯.FineBond → ℝ) :
    0 ≤ holderBond α s f := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.holderBond_nonneg <;> assumption
theorem holderTensor_nonneg {r : ℕ} (α s : ℝ) (T : 𝒯.Tensor r) :
    0 ≤ holderTensor α s T :=
  Real.iSup_nonneg fun _ => holderBond_nonneg _ _ _
theorem sourceSize_nonneg {r : ℕ} (ε s : ℝ) (T : 𝒯.Tensor r) :
    0 ≤ sourceSize ε s T := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.sourceNormSum_nonneg <;> assumption
theorem ltwoBond_nonneg (f : 𝒯.FineBond → ℝ) : 0 ≤ ltwoBond f := Real.sqrt_nonneg _
theorem ltwoTensor_nonneg {r : ℕ} (T : 𝒯.Tensor r) : 0 ≤ ltwoTensor T := by apply _root_.YangMills.Construction.CornerGreen.ltwoTensor_nonneg' <;> assumption
end Nonneg
theorem levelSpacing_nonneg (Q : LevelCube 𝒮 M) : 0 ≤ levelSpacing Q := by
  have hξ := 𝒮.ξ_pos
  have hL : (0 : ℝ) < 𝒮.L := by
    have := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 0 < 𝒮.L)
  simp only [levelSpacing, NestedRegions.scale, scaleSpacing]
  positivity
theorem torusDist_nonneg (Q : LevelCube 𝒮 M) (o o' : (torusSetting Q).Point) :
    0 ≤ Q.torusDist o o' := by
  refine mul_nonneg (inv_nonneg.mpr (levelSpacing_nonneg Q)) (Real.sInf_nonneg ?_)
  rintro r ⟨v, _, rfl⟩
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _
end CubeOperators
end YangMills.Construction
