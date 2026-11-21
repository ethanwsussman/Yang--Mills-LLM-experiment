import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.AdjointDefectOfACubeAsItsSourcesProof
import YangMills.Construction.DirichletOperator.CubeTermsVanishAwayFromASiteProof
import YangMills.Construction.DirichletOperator.DivergenceSourceOnTheTorusOfACube
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open RegionSequence RegionSequence.NestedRegions PartitionCubes
open CubeTorus (torusSetting levelSpacing TensorAnchorSupported)
open CubeOperators (cubeDivOne sourceSize)
open CubeDivergence (leibnizRemainder pushBonds formDiv pushedRemainder)
namespace CubeSourceProof
variable {𝒮 : NestedRegions} {M : ℕ}
theorem supNorm_eq_norm {S : ℝ} (p : Torus.PeriodicTorus 4 S) : Torus.supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem norm_unitStep_le (ν : Fin 4) : ‖(Dirichlet.unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point)‖ ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.CubeDivergence.norm_unitStep_le <;> assumption
theorem mem_cubeHalfSide_iff {𝒯 : NestedRegions} (o x : 𝒯.Point) (r : ℝ) :
    x ∈ cubeHalfSide o r ↔ ‖x - o‖ ≤ r := by apply _root_.YangMills.Construction.ApproxInverseTerms.mem_cubeHalfSide_iff <;> assumption
theorem ξ_le_levelScale (y : 𝒮.Point) : 𝒮.ξ ≤ 𝒮.levelScale y := by apply _root_.YangMills.Construction.DivSourceEstimate.ξ_le_levelScale <;> assumption
theorem finite_fineBond (hl : Torus.TorusLengthsStatement) (𝒯 : NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem bondInner_eq_sum {𝒯 : NestedRegions} [Fintype 𝒯.FineBond] (A B : 𝒯.FineBond → ℝ) :
    bondInner A B = 𝒯.ξ ^ 4 * ∑ b, A b * B b := by
  simp only [bondInner, finsum_eq_sum_of_fintype]
theorem bondInner_comm {𝒯 : NestedRegions} (A B : 𝒯.FineBond → ℝ) :
    bondInner A B = bondInner B A := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
theorem tensorInner_comm {𝒯 : NestedRegions} {r : ℕ} (J J' : 𝒯.Tensor r) :
    tensorInner J J' = tensorInner J' J :=
  Finset.sum_congr rfl fun _ _ => bondInner_comm _ _
theorem supBond_nonneg {𝒯 : NestedRegions} (f : 𝒯.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
theorem abs_le_supBond {𝒯 : NestedRegions} [Finite 𝒯.FineBond] (f : 𝒯.FineBond → ℝ)
    (b : 𝒯.FineBond) : |f b| ≤ supBond f :=
  le_ciSup (f := fun b => ‖f b‖) (Set.finite_range _).bddAbove b
theorem supTensor_nonneg {𝒯 : NestedRegions} {r : ℕ} (J : 𝒯.Tensor r) : 0 ≤ supTensor J :=
  Real.iSup_nonneg fun _ => supBond_nonneg _
theorem supBond_le_supTensor {𝒯 : NestedRegions} {r : ℕ} (J : 𝒯.Tensor r) (ν : Fin r → Fin 4) :
    supBond (J ν) ≤ supTensor J :=
  le_ciSup (f := fun ν => supBond (J ν)) (Set.finite_range _).bddAbove ν
theorem abs_le_supTensor {𝒯 : NestedRegions} [Finite 𝒯.FineBond] {r : ℕ} (J : 𝒯.Tensor r)
    (ν : Fin r → Fin 4) (b : 𝒯.FineBond) : |J ν b| ≤ supTensor J :=
  (abs_le_supBond _ b).trans (supBond_le_supTensor J ν)
theorem holderBond_nonneg {𝒯 : NestedRegions} {α r : ℝ} (hr : 0 ≤ r)
    (f : 𝒯.FineBond → ℝ) : 0 ≤ holderBond α r f := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨b, b', -, hd, -, rfl⟩
  exact mul_nonneg (Real.rpow_nonneg (div_nonneg hr hd.le) _) (norm_nonneg _)
theorem holderTensor_nonneg {𝒯 : NestedRegions} {k : ℕ} {α r : ℝ} (hr : 0 ≤ r)
    (J : 𝒯.Tensor k) : 0 ≤ holderTensor α r J :=
  Real.iSup_nonneg fun _ => holderBond_nonneg hr _
section Transfers
variable (𝔏 : CubeSystem 𝒮)
end Transfers
theorem leibnizRemainder_apply (Φ : 𝒮.FineSite → ℝ) (J : 𝒮.Tensor 1) (b : 𝒮.FineBond) :
    leibnizRemainder Φ J b =
      ∑ ν, Dirichlet.translateBackward ν (Dirichlet.forwardDiff ν Φ) b.source *
        J (constIdx ν) (shiftDown ν b) := by
  simp only [leibnizRemainder, Finset.sum_apply, smulSiteBond, smul_eq_mul]
theorem ξ_le_scale (n : ℕ) : 𝒮.ξ ≤ 𝒮.scale n := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.ξ_le_scale <;> assumption
theorem holderSite_nonneg {𝒯 : NestedRegions} {α r : ℝ} (hr : 0 ≤ r)
    (f : 𝒯.FineSite → ℝ) : 0 ≤ holderSite α r f := by apply _root_.YangMills.Construction.DivSourceEstimate.holderSite_nonneg <;> assumption
theorem scale_le_scale_succ (n : ℕ) : 𝒮.scale n ≤ 𝒮.scale (n + 1) := by
  have hL : (1 : ℝ) ≤ 𝒮.L := by
    have : 13 ≤ 𝒮.L := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 1 ≤ 𝒮.L)
  have hξ := 𝒮.ξ_pos
  have hn : (0 : ℝ) < (𝒮.L : ℝ) ^ n := by positivity
  simp only [RegionSequence.NestedRegions.scale, Torus.scaleSpacing, zpow_natCast]
  rw [pow_succ]
  have : (𝒮.L : ℝ) ^ n * 1 ≤ (𝒮.L : ℝ) ^ n * 𝒮.L := mul_le_mul_of_nonneg_left hL hn.le
  nlinarith
end CubeSourceProof
end YangMills.Construction
