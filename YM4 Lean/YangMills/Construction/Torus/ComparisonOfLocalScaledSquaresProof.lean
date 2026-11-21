import YangMills.Construction.HoleBesideASecondHole.CellsPutBackProof
import YangMills.Construction.Lattice.CubesOfTwoStandardPartitionsProof
import YangMills.Construction.Torus.BoundOnTheScaledRemainderBlocksProof
import YangMills.Construction.Torus.ChangeOfDomainAndBoundaryConditionsProof
import YangMills.Construction.Torus.DistanceAveragesWholePairMatricesAndNormsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted.LocalComparison
open Set TorusMetric
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
variable {D : TorusData}
theorem three_le_L (D : TorusData) : (3 : ℝ) ≤ D.L := by
  exact_mod_cast D.blocking.three_le_factor
theorem L_pos_real (D : TorusData) : (0 : ℝ) < D.L := by linarith [three_le_L D]
theorem three_le_blockNumber (D : TorusData) : (3 : ℝ) ≤ D.blockNumber :=
  (three_le_L D).trans (by exact_mod_cast D.le_blockNumber)
theorem scale_pos (D : TorusData) (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
theorem scale_succ (D : TorusData) (n : ℕ) : D.scale (n + 1) = (D.L : ℝ) * D.scale n := by apply _root_.YangMills.Construction.Weighted.DistBounds.scale_succ <;> assumption
theorem scale_mono (D : TorusData) {a b : ℕ} (h : a ≤ b) : D.scale a ≤ D.scale b := by apply _root_.YangMills.Construction.Weighted.DistBounds.scale_mono <;> assumption
theorem blockSide_pos (D : TorusData) (j : ℕ) : 0 < D.blockSide j :=
  mul_pos (by linarith [three_le_blockNumber D]) (scale_pos D j)
theorem abs_clamp_sub_le (a b : ℝ) : |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |a - b| := by apply _root_.YangMills.Construction.Reinsertion.abs_clamp_sub_clamp_le <;> assumption
section Sites
variable (B : SeparatedChain D)
variable {B}
theorem block_subset_bareSites (hb : B.BlocksPartition) {y : D.Space} (hy : y ∈ B.allSites) :
    B.block y ⊆ D.bareSites (B.stage 0) := by apply _root_.YangMills.Construction.Weighted.DomainChange.block_subset_bareSites <;> assumption
theorem finite_allSites (hs : ∀ n, ∀ y ∈ B.layerSites n, B.BlockDescription n y) :
    B.allSites.Finite := by apply _root_.YangMills.Construction.Weighted.AvgGreenSqBounds.allSites_finite <;> assumption
theorem blockCenter_spec (hb : B.BlocksPartition) {x : D.BareSite}
    (hx : x ∈ D.bareSites (B.stage 0)) :
    B.blockCenter x ∈ B.allSites ∧ x ∈ B.block (B.blockCenter x) := by
  rw [← hb.2] at hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hx
  exact Classical.epsilon_spec (p := fun y => y ∈ B.allSites ∧ x ∈ B.block y) ⟨y, hy, hxy⟩
end Sites
section Cutoff
variable {B : SeparatedChain D}
theorem siteScale_pos (B : SeparatedChain D) (y : D.Space) : 0 < B.siteScale y := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.siteScale_pos <;> assumption
end Cutoff
section Blocks
instance instFintypeBareSite (D : TorusData) : Fintype D.BareSite :=
  @Fintype.ofFinite _ D.bareSite_finite
theorem finsum_mem_eq_sum_indicator {α : Type*} [Fintype α] (s : Set α) (f : α → ℝ) :
    ∑ᶠ x ∈ s, f x = ∑ x, s.indicator f x := by
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
theorem siteNorm_nonneg (E : Set D.BareSite) (f : D.BareSite → ℝ) :
    0 ≤ TorusData.siteNorm E f := Real.sqrt_nonneg _
theorem siteNorm_le_mul {E : Set D.BareSite} {f g : D.BareSite → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (h : ∀ x ∈ E, |f x| ≤ τ * |g x|) : TorusData.siteNorm E f ≤ τ * TorusData.siteNorm E g := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.siteNorm_le_mul <;> assumption
variable (B : SeparatedChain D)
end Blocks
section Numbers
theorem greenDecayRate_pos (D : TorusData) : 0 < greenDecayRate 4 D.L := by
  have := L_pos_real D
  unfold greenDecayRate
  positivity
theorem coercivityConst_pos (D : TorusData) : 0 < coercivityConst D.L := by
  have h := three_le_L D
  have h1 : ((D.L : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  unfold coercivityConst
  linarith
theorem gapNumber_mul_blockNumber_pos (D : TorusData) : 0 < (D.gapNumber : ℝ) * (D.blockNumber : ℝ) := by
  have h1 : (3 : ℝ) ≤ D.gapNumber :=
    (three_le_L D).trans (by exact_mod_cast D.le_gapNumber)
  have h2 := three_le_blockNumber D
  positivity
end Numbers
section Sums
variable (B : SeparatedChain D)
theorem weightedDist_nonneg (x x' : D.Space) : 0 ≤ B.weightedDistance x x' := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.weightedDistance_nonneg <;> assumption
end Sums
section Main
variable {B : SeparatedChain D}
end Main
end YangMills.Construction.Weighted.LocalComparison
