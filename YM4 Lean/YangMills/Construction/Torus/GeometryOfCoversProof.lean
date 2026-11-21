import YangMills.Construction.Torus.CoverOfTheConstructedConstantExistsProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Weighted
namespace CoverGeometryLemmas
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : _root_.YangMills.Construction.TorusMetric.torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem norm_torusProj_le {S c : ℝ} (hc : 0 ≤ c) (v : Fin 4 → ℝ) (hv : ∀ μ, |v μ| ≤ c) :
    ‖torusProj S v‖ ≤ c :=
  (pi_norm_le_iff_of_nonneg hc).2 fun μ => (addCircle_norm_coe_le_abs (v μ)).trans (hv μ)
variable {D : TorusData}
theorem three_le_L (D : TorusData) : 3 ≤ D.L := D.blocking.three_le_factor
theorem L_pos_real (D : TorusData) : (0 : ℝ) < D.L := by apply _root_.YangMills.Construction.Weighted.DistanceAvgPairMatrixNormProof.L_pos_real <;> assumption
theorem three_le_L_real (D : TorusData) : (3 : ℝ) ≤ D.L := by exact_mod_cast three_le_L D
theorem three_le_blockNumber_real (D : TorusData) : (3 : ℝ) ≤ D.blockNumber :=
  (three_le_L_real D).trans (by exact_mod_cast D.le_blockNumber)
theorem scale_pos (D : TorusData) (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
theorem scale_succ (D : TorusData) (n : ℕ) : D.scale (n + 1) = (D.L : ℝ) * D.scale n := by apply _root_.YangMills.Construction.Weighted.DistBounds.scale_succ <;> assumption
theorem scale_mono (D : TorusData) {a b : ℕ} (h : a ≤ b) : D.scale a ≤ D.scale b := by apply _root_.YangMills.Construction.Weighted.DistBounds.scale_mono <;> assumption
theorem blockSide_pos (D : TorusData) (j : ℕ) : 0 < D.blockSide j := by apply _root_.YangMills.Construction.Weighted.LocalComparison.blockSide_pos <;> assumption
theorem blockSide_eq_scale (D : TorusData) {m : ℕ} (hm : D.blockNumber = D.L ^ m) (j : ℕ) :
    D.blockSide j = D.scale (j + m) := by apply _root_.YangMills.Construction.Weighted.CubeGeometry.Scales.blockSide_eq_scale <;> assumption
variable (B : SeparatedChain D)
theorem stage_antitone {a b : ℕ} (h : a ≤ b) : B.stage b ⊆ B.stage a := by apply _root_.YangMills.Construction.Weighted.DistBounds.stage_anti <;> assumption
variable {B}
theorem partition_facts (hP : CubesLayersBlocksBallsHold) (B : SeparatedChain D) :
    B.SiteCubesTile ∧ B.BlocksPartition ∧
      (∀ n, ∀ y ∈ B.layerSites n, B.BlockDescription n y) ∧
      (∀ n, n ≤ D.top → B.LayerDecomposition n) ∧
      ∀ x : D.BareSite, (x : D.Space) ∈ B.stage 0 → (x : D.Space) ∈ B.stage (B.bareLevel x) := by
  obtain ⟨m, hm⟩ := D.blockNumber_power
  have hle : D.scale 0 ≤ (D.blockNumber : ℝ) * D.scale D.top := by
    have h1 := scale_mono D (Nat.zero_le D.top)
    have h2 := scale_pos D D.top
    nlinarith [three_le_blockNumber_real D]
  obtain ⟨-, -, -, h4, h5, h6, h7, h8, -⟩ := hP D B m hm 0 0 le_rfl hle
  exact ⟨h5, h6, h7, h4, h8⟩
theorem blockCenter_spec (hP : CubesLayersBlocksBallsHold)
    (B : SeparatedChain D) {x : D.BareSite} (hx : x ∈ D.bareSites (B.stage 0)) :
    B.blockCenter x ∈ B.allSites ∧ x ∈ B.block (B.blockCenter x) := by
  obtain ⟨-, ⟨-, hU⟩, -⟩ := partition_facts hP B
  rw [← hU] at hx
  simp only [mem_iUnion] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  exact Classical.epsilon_spec (p := fun y => y ∈ B.allSites ∧ x ∈ B.block y) ⟨y, hy, hxy⟩
theorem mem_layerSites_level {y : D.Space} (hy : y ∈ B.allSites) :
    y ∈ B.layerSites (B.level y) := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.mem_layerSites_level <;> assumption
theorem siteScale_pos (B : SeparatedChain D) (y : D.Space) : 0 < B.siteScale y := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.siteScale_pos <;> assumption
end CoverGeometryLemmas
end YangMills.Construction.Weighted
