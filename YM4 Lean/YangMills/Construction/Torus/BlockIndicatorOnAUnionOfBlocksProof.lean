import YangMills.Construction.Torus.BlockIndicatorOnAUnionOfBlocks
import YangMills.Construction.Torus.StandardPartitionsLayersBlocksAndBalls
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
namespace BlockUnionIndicator
variable {D : TorusData} (C : SeparatedChain D)
theorem partition_and_blocks (hP : CubesLayersBlocksBallsHold) :
    C.BlocksPartition ∧ ∀ k, ∀ y ∈ C.layerSites k, C.BlockDescription k y := by
  obtain ⟨m, hm⟩ := D.blockNumber_power
  have hL3 : 3 ≤ D.L := D.blocking.three_le_factor
  have hL : (1 : ℝ) ≤ D.L := by exact_mod_cast (by omega : 1 ≤ D.L)
  have hN : (1 : ℝ) ≤ D.blockNumber := by
    have hN3 : 3 ≤ D.blockNumber := le_trans hL3 D.le_blockNumber
    exact_mod_cast (by omega : 1 ≤ D.blockNumber)
  have hle : D.scale 0 ≤ (D.blockNumber : ℝ) * D.scale D.top := by
    have ha := D.bareSpacing_pos
    have hp1 : (1 : ℝ) ≤ (D.L : ℝ) ^ D.top := one_le_pow₀ hL
    have hp2 : D.bareSpacing ≤ (D.L : ℝ) ^ D.top * D.bareSpacing := by nlinarith
    simp only [TorusData.scale, pow_zero, one_mul]
    nlinarith
  obtain ⟨-, -, -, -, -, hpart, hblk, -⟩ := hP D C m hm 0 0 le_rfl hle
  exact ⟨hpart, hblk⟩
variable (hP : CubesLayersBlocksBallsHold)
include hP
theorem exists_mem_block_self {y : D.Space} (hy : y ∈ C.allSites) :
    ∃ x ∈ C.block y, (x : D.Space) = y := by
  have hne : {k | y ∈ C.layerSites k}.Nonempty := by
    simp only [SeparatedChain.allSites, mem_iUnion] at hy
    obtain ⟨k, -, hk⟩ := hy
    exact ⟨k, hk⟩
  exact ((partition_and_blocks C hP).2 _ _ (Nat.sInf_mem hne)).2.2.2.2.1
theorem block_subset_bareSites_stage_zero {y : D.Space} (hy : y ∈ C.allSites) :
    C.block y ⊆ D.bareSites (C.stage 0) := by
  rw [← (partition_and_blocks C hP).1.2]
  exact subset_biUnion_of_mem (u := fun y => C.block y) hy
theorem eq_of_mem_block_of_mem_block {y y' : D.Space} (hy : y ∈ C.allSites)
    (hy' : y' ∈ C.allSites) {x : D.BareSite} (hx : x ∈ C.block y) (hx' : x ∈ C.block y') :
    y = y' := by
  by_contra hne
  exact disjoint_left.1 ((partition_and_blocks C hP).1.1 y hy y' hy' hne) hx hx'
theorem block_subset_bareSites_of_isBlockUnion {W : Set D.Space} (hW : C.IsBlockUnion W)
    {y : D.Space} (hy : y ∈ C.sitesIn W) : C.block y ⊆ D.bareSites W := by
  obtain ⟨Y, -, hY, rfl⟩ := hW
  obtain ⟨x, hx, hxy⟩ := exists_mem_block_self C hP hy.1
  have hyW := hy.2
  simp only [mem_iUnion] at hyW
  obtain ⟨y', hy', hyc⟩ := hyW
  have hx' : x ∈ C.block y' := by
    change (x : D.Space) ∈ C.siteCube y'
    rw [hxy]
    exact hyc
  have he : y = y' := eq_of_mem_block_of_mem_block C hP hy.1 (hY hy') hx hx'
  intro z hz
  change (z : D.Space) ∈ ⋃ y ∈ Y, C.siteCube y
  exact mem_biUnion (he ▸ hy') hz
theorem blockIndicator_mem_bareSpaceOn {W : Set D.Space} (hW : C.IsBlockUnion W)
    {y : D.Space} (hy : y ∈ C.sitesIn W) : C.blockIndicator y ∈ C.bareSpaceOn W := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · exact indicator_of_notMem (fun h => hx (block_subset_bareSites_stage_zero C hP hy.1 h)) _
  · exact indicator_of_notMem (fun h => hx (block_subset_bareSites_of_isBlockUnion C hP hW hy h)) _
theorem blockIndicatorIn_eq {W : Set D.Space} (hW : C.IsBlockUnion W) {y : D.Space}
    (hy : y ∈ C.sitesIn W) :
    C.blockIndicatorIn W y = ⟨C.blockIndicator y, blockIndicator_mem_bareSpaceOn C hP hW hy⟩ := by
  apply Subtype.ext
  funext x
  change (D.bareSites (C.stage 0) ∩ D.bareSites W).indicator (C.blockIndicator y) x =
    C.blockIndicator y x
  by_cases hx : x ∈ C.block y
  · have hm : x ∈ D.bareSites (C.stage 0) ∩ D.bareSites W :=
      ⟨block_subset_bareSites_stage_zero C hP hy.1 hx,
        block_subset_bareSites_of_isBlockUnion C hP hW hy hx⟩
    exact indicator_of_mem hm _
  · have h0 : C.blockIndicator y x = 0 := indicator_of_notMem hx _
    rw [h0]
    by_cases hx' : x ∈ D.bareSites (C.stage 0) ∩ D.bareSites W
    · rw [indicator_of_mem hx', h0]
    · exact indicator_of_notMem hx' _
end BlockUnionIndicator
theorem BlockUnionIndicator.blockIndicatorOnBlockUnion_holds
    (hP : CubesLayersBlocksBallsHold) :
    BlockIndicatorOnBlockUnionStatement :=
  fun _ C _ hW _ hy =>
    ⟨block_subset_bareSites_of_isBlockUnion C hP hW hy,
      block_subset_bareSites_stage_zero C hP hy.1,
      blockIndicator_mem_bareSpaceOn C hP hW hy, blockIndicatorIn_eq C hP hW hy⟩
end YangMills.Construction.Weighted
