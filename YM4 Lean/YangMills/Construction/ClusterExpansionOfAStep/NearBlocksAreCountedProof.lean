import YangMills.Construction.ClusterExpansionOfAStep.BallsAndBlocksOfATorusForm
import YangMills.Construction.ClusterExpansionOfAStep.NearBlocksAreCounted
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages StepSettings TorusLumps TorusFields TorusBalls
namespace ClusterExpansionOfAStep
theorem nearBlocks_card_le_units : NearBlocksCardBound := by
  intro L r n _ _ θ
  classical
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hne : {k | ∃ C : Finset (TorusSite (n * L)), C.card = k ∧ θ.2 ⊆ thickening (4 * r) C}.Nonempty :=
    ⟨θ.2.card, θ.2, rfl, fun z hz => (mem_thickening _ _ _).mpr ⟨z, hz, by simp [supDist_self]⟩⟩
  obtain ⟨C, hC, hcov⟩ := Nat.sInf_mem hne
  set U : Finset (TorusSite n) := θ.1.image (fun b => parentBlock L b.1) ∪ C.image (parentBlock L) with hU
  set m := 10 * r / L + 4 with hm
  have hmono : 9 * r / L + 1 ≤ m := by
    have : 9 * r / L ≤ 10 * r / L := Nat.div_le_div_right (by omega)
    omega
  have hsub : blocksNear L r (clusterSupportSites L θ) ⊆
      U.biUnion fun y => thickening m ({y} : Finset (TorusSite n)) := by
    intro Y hY
    obtain ⟨q, hq⟩ := (Finset.mem_filter.mp hY).2
    obtain ⟨hq1, hq2⟩ := Finset.mem_inter.mp hq
    have hqY : parentBlock L q = Y := by
      simpa [sitesInBlocks] using hq1
    obtain ⟨z, hz, hqz⟩ := (mem_thickening _ _ _).mp hq2
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
      refine Finset.mem_biUnion.mpr ⟨parentBlock L b.1, Finset.mem_union_left _
        (Finset.mem_image_of_mem _ hb), (mem_thickening _ _ _).mpr ⟨_, Finset.mem_singleton_self _, ?_⟩⟩
      rw [← hqY]
      refine (supDist_parentBlock_le_div_add_one L q b.1).trans (le_trans ?_ hmono)
      have : supDist q b.1 / L ≤ 9 * r / L := Nat.div_le_div_right (by omega)
      omega
    · obtain ⟨c, hc, hzc⟩ := (mem_thickening _ _ _).mp (hcov hz)
      refine Finset.mem_biUnion.mpr ⟨parentBlock L c, Finset.mem_union_right _
        (Finset.mem_image_of_mem _ hc), (mem_thickening _ _ _).mpr ⟨_, Finset.mem_singleton_self _, ?_⟩⟩
      rw [← hqY]
      refine (supDist_parentBlock_le_div_add_one L q c).trans (le_trans ?_ hmono)
      have h1 : supDist q c ≤ 9 * r := by
        have := supDist_triangle q z c
        omega
      have : supDist q c / L ≤ 9 * r / L := Nat.div_le_div_right h1
      omega
  have hcard : U.card ≤ supportUnitCount L r θ := by
    refine (Finset.card_union_le _ _).trans ?_
    have h2 : (C.image (parentBlock L)).card ≤ C.card := Finset.card_image_le
    have h3 : C.card = ballCoverNumber (4 * r) θ.2 := hC
    unfold supportUnitCount badBlockCount
    omega
  have h2m : 2 * m + 1 ≤ 20 * r / L + 9 := by
    have : 2 * (10 * r / L) ≤ 20 * r / L := by
      rw [Nat.le_div_iff_mul_le hL]
      have := Nat.div_mul_le_self (10 * r) L
      nlinarith
    omega
  calc (blocksNear L r (clusterSupportSites L θ)).card
      ≤ (U.biUnion fun y => thickening m ({y} : Finset (TorusSite n))).card := Finset.card_le_card hsub
    _ ≤ ∑ y ∈ U, (thickening m ({y} : Finset (TorusSite n))).card := Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ U, (2 * m + 1) ^ 4 := Finset.sum_le_sum fun y _ => card_thickening_singleton_le m y
    _ = U.card * (2 * m + 1) ^ 4 := by simp
    _ ≤ supportUnitCount L r θ * (20 * r / L + 9) ^ 4 :=
        Nat.mul_le_mul hcard (Nat.pow_le_pow_left h2m 4)
    _ = (20 * r / L + 9) ^ 4 * supportUnitCount L r θ := Nat.mul_comm _ _
end ClusterExpansionOfAStep
end YangMills.Construction
end
