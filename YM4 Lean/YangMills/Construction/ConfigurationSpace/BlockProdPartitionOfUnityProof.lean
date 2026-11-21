import YangMills.Construction.BumpFunctions.SmoothBumpsGevreyBounds
import YangMills.Construction.ConfigurationSpace.BlockProdPartitionOfUnity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
theorem blockProdPartitionOfUnity_of_gevreyBounds
    (hb : BumpFunctions.SmoothBumpsGevreyBounds) : BlockProdPartitionOfUnity := by
  obtain ⟨-, -, -, ⟨-, -, -, hsum, hcard⟩, -, -⟩ := hb
  intro n j x
  let t : CoordIndex n → ℝ := fun ι => 2 * coords x ι / WhitneyScales.whitneySide j
  have hfin : ∀ ι, (Function.support fun l : ℤ =>
      BumpFunctions.mollifiedUnitIndicator (t ι - l)).Finite :=
    fun ι => Set.finite_of_encard_le_coe (k := 2) (hcard (t ι))
  let F : CoordIndex n → Finset ℤ := fun ι => (hfin ι).toFinset
  have hF : ∀ ι l, l ∈ F ι ↔ BumpFunctions.mollifiedUnitIndicator (t ι - l) ≠ 0 := by
    intro ι l
    simp [F]
  have hFcard : ∀ ι, (F ι).card ≤ 2 := by
    intro ι
    have h := hcard (t ι)
    rw [Set.Finite.encard_eq_coe_toFinset_card (hfin ι)] at h
    exact_mod_cast h
  have hprod : ∀ z : IntPoint n,
      blockProd j z x = ∏ ι, BumpFunctions.mollifiedUnitIndicator (t ι - z ι) := fun z => rfl
  have hset : {z : IntPoint n | blockProd j z x ≠ 0} =
      (Fintype.piFinset F : Set (IntPoint n)) := by
    ext z
    simp only [Set.mem_ofPred_eq, hprod, Finset.prod_ne_zero_iff, Finset.mem_univ, true_imp_iff,
      Finset.mem_coe, Fintype.mem_piFinset, hF]
  refine ⟨?_, ?_⟩
  · have hle : (Fintype.piFinset F).card ≤ 2 ^ (4 * n) := by
      rw [Fintype.card_piFinset]
      calc ∏ ι, (F ι).card ≤ ∏ _ι : CoordIndex n, 2 :=
            Finset.prod_le_prod' fun ι _ => hFcard ι
        _ = 2 ^ (4 * n) := by
            simp [Finset.prod_const, Fintype.card_prod, mul_comm]
    unfold setCard
    rw [hset, Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hle
  · have hzero : ∀ z ∉ Fintype.piFinset F, blockProd j z x = 0 := by
      intro z hz
      by_contra hne
      exact hz (by simpa using (Set.ext_iff.mp hset z).mp hne)
    rw [tsum_eq_sum hzero]
    have hone : ∀ ι, ∑ l ∈ F ι, BumpFunctions.mollifiedUnitIndicator (t ι - l) = 1 := by
      intro ι
      rw [← hsum (t ι)]
      refine (tsum_eq_sum fun l hl => ?_).symm
      by_contra hne
      exact hl ((hF ι l).mpr hne)
    simp only [hprod]
    rw [← Finset.prod_univ_sum F fun ι l => BumpFunctions.mollifiedUnitIndicator (t ι - l)]
    simp [hone]
end YangMills.Construction.ConfigurationSpace
end
