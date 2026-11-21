import YangMills.Construction.ConfigurationSpace.BlockProdPartitionOfUnity
import YangMills.Construction.ConfigurationSpace.DiagonalCutoffBounds
import YangMills.Construction.ConfigurationSpace.WhitneyPartitionOfUnity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
theorem whitneyPartitionOfUnityProperty_of (hblock : BlockProdPartitionOfUnity)
    (hcut : DiagonalCutoffProperties) : WhitneyPartitionOfUnityProperty := by
  classical
  intro n hn x hx
  have hc := (hcut n hn 0).2.2
  obtain ⟨hAfin, hAsum⟩ := hc.2.2.1 x hx
  have hthree := hc.2.2.2.2.2.2.2.1 x
  set A : Finset ℕ := hAfin.toFinset with hAdef
  have hmemA : ∀ j, j ∈ A ↔ shellDiff j x ≠ 0 := fun j => by simp [hAdef]
  have hAcard : A.card ≤ 3 := by
    have hsub : (A : Set ℕ) ⊆ {j' : ℕ | x ∈ tsupport (shellDiff (n := n) j')} := by
      intro j hj
      exact subset_tsupport _ ((hmemA j).1 hj)
    have hle := (Set.encard_le_encard hsub).trans hthree
    rw [Set.encard_coe_eq_coe_finsetCard] at hle
    exact_mod_cast hle
  have hBle : ∀ j : ℕ, {z : IntPoint n | blockProd j z x ≠ 0}.encard ≤
      ((2 ^ (4 * n) : ℕ) : ℕ∞) := fun j => by
    have h := (hblock n j x).1
    push_cast
    exact h
  have hBfin : ∀ j : ℕ, {z : IntPoint n | blockProd j z x ≠ 0}.Finite :=
    fun j => Set.finite_of_encard_le_coe (hBle j)
  set B : ℕ → Finset (IntPoint n) := fun j => (hBfin j).toFinset with hBdef
  have hmemB : ∀ j z, z ∈ B j ↔ blockProd j z x ≠ 0 := fun j z => by simp [hBdef]
  have hBcard : ∀ j, (B j).card ≤ 2 ^ (4 * n) := fun j => by
    have h := hBle j
    rw [(hBfin j).encard_eq_coe_toFinset_card] at h
    exact_mod_cast h
  have hBsum : ∀ j, ∑ z ∈ B j, blockProd j z x = 1 := fun j => by
    rw [← (hblock n j x).2]
    refine (tsum_eq_sum fun z hz => ?_).symm
    by_contra h
    exact hz ((hmemB j z).2 h)
  set T : Finset (ℕ × IntPoint n) := A.biUnion fun j => (B j).image (Prod.mk j) with hTdef
  have hT : ∀ p : ℕ × IntPoint n, whitneyPiece p.1 p.2 x ≠ 0 → p ∈ T := by
    rintro ⟨j, z⟩ h
    have h' : shellDiff j x * blockProd j z x ≠ 0 := h
    refine Finset.mem_biUnion.2 ⟨j, (hmemA j).2 (left_ne_zero_of_mul h'), ?_⟩
    exact Finset.mem_image.2 ⟨z, (hmemB j z).2 (right_ne_zero_of_mul h'), rfl⟩
  have hTcard : T.card ≤ 3 * 2 ^ (4 * n) :=
    (Finset.card_biUnion_le_card_mul A _ (2 ^ (4 * n)) fun j _ =>
      Finset.card_image_le.trans (hBcard j)).trans (Nat.mul_le_mul_right _ hAcard)
  constructor
  · have hsub : {p : ℕ × IntPoint n | whitneyPiece p.1 p.2 x ≠ 0} ⊆ (T : Set _) :=
      fun p hp => hT p hp
    have hle := Set.encard_le_encard hsub
    rw [Set.encard_coe_eq_coe_finsetCard] at hle
    refine hle.trans ?_
    have : ((T.card : ℕ) : ℕ∞) ≤ ((3 * 2 ^ (4 * n) : ℕ) : ℕ∞) := by exact_mod_cast hTcard
    simpa using this
  · set f : ℕ × IntPoint n → ℝ := fun p => whitneyPiece p.1 p.2 x with hf
    have hind : (pieceIndexSet n).indicator f = f := by
      funext p
      by_cases hp : p ∈ pieceIndexSet n
      · exact Set.indicator_of_mem hp f
      · rw [Set.indicator_of_notMem hp]
        by_contra h
        exact hp ⟨x, fun h0 => h h0.symm⟩
    have hsubtype : ∑' p : pieceIndexSet n, whitneyPiece p.1.1 p.1.2 x = ∑' p, f p := by
      have h := tsum_subtype (pieceIndexSet n) f
      rw [hind] at h
      exact h
    rw [hsubtype, tsum_eq_sum (s := T) fun p hp => by
      by_contra h
      exact hp (hT p h)]
    rw [Finset.sum_biUnion]
    · have hinner : ∀ j ∈ A, ∑ p ∈ (B j).image (Prod.mk j), f p = shellDiff j x := by
        intro j _
        rw [Finset.sum_image fun a _ b _ h => (Prod.mk.inj h).2]
        change ∑ z ∈ B j, shellDiff j x * blockProd j z x = _
        rw [← Finset.mul_sum, hBsum, mul_one]
      rw [Finset.sum_congr rfl hinner, ← hAsum]
      refine (tsum_eq_sum fun j hj => ?_).symm
      by_contra h
      exact hj ((hmemA j).2 h)
    · intro a _ b _ hab
      refine Finset.disjoint_left.2 fun p hpa hpb => hab ?_
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.1 hpa
      obtain ⟨w, _, hw⟩ := Finset.mem_image.1 hpb
      exact (Prod.mk.inj hw).1.symm
end YangMills.Construction.ConfigurationSpace
end
