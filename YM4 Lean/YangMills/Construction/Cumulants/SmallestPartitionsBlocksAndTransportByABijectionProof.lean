import YangMills.Construction.Cumulants.SmallestPartitionsBlocksAndTransportByABijection
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SetPartition.Elementary
section Pushforward
variable {α β : Type*} [DecidableEq α] [DecidableEq β] {A : Finset α} {A' : Finset β}
private theorem blockImage_subset_target (e : A ≃ A') (J : Finset α) : blockImage e J ⊆ A' := by
  intro y hy
  obtain ⟨l, -, rfl⟩ := (mem_blockImage e J y).1 hy
  exact (e l).2
private theorem apply_mem_blockImage (e : A ≃ A') {J : Finset α} (l : A) (hl : (l : α) ∈ J) :
    (e l : β) ∈ blockImage e J :=
  (mem_blockImage e J _).2 ⟨l, hl, rfl⟩
private theorem mem_of_apply_mem_blockImage (e : A ≃ A') {J : Finset α} (l : A)
    (h : (e l : β) ∈ blockImage e J) : (l : α) ∈ J := by
  obtain ⟨l', hl', hel⟩ := (mem_blockImage e J _).1 h
  have hll : l' = l := e.injective (Subtype.ext hel)
  rw [← hll]
  exact hl'
private theorem blockImage_eq_imp_eq (e : A ≃ A') {J K : Finset α} (hJ : J ⊆ A) (hK : K ⊆ A)
    (h : blockImage e J = blockImage e K) : J = K := by
  ext x
  constructor
  · intro hx
    have hy := apply_mem_blockImage e ⟨x, hJ hx⟩ hx
    rw [h] at hy
    exact mem_of_apply_mem_blockImage e ⟨x, hJ hx⟩ hy
  · intro hx
    have hy := apply_mem_blockImage e ⟨x, hK hx⟩ hx
    rw [← h] at hy
    exact mem_of_apply_mem_blockImage e ⟨x, hK hx⟩ hy
private theorem card_blockImage_of_subset (e : A ≃ A') {J : Finset α} (hJ : J ⊆ A) :
    (blockImage e J).card = J.card := by
  unfold blockImage
  rw [Finset.card_image_of_injective _ fun a b h => e.injective (Subtype.ext h)]
  refine Finset.card_bij (fun l _ => (l : α)) ?_ ?_ ?_
  · intro l hl
    exact (Finset.mem_filter.1 hl).2
  · intro a _ b _ h
    exact Subtype.ext h
  · intro x hx
    exact ⟨⟨x, hJ hx⟩, Finset.mem_filter.2 ⟨Finset.mem_attach _ _, hx⟩, rfl⟩
private theorem blockImage_blockImage_symm (e : A ≃ A') {K : Finset β} (hK : K ⊆ A') :
    blockImage e (blockImage e.symm K) = K := by
  ext y
  rw [mem_blockImage]
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨k, hk, hkl⟩ := (mem_blockImage e.symm K _).1 hl
    have hkl' : e.symm k = l := Subtype.ext hkl
    rw [← hkl', Equiv.apply_symm_apply]
    exact hk
  · intro hy
    refine ⟨e.symm ⟨y, hK hy⟩,
      (mem_blockImage e.symm K _).2 ⟨⟨y, hK hy⟩, hy, rfl⟩, ?_⟩
    rw [Equiv.apply_symm_apply]
private def pushforward (e : A ≃ A') (π : Partitions A) : Partitions A' where
  parts := partitionImage e π
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro I hI K hK hne
    obtain ⟨J, hJ, rfl⟩ := (mem_partitionImage e π I).1 hI
    obtain ⟨J', hJ', rfl⟩ := (mem_partitionImage e π K).1 hK
    have hd : J ≠ J' := fun hjj => hne (by rw [hjj])
    have hdis : Disjoint J J' := π.disjoint hJ hJ' hd
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨l, hl, rfl⟩ := (mem_blockImage e J y).1 hy
    exact Finset.disjoint_left.1 hdis hl (mem_of_apply_mem_blockImage e l hy')
  sup_parts := by
    ext y
    rw [Finset.mem_sup]
    constructor
    · rintro ⟨I, hI, hy⟩
      obtain ⟨J, -, rfl⟩ := (mem_partitionImage e π I).1 hI
      exact blockImage_subset_target e J hy
    · intro hy
      obtain ⟨J, hJ, hl⟩ := π.exists_mem (e.symm ⟨y, hy⟩).2
      refine ⟨blockImage e J, (mem_partitionImage e π _).2 ⟨J, hJ, rfl⟩, ?_⟩
      have h := apply_mem_blockImage e (e.symm ⟨y, hy⟩) hl
      rw [Equiv.apply_symm_apply] at h
      exact h
  bot_notMem := by
    intro hI
    obtain ⟨J, hJ, hJe⟩ := (mem_partitionImage e π ⊥).1 hI
    have hc := card_blockImage_of_subset e (π.le hJ)
    rw [hJe] at hc
    have hp : 0 < J.card := Finset.card_pos.mpr (π.nonempty_of_mem_parts hJ)
    simp at hc
    omega
private theorem partitionImage_pushforward_symm (e : A ≃ A') (ρ : Partitions A') :
    partitionImage e (pushforward e.symm ρ) = ρ.parts := by
  ext K
  rw [mem_partitionImage]
  constructor
  · rintro ⟨I, hI, rfl⟩
    obtain ⟨K, hK, rfl⟩ := (mem_partitionImage e.symm ρ I).1 hI
    have hs : K ⊆ A' := ρ.le hK
    rw [blockImage_blockImage_symm e hs]
    exact hK
  · intro hK
    have hs : K ⊆ A' := ρ.le hK
    exact ⟨blockImage e.symm K, (mem_partitionImage e.symm ρ _).2 ⟨K, hK, rfl⟩,
      blockImage_blockImage_symm e hs⟩
private theorem blockImage_injOn_parts (e : A ≃ A') (π : Partitions A) :
    Set.InjOn (blockImage e) (π.parts : Set (Finset α)) := by
  intro J hJ K hK h
  have hJ' : J ⊆ A := π.le hJ
  have hK' : K ⊆ A := π.le hK
  exact blockImage_eq_imp_eq e hJ' hK' h
private theorem partitionImage_injective (e : A ≃ A') :
    Function.Injective (partitionImage e) := by
  have key : ∀ π ρ : Partitions A, partitionImage e π = partitionImage e ρ →
      π.parts ⊆ ρ.parts := by
    intro π ρ h J hJ
    have hm : blockImage e J ∈ partitionImage e ρ := by
      rw [← h]
      exact (mem_partitionImage e π _).2 ⟨J, hJ, rfl⟩
    obtain ⟨K, hK, hKJ⟩ := (mem_partitionImage e ρ _).1 hm
    have hJ' : J ⊆ A := π.le hJ
    have hK' : K ⊆ A := ρ.le hK
    rw [← blockImage_eq_imp_eq e hK' hJ' hKJ]
    exact hK
  intro π ρ h
  exact Finpartition.ext (Finset.Subset.antisymm (key π ρ h) (key ρ π h.symm))
end Pushforward
private theorem smallCases_holds : SmallCases := by
  have hempty : ∀ (α : Type) [DecidableEq α],
      partitionSets (∅ : Finset α) = {∅} := by
    intro α _
    ext s
    simp only [partitionSets, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨π, rfl⟩
      exact parts_eq_empty_of_empty π
    · rintro rfl
      exact ⟨⊥, parts_eq_empty_of_empty _⟩
  refine ⟨hempty, ?_, ?_, singletonFree_one, ?_⟩
  · rw [Finset.univ_eq_empty]
    exact hempty _
  · ext s
    simp only [Set.mem_image, Finset.mem_coe, Set.mem_singleton_iff]
    constructor
    · rintro ⟨π, -, rfl⟩
      exact parts_eq_empty_of_empty π
    · rintro rfl
      exact ⟨⊥, mem_singletonFree_zero _, parts_eq_empty_of_empty _⟩
  · intro α _ l
    ext s
    simp only [partitionSets, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨π, rfl⟩
      have hall : ∀ K ∈ π.parts, K = {l} := fun K hK =>
        (Finset.subset_singleton_iff.1 (π.le hK)).resolve_left
          (π.nonempty_of_mem_parts hK).ne_empty
      obtain ⟨J, hJ, -⟩ := π.exists_mem (Finset.mem_singleton_self l)
      have hmem : ({l} : Finset α) ∈ π.parts := hall J hJ ▸ hJ
      exact Finset.eq_singleton_iff_unique_mem.2 ⟨hmem, hall⟩
    · rintro rfl
      exact ⟨Finpartition.indiscrete (Finset.singleton_ne_empty l), rfl⟩
private theorem blockFacts_holds : BlockFacts := by
  intro α _ A
  refine ⟨?_, ?_⟩
  · intro π l hl
    obtain ⟨J, hJ, hlJ⟩ := π.exists_mem hl
    exact ⟨J, ⟨hJ, hlJ⟩, fun K hK => π.eq_of_mem_parts hK.1 hJ hK.2 hlJ⟩
  · intro hA
    refine ⟨⟨Finpartition.indiscrete hA, rfl⟩, ?_⟩
    intro π hπ J hJ
    have hs : J ⊆ A := π.le hJ
    refine Finset.ssubset_iff_subset_ne.2 ⟨hs, ?_⟩
    rintro rfl
    apply hπ
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨hJ, fun K hK => ?_⟩
    obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts hK
    have hxJ : x ∈ J := π.le hK hx
    exact π.eq_of_mem_parts hK hJ hx hxJ
private theorem transportUnderEquiv_holds : TransportUnderEquiv := by
  intro α β _ _ A A' e
  refine ⟨⟨fun π _ => ⟨pushforward e π, rfl⟩, (partitionImage_injective e).injOn, ?_⟩, ?_⟩
  · rintro s ⟨ρ, rfl⟩
    exact ⟨pushforward e.symm ρ, Set.mem_univ _, partitionImage_pushforward_symm e ρ⟩
  · intro π
    refine ⟨⟨?_, blockImage_injOn_parts e π, ?_⟩, ?_, ?_⟩
    · intro J hJ
      exact (mem_partitionImage e π _).2 ⟨J, hJ, rfl⟩
    · intro I hI
      obtain ⟨J, hJ, rfl⟩ := (mem_partitionImage e π I).1 hI
      exact ⟨J, hJ, rfl⟩
    · intro J hJ
      have hs : J ⊆ A := π.le hJ
      exact card_blockImage_of_subset e hs
    · exact Finset.card_image_of_injOn (blockImage_injOn_parts e π)
private theorem pushforward_mem_singletonFree {q : ℕ} (e : Equiv.Perm (Finset.univ : Finset (Fin q)))
    {π : PartitionsFin q} (hπ : π ∈ singletonFree q) :
    pushforward e π ∈ singletonFree q := by
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun I hI => ?_⟩
  obtain ⟨J, hJ, rfl⟩ := (mem_partitionImage e π I).1 hI
  have hs : J ⊆ Finset.univ := π.le hJ
  rw [card_blockImage_of_subset e hs]
  exact (Finset.mem_filter.1 hπ).2 J hJ
private theorem permsPreservePartitions_holds : PermsPreservePartitions := by
  intro q _ e
  refine ⟨(transportUnderEquiv_holds (Fin q) (Fin q) _ _ e).1.image_eq, ?_⟩
  ext s
  simp only [Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨π, hπ, rfl⟩
    exact ⟨pushforward e π, pushforward_mem_singletonFree e hπ, rfl⟩
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨pushforward e.symm ρ, pushforward_mem_singletonFree e.symm hρ,
      partitionImage_pushforward_symm e ρ⟩
theorem basicFacts_holds : BasicFacts :=
  ⟨smallCases_holds, blockFacts_holds, transportUnderEquiv_holds, permsPreservePartitions_holds⟩
end YangMills.Construction.SetPartition.Elementary
