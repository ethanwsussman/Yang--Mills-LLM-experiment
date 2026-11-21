import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongParametersIsASumOfCumulants
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Cumulants
namespace YangMills.Construction.DensityMeans
section Partitions
variable {α : Type} [DecidableEq α]
private structure IsPartsOf (S : Finset α) (P : Finset (Finset α)) : Prop where
  nonempty : ∀ B ∈ P, B.Nonempty
  pairwise_disjoint : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C
  biUnion_eq : P.biUnion id = S
private def partsFamily (S : Finset α) : Finset (Finset (Finset α)) :=
  (Finset.univ : Finset (Finpartition S)).image Finpartition.parts
private theorem mem_partsFamily {S : Finset α} {P : Finset (Finset α)} : P ∈ partsFamily S ↔ IsPartsOf S P := by
  constructor
  · intro h
    obtain ⟨π, -, rfl⟩ := Finset.mem_image.1 h
    refine ⟨fun B hB => π.nonempty_of_mem_parts hB, fun B hB C hC h => π.disjoint hB hC h, ?_⟩
    rw [← Finset.sup_eq_biUnion]
    exact π.sup_parts
  · intro h
    refine Finset.mem_image.2 ⟨⟨P, ?_, ?_, ?_⟩, Finset.mem_univ _, rfl⟩
    · exact Finset.supIndep_iff_pairwiseDisjoint.2 fun B hB C hC hBC => h.pairwise_disjoint B hB C hC hBC
    · rw [Finset.sup_eq_biUnion]
      exact h.biUnion_eq
    · exact fun h0 => Finset.not_nonempty_empty (h.nonempty _ h0)
private theorem sum_finpartition_eq (S : Finset α) (F : Finset (Finset α) → ℝ) :
    ∑ π : Finpartition S, F π.parts = ∑ P ∈ partsFamily S, F P := by
  rw [partsFamily, Finset.sum_image]
  intro π _ π' _ h
  exact Finpartition.ext h
private theorem IsPartsOf.subset {S : Finset α} {P : Finset (Finset α)} (h : IsPartsOf S P) {B : Finset α} (hB : B ∈ P) :
    B ⊆ S := by
  rw [← h.biUnion_eq]
  exact Finset.subset_biUnion_of_mem id hB
private theorem IsPartsOf.mem_iff {S : Finset α} {P : Finset (Finset α)} (h : IsPartsOf S P) {x : α} :
    x ∈ S ↔ ∃ B ∈ P, x ∈ B := by
  rw [← h.biUnion_eq]
  simp
private theorem IsPartsOf.union {W V : Finset α} {A R : Finset (Finset α)} (hA : IsPartsOf W A) (hR : IsPartsOf V R)
    (h : Disjoint W V) : IsPartsOf (W ∪ V) (A ∪ R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    rcases Finset.mem_union.1 hB with hB | hB
    · exact hA.nonempty B hB
    · exact hR.nonempty B hB
  · intro B hB C hC hBC
    rcases Finset.mem_union.1 hB with hB | hB <;> rcases Finset.mem_union.1 hC with hC | hC
    · exact hA.pairwise_disjoint B hB C hC hBC
    · exact h.mono (hA.subset hB) (hR.subset hC)
    · exact (h.mono (hA.subset hC) (hR.subset hB)).symm
    · exact hR.pairwise_disjoint B hB C hC hBC
  · ext x
    simp only [Finset.mem_biUnion, Finset.mem_union, id, hA.mem_iff, hR.mem_iff]
    constructor
    · rintro ⟨B, hB | hB, hx⟩
      · exact Or.inl ⟨B, hB, hx⟩
      · exact Or.inr ⟨B, hB, hx⟩
    · rintro (⟨B, hB, hx⟩ | ⟨B, hB, hx⟩)
      · exact ⟨B, Or.inl hB, hx⟩
      · exact ⟨B, Or.inr hB, hx⟩
private theorem IsPartsOf.disjoint_parts {W V : Finset α} {A R : Finset (Finset α)} (hA : IsPartsOf W A) (hR : IsPartsOf V R)
    (h : Disjoint W V) : Disjoint A R := by
  rw [Finset.disjoint_left]
  intro B hB hB'
  obtain ⟨x, hx⟩ := hA.nonempty B hB
  exact Finset.disjoint_left.1 h (hA.subset hB hx) (hR.subset hB' hx)
private theorem IsPartsOf.biUnion_of_subset {Y : Finset α} {P A : Finset (Finset α)} (hP : IsPartsOf Y P) (hA : A ⊆ P) :
    IsPartsOf (A.biUnion id) A :=
  ⟨fun B hB => hP.nonempty B (hA hB), fun B hB C hC h => hP.pairwise_disjoint B (hA hB) C (hA hC) h, rfl⟩
private theorem IsPartsOf.sdiff {Y : Finset α} {P A : Finset (Finset α)} (hP : IsPartsOf Y P) (hA : A ⊆ P) :
    IsPartsOf (Y \ A.biUnion id) (P \ A) := by
  refine ⟨fun B hB => hP.nonempty B (Finset.mem_sdiff.1 hB).1,
    fun B hB C hC h => hP.pairwise_disjoint B (Finset.mem_sdiff.1 hB).1 C (Finset.mem_sdiff.1 hC).1 h, ?_⟩
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_sdiff, id]
  constructor
  · rintro ⟨B, ⟨hB, hBA⟩, hx⟩
    refine ⟨hP.subset hB hx, ?_⟩
    rintro ⟨C, hC, hxC⟩
    have hne : B ≠ C := fun e => hBA (e ▸ hC)
    exact Finset.disjoint_left.1 (hP.pairwise_disjoint B hB C (hA hC) hne) hx hxC
  · rintro ⟨hx, hn⟩
    obtain ⟨B, hB, hxB⟩ := hP.mem_iff.1 hx
    exact ⟨B, ⟨hB, fun hBA => hn ⟨B, hBA, hxB⟩⟩, hxB⟩
private theorem isPartsOf_singleton {C : Finset α} (hC : C.Nonempty) : IsPartsOf C {C} := by
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    rw [Finset.mem_singleton.1 hB]
    exact hC
  · intro B hB D hD h
    exact absurd ((Finset.mem_singleton.1 hB).trans (Finset.mem_singleton.1 hD).symm) h
  · simp
private theorem partsFamily_empty : partsFamily (∅ : Finset α) = {∅} := by
  ext P
  rw [mem_partsFamily, Finset.mem_singleton]
  constructor
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro B hB
    obtain ⟨x, hx⟩ := h.nonempty B hB
    exact Finset.notMem_empty x (h.subset hB hx)
  · rintro rfl
    exact ⟨by simp, by simp, by simp⟩
private theorem sum_partition_split (Y : Finset α) (F : Finset (Finset α) → Finset (Finset α) → ℝ) :
    ∑ P ∈ partsFamily Y, ∑ A ∈ P.powerset, F A (P \ A) =
      ∑ W ∈ Y.powerset, ∑ A ∈ partsFamily W, ∑ R ∈ partsFamily (Y \ W), F A R := by
  have e1 := Finset.sum_sigma' (partsFamily Y) (fun P => P.powerset) (fun P A => F A (P \ A))
  have e2 := Finset.sum_sigma' Y.powerset (fun W => partsFamily W ×ˢ partsFamily (Y \ W)) (fun _ x => F x.1 x.2)
  rw [e1]
  have e3 : ∑ W ∈ Y.powerset, ∑ A ∈ partsFamily W, ∑ R ∈ partsFamily (Y \ W), F A R =
      ∑ W ∈ Y.powerset, ∑ x ∈ partsFamily W ×ˢ partsFamily (Y \ W), F x.1 x.2 :=
    Finset.sum_congr rfl fun W _ => (Finset.sum_product (partsFamily W) (partsFamily (Y \ W)) (fun x => F x.1 x.2)).symm
  rw [e3, e2]
  refine Finset.sum_nbij' (fun x => ⟨x.2.biUnion id, (x.2, x.1 \ x.2)⟩)
    (fun y => ⟨y.2.1 ∪ y.2.2, y.2.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨P, A⟩ h
    simp only [Finset.mem_sigma, Finset.mem_powerset, mem_partsFamily] at h
    obtain ⟨hP, hA⟩ := h
    simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_product, mem_partsFamily]
    refine ⟨?_, hP.biUnion_of_subset hA, hP.sdiff hA⟩
    intro x hx
    obtain ⟨B, hB, hxB⟩ := Finset.mem_biUnion.1 hx
    exact hP.subset (hA hB) hxB
  · rintro ⟨W, A, R⟩ h
    simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_product, mem_partsFamily] at h
    obtain ⟨hW, hA, hR⟩ := h
    simp only [Finset.mem_sigma, Finset.mem_powerset, mem_partsFamily]
    refine ⟨?_, Finset.subset_union_left⟩
    have := hA.union hR Finset.disjoint_sdiff
    rwa [Finset.union_sdiff_of_subset hW] at this
  · rintro ⟨P, A⟩ h
    simp only [Finset.mem_sigma, Finset.mem_powerset] at h
    simp [Finset.union_sdiff_of_subset h.2]
  · rintro ⟨W, A, R⟩ h
    simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_product, mem_partsFamily] at h
    obtain ⟨hW, hA, hR⟩ := h
    have hd : Disjoint A R := hA.disjoint_parts hR Finset.disjoint_sdiff
    have h1 : A.biUnion id = W := hA.biUnion_eq
    simp [Finset.union_sdiff_cancel_left hd, h1]
  · rintro ⟨P, A⟩ _
    rfl
private theorem sum_partition_pointed (V : Finset α) (G : Finset (Finset α) → Finset α → ℝ) :
    ∑ R ∈ partsFamily V, ∑ C ∈ R, G (R.erase C) C =
      ∑ C ∈ V.powerset.erase ∅, ∑ Q ∈ partsFamily (V \ C), G Q C := by
  have e1 := Finset.sum_sigma' (partsFamily V) (fun R => R) (fun R C => G (R.erase C) C)
  have e2 := Finset.sum_sigma' (V.powerset.erase ∅) (fun C => partsFamily (V \ C)) (fun C Q => G Q C)
  rw [e1, e2]
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1.erase x.2⟩) (fun y => ⟨insert y.1 y.2, y.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨R, C⟩ h
    simp only [Finset.mem_sigma, mem_partsFamily] at h
    obtain ⟨hR, hC⟩ := h
    simp only [Finset.mem_sigma, Finset.mem_erase, Finset.mem_powerset, mem_partsFamily]
    refine ⟨⟨(hR.nonempty C hC).ne_empty, hR.subset hC⟩, ?_⟩
    have := hR.sdiff (Finset.singleton_subset_iff.2 hC)
    simpa [Finset.sdiff_singleton_eq_erase] using this
  · rintro ⟨C, Q⟩ h
    simp only [Finset.mem_sigma, Finset.mem_erase, Finset.mem_powerset, mem_partsFamily] at h
    obtain ⟨⟨hC0, hCV⟩, hQ⟩ := h
    simp only [Finset.mem_sigma, mem_partsFamily]
    refine ⟨?_, Finset.mem_insert_self _ _⟩
    have := (isPartsOf_singleton (Finset.nonempty_iff_ne_empty.2 hC0)).union hQ Finset.disjoint_sdiff
    rwa [Finset.union_sdiff_of_subset hCV, ← Finset.insert_eq] at this
  · rintro ⟨R, C⟩ h
    simp only [Finset.mem_sigma] at h
    simp [Finset.insert_erase h.2]
  · rintro ⟨C, Q⟩ h
    simp only [Finset.mem_sigma, Finset.mem_erase, Finset.mem_powerset, mem_partsFamily] at h
    obtain ⟨⟨hC0, hCV⟩, hQ⟩ := h
    have hn : C ∉ Q := by
      intro hc
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hC0
      exact (Finset.mem_sdiff.1 (hQ.subset hc hx)).2 hx
    simp [Finset.erase_insert hn]
  · rintro ⟨R, C⟩ _
    rfl
private theorem sum_partition_insert {a : α} {U : Finset α} (ha : a ∉ U) (F : Finset (Finset α) → ℝ) :
    ∑ P ∈ partsFamily (insert a U), F P =
      ∑ W ∈ U.powerset, ∑ Q ∈ partsFamily (U \ W), F (insert (insert a W) Q) := by
  have e1 : ∀ P ∈ partsFamily (insert a U), F P = ∑ C ∈ P, if a ∈ C then F (insert C (P.erase C)) else 0 := by
    intro P hP
    have hP' := mem_partsFamily.1 hP
    obtain ⟨C, hC, haC⟩ := hP'.mem_iff.1 (Finset.mem_insert_self a U)
    rw [Finset.sum_eq_single_of_mem C hC, if_pos haC, Finset.insert_erase hC]
    intro D hD hDC
    rw [if_neg]
    intro haD
    exact Finset.disjoint_left.1 (hP'.pairwise_disjoint D hD C hC hDC) haD haC
  rw [Finset.sum_congr rfl e1]
  rw [sum_partition_pointed (insert a U) (fun Q C => if a ∈ C then F (insert C Q) else 0)]
  rw [Finset.sum_erase _ (by simp), Finset.sum_powerset_insert ha]
  have z : ∑ t ∈ U.powerset, ∑ Q ∈ partsFamily (insert a U \ t), (if a ∈ t then F (insert t Q) else 0) = 0 := by
    refine Finset.sum_eq_zero fun W hW => Finset.sum_eq_zero fun Q _ => if_neg ?_
    exact fun h => ha (Finset.mem_powerset.1 hW h)
  rw [z, zero_add]
  refine Finset.sum_congr rfl fun W hW => ?_
  have hs : insert a U \ insert a W = U \ W := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (Or.inl h1) h2
      · exact ⟨h1, fun h => h2 (Or.inr h)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, fun h => h.elim (fun e => ha (e ▸ h1)) h2⟩
  rw [hs]
  exact Finset.sum_congr rfl fun Q _ => if_pos (Finset.mem_insert_self a W)
end Partitions
section Moments
variable {α : Type} [DecidableEq α]
private def cumulantOfMoments (m : Finset α → ℝ) (S : Finset α) : ℝ :=
  ∑ P ∈ partsFamily S, cumulantWeight P.card * ∏ J ∈ P, m J
private theorem cumulantWeight_succ_add {c : ℕ} (hc : 1 ≤ c) : cumulantWeight (c + 1) + (c : ℝ) * cumulantWeight c = 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  simp only [cumulantWeight, Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  ring
private theorem sum_powerset_powerset (X : Finset α) (H : Finset α → Finset α → ℝ) :
    ∑ A ∈ X.powerset, ∑ W ∈ A.powerset, H A W =
      ∑ W ∈ X.powerset, ∑ B ∈ (X \ W).powerset, H (W ∪ B) W := by
  have e1 := Finset.sum_sigma' X.powerset (fun A => A.powerset) (fun A W => H A W)
  have e2 := Finset.sum_sigma' X.powerset (fun W => (X \ W).powerset) (fun W B => H (W ∪ B) W)
  rw [e1, e2]
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1 \ x.2⟩) (fun y => ⟨y.1 ∪ y.2, y.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨A, W⟩ h
    simp only [Finset.mem_sigma, Finset.mem_powerset] at h
    simp only [Finset.mem_sigma, Finset.mem_powerset]
    exact ⟨h.2.trans h.1, Finset.sdiff_subset_sdiff h.1 le_rfl⟩
  · rintro ⟨W, B⟩ h
    simp only [Finset.mem_sigma, Finset.mem_powerset] at h
    simp only [Finset.mem_sigma, Finset.mem_powerset]
    exact ⟨Finset.union_subset h.1 (h.2.trans Finset.sdiff_subset), Finset.subset_union_left⟩
  · rintro ⟨A, W⟩ h
    simp only [Finset.mem_sigma, Finset.mem_powerset] at h
    simp [Finset.union_sdiff_of_subset h.2]
  · rintro ⟨W, B⟩ h
    simp only [Finset.mem_sigma, Finset.mem_powerset] at h
    have hd : Disjoint W B := Finset.disjoint_of_subset_right h.2 Finset.disjoint_sdiff
    simp [Finset.union_sdiff_cancel_left hd]
  · rintro ⟨A, W⟩ h
    simp only [Finset.mem_sigma, Finset.mem_powerset] at h
    simp [Finset.union_sdiff_of_subset h.2]
private theorem union_sdiff_cancel_of_subset_sdiff {X W B : Finset α} (h : B ⊆ X \ W) : (W ∪ B) \ W = B :=
  Finset.union_sdiff_cancel_left (Finset.disjoint_of_subset_right h Finset.disjoint_sdiff)
private theorem sdiff_union_eq_sdiff_sdiff (X W B : Finset α) : X \ (W ∪ B) = (X \ W) \ B := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto
private theorem sum_marked_tail_eq_zero (m : Finset α → ℝ) (h0 : m ∅ = 1) {V : Finset α} (hV : V.Nonempty) :
    ∑ B ∈ V.powerset, (∑ Q ∈ partsFamily B, cumulantWeight (Q.card + 1) * ∏ J ∈ Q, m J) * m (V \ B) = 0 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset_self V)]
  have e1 : ∑ B ∈ V.powerset.erase V,
        (∑ Q ∈ partsFamily B, cumulantWeight (Q.card + 1) * ∏ J ∈ Q, m J) * m (V \ B) =
      ∑ C ∈ V.powerset.erase ∅, ∑ Q ∈ partsFamily (V \ C),
        (fun (Q : Finset (Finset α)) (C : Finset α) => cumulantWeight (Q.card + 1) * (∏ J ∈ Q, m J) * m C) Q C := by
    refine Finset.sum_nbij' (fun B => V \ B) (fun C => V \ C) ?_ ?_ ?_ ?_ ?_
    · intro B hB
      simp only [Finset.mem_erase, Finset.mem_powerset] at hB
      simp only [Finset.mem_erase, Finset.mem_powerset]
      refine ⟨?_, Finset.sdiff_subset⟩
      intro h
      exact hB.1 (Finset.Subset.antisymm hB.2 (Finset.sdiff_eq_empty_iff_subset.1 h))
    · intro C hC
      simp only [Finset.mem_erase, Finset.mem_powerset] at hC
      simp only [Finset.mem_erase, Finset.mem_powerset]
      refine ⟨?_, Finset.sdiff_subset⟩
      intro h
      have : V \ (V \ C) = C := Finset.sdiff_sdiff_eq_self hC.2
      rw [h, Finset.sdiff_self] at this
      exact hC.1 this.symm
    · intro B hB
      simp only [Finset.mem_erase, Finset.mem_powerset] at hB
      exact Finset.sdiff_sdiff_eq_self hB.2
    · intro C hC
      simp only [Finset.mem_erase, Finset.mem_powerset] at hC
      exact Finset.sdiff_sdiff_eq_self hC.2
    · intro B hB
      simp only [Finset.mem_erase, Finset.mem_powerset] at hB
      rw [Finset.sdiff_sdiff_eq_self hB.2, Finset.sum_mul]
  rw [e1, ← sum_partition_pointed V, Finset.sdiff_self, h0, mul_one, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun R hR => ?_
  have hR' := mem_partsFamily.1 hR
  have e2 : ∑ C ∈ R, cumulantWeight ((R.erase C).card + 1) * (∏ J ∈ R.erase C, m J) * m C =
      (R.card : ℝ) * (cumulantWeight R.card * ∏ J ∈ R, m J) := by
    have : ∀ C ∈ R, cumulantWeight ((R.erase C).card + 1) * (∏ J ∈ R.erase C, m J) * m C =
        cumulantWeight R.card * ∏ J ∈ R, m J := by
      intro C hC
      rw [Finset.card_erase_add_one hC, mul_assoc, Finset.prod_erase_mul _ _ hC]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  rw [e2]
  have hc : 1 ≤ R.card := by
    obtain ⟨x, hx⟩ := hV
    obtain ⟨B, hB, -⟩ := hR'.mem_iff.1 hx
    exact Finset.card_pos.2 ⟨B, hB⟩
  have := cumulantWeight_succ_add hc
  calc cumulantWeight (R.card + 1) * ∏ J ∈ R, m J + (R.card : ℝ) * (cumulantWeight R.card * ∏ J ∈ R, m J)
      = (cumulantWeight (R.card + 1) + (R.card : ℝ) * cumulantWeight R.card) * ∏ J ∈ R, m J := by ring
    _ = 0 := by rw [this, zero_mul]
private theorem moment_eq_sum_cumulant_mul (m : Finset α → ℝ) (h0 : m ∅ = 1) {z : α} {X : Finset α} (hz : z ∉ X) :
    m (insert z X) = ∑ A ∈ X.powerset, cumulantOfMoments m (insert z A) * m (X \ A) := by
  have e1 : ∀ A ∈ X.powerset, cumulantOfMoments m (insert z A) * m (X \ A) =
      ∑ W ∈ A.powerset, (fun (A W : Finset α) => m (insert z W) *
        (∑ Q ∈ partsFamily (A \ W), cumulantWeight (Q.card + 1) * ∏ J ∈ Q, m J) * m (X \ A)) A W := by
    intro A hA
    have hzA : z ∉ A := fun h => hz (Finset.mem_powerset.1 hA h)
    rw [cumulantOfMoments, sum_partition_insert hzA, Finset.sum_mul]
    refine Finset.sum_congr rfl fun W hW => ?_
    have e0 : ∑ Q ∈ partsFamily (A \ W), cumulantWeight (insert (insert z W) Q).card * ∏ J ∈ insert (insert z W) Q, m J =
        m (insert z W) * ∑ Q ∈ partsFamily (A \ W), cumulantWeight (Q.card + 1) * ∏ J ∈ Q, m J := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun Q hQ => ?_
      have hn : insert z W ∉ Q := by
        intro h
        have := (mem_partsFamily.1 hQ).subset h (Finset.mem_insert_self z W)
        exact hzA (Finset.mem_sdiff.1 this).1
      rw [Finset.card_insert_of_notMem hn, Finset.prod_insert hn]
      ring
    rw [e0]
  rw [Finset.sum_congr rfl e1, sum_powerset_powerset X]
  have e2 : ∀ W ∈ X.powerset, ∑ B ∈ (X \ W).powerset,
      m (insert z W) * (∑ Q ∈ partsFamily ((W ∪ B) \ W), cumulantWeight (Q.card + 1) * ∏ J ∈ Q, m J) * m (X \ (W ∪ B)) =
      m (insert z W) * ∑ B ∈ (X \ W).powerset,
        (∑ Q ∈ partsFamily B, cumulantWeight (Q.card + 1) * ∏ J ∈ Q, m J) * m ((X \ W) \ B) := by
    intro W _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun B hB => ?_
    rw [union_sdiff_cancel_of_subset_sdiff (Finset.mem_powerset.1 hB), sdiff_union_eq_sdiff_sdiff, mul_assoc]
  rw [Finset.sum_congr rfl e2, Finset.sum_eq_single_of_mem X (Finset.mem_powerset_self X)]
  · rw [Finset.sdiff_self]
    simp [partsFamily_empty, cumulantWeight, h0]
  · intro W hW hne
    have : (X \ W).Nonempty := by
      rw [Finset.sdiff_nonempty]
      exact fun h => hne (Finset.Subset.antisymm (Finset.mem_powerset.1 hW) h)
    rw [sum_marked_tail_eq_zero m h0 this, mul_zero]
end Moments
section Core
variable {β : Type} [DecidableEq β]
private theorem moment_insert_none_image_some (m : Finset (Option (Finset β)) → ℝ) (h0 : m ∅ = 1) (P : Finset (Finset β)) :
    m (insert none (P.image some)) =
      ∑ A ∈ P.powerset, cumulantOfMoments m (insert none (A.image some)) * m ((P \ A).image some) := by
  rw [moment_eq_sum_cumulant_mul m h0 (by simp)]
  symm
  refine Finset.sum_nbij (fun A => A.image some) ?_ ?_ ?_ ?_
  · intro A hA
    exact Finset.mem_powerset.2 (Finset.image_subset_image (Finset.mem_powerset.1 hA))
  · intro A _ A' _ h
    exact Finset.image_injective (Option.some_injective _) h
  · intro A' hA'
    obtain ⟨A, hA, rfl⟩ := Finset.subset_image_iff.1 (Finset.mem_powerset.1 hA')
    exact ⟨A, Finset.mem_coe.2 (Finset.mem_powerset.2 hA), rfl⟩
  · intro A _
    rw [Finset.image_sdiff _ _ (Option.some_injective _)]
private theorem sum_partition_moments (m : Finset (Option (Finset β)) → ℝ) (R : Finset (Finset β) → ℝ) (h0 : m ∅ = 1)
    (hR : ∀ P, m (P.image some) = R P) (U : Finset β) :
    ∑ P ∈ partsFamily U, m (insert none (P.image some)) =
      ∑ W ∈ U.powerset, (∑ A ∈ partsFamily W, cumulantOfMoments m (insert none (A.image some))) *
        ∑ Q ∈ partsFamily (U \ W), R Q := by
  have e : ∀ P ∈ partsFamily U, m (insert none (P.image some)) =
      ∑ A ∈ P.powerset, (fun A Q => cumulantOfMoments m (insert none (A.image some)) * R Q) A (P \ A) := by
    intro P _
    rw [moment_insert_none_image_some m h0]
    exact Finset.sum_congr rfl fun A _ => by rw [hR]
  rw [Finset.sum_congr rfl e, sum_partition_split U (fun A Q => cumulantOfMoments m (insert none (A.image some)) * R Q)]
  exact Finset.sum_congr rfl fun W _ => (Finset.sum_mul_sum _ _ _ _).symm
private theorem eq_of_convolution_eq (r c d n : Finset β → ℝ) (hd : d ∅ = 1)
    (h1 : ∀ S, n S = ∑ T ∈ S.powerset, r T * d (S \ T))
    (h2 : ∀ S, n S = ∑ T ∈ S.powerset, c T * d (S \ T)) (S : Finset β) : r S = c S := by
  induction S using Finset.strongInduction with
  | H S ih =>
    have e := (h1 S).symm.trans (h2 S)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset_self S),
      ← Finset.add_sum_erase _ (fun T => c T * d (S \ T)) (Finset.mem_powerset_self S)] at e
    have e2 : ∑ T ∈ S.powerset.erase S, r T * d (S \ T) = ∑ T ∈ S.powerset.erase S, c T * d (S \ T) := by
      refine Finset.sum_congr rfl fun T hT => ?_
      simp only [Finset.mem_erase, Finset.mem_powerset] at hT
      rw [ih T (Finset.ssubset_iff_subset_ne.2 ⟨hT.2, hT.1⟩)]
    rw [e2, Finset.sdiff_self, hd, mul_one, mul_one] at e
    exact add_right_cancel e
private theorem eq_sum_cumulants_of_product_rule (μ : Finset β → Finset (Option (Finset β)) → ℝ)
    (R : Finset (Finset β) → ℝ)
    (h0 : ∀ I, μ I ∅ = 1) (hR : ∀ I P, μ I (P.image some) = R P) (r n : Finset β → ℝ)
    (hn : ∀ S, n S = ∑ I ∈ S.powerset, ∑ P ∈ partsFamily (S \ I), μ I (insert none (P.image some)))
    (hr : ∀ S, n S = ∑ T ∈ S.powerset, r T * ∑ P ∈ partsFamily (S \ T), R P) (S : Finset β) :
    r S = ∑ I ∈ S.powerset, ∑ P ∈ partsFamily (S \ I), cumulantOfMoments (μ I) (insert none (P.image some)) := by
  let C : Finset β → Finset β → ℝ := fun I W => ∑ A ∈ partsFamily W, cumulantOfMoments (μ I) (insert none (A.image some))
  let d : Finset β → ℝ := fun U => ∑ P ∈ partsFamily U, R P
  refine eq_of_convolution_eq r (fun T => ∑ I ∈ T.powerset, C I (T \ I)) d n ?_ hr ?_ S
  · simp only [d, partsFamily_empty, Finset.sum_singleton]
    rw [← hR ∅ ∅, Finset.image_empty, h0]
  · intro S
    rw [hn S]
    have e1 : ∑ T ∈ S.powerset, (∑ I ∈ T.powerset, C I (T \ I)) * d (S \ T) =
        ∑ T ∈ S.powerset, ∑ I ∈ T.powerset, (fun T I => C I (T \ I) * d (S \ T)) T I :=
      Finset.sum_congr rfl fun T _ => Finset.sum_mul _ _ _
    rw [e1, sum_powerset_powerset S]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [sum_partition_moments (μ I) R (h0 I) (hR I) (S \ I)]
    refine Finset.sum_congr rfl fun B hB => ?_
    simp only [C, d]
    rw [union_sdiff_cancel_of_subset_sdiff (Finset.mem_powerset.1 hB), sdiff_union_eq_sdiff_sdiff]
end Core
section Calculus
variable {n : ℕ}
private def mixedPartial (f : (Fin n → ℝ) → ℝ) (I : Finset (Fin n)) (τ : Fin n → ℝ) : ℝ :=
  iteratedFDeriv ℝ I.card f τ fun j => Pi.single (I.orderEmbOfFin rfl j) 1
private def partialAlong (f : (Fin n → ℝ) → ℝ) (a : Fin n) : (Fin n → ℝ) → ℝ := fun τ => fderiv ℝ f τ (Pi.single a 1)
private theorem mixedPartial_of_card (f : (Fin n → ℝ) → ℝ) (I : Finset (Fin n)) (τ : Fin n → ℝ) {k : ℕ} (h : I.card = k) :
    mixedPartial f I τ = iteratedFDeriv ℝ k f τ fun j => Pi.single (I.orderEmbOfFin h j) 1 := by
  subst h
  rfl
private theorem mixedPartial_empty (f : (Fin n → ℝ) → ℝ) (τ : Fin n → ℝ) : mixedPartial f ∅ τ = f τ :=
  iteratedFDeriv_zero_apply _
private theorem snoc_orderEmbOfFin_insert {a : Fin n} {U : Finset (Fin n)} (ha : ∀ b ∈ U, b < a) {c : ℕ} (h : U.card = c)
    (h' : (insert a U).card = c + 1) :
    Fin.snoc (α := fun _ => Fin n) (⇑(U.orderEmbOfFin h)) a = ⇑((insert a U).orderEmbOfFin h') := by
  refine Finset.orderEmbOfFin_unique h' ?_ ?_
  · intro x
    induction x using Fin.lastCases with
    | last => simp
    | cast i =>
      simp only [Fin.snoc_castSucc]
      exact Finset.mem_insert_of_mem (Finset.orderEmbOfFin_mem U h i)
  · intro i j hij
    induction j using Fin.lastCases with
    | last =>
      induction i using Fin.lastCases with
      | last => exact absurd hij (lt_irrefl _)
      | cast i =>
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact ha _ (Finset.orderEmbOfFin_mem U h i)
    | cast j =>
      induction i using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last _))
      | cast i =>
        simp only [Fin.snoc_castSucc]
        exact (U.orderEmbOfFin h).strictMono (Fin.castSucc_lt_castSucc_iff.1 hij)
private theorem mixedPartial_insert {f : (Fin n → ℝ) → ℝ} {a : Fin n} {U : Finset (Fin n)} (ha : ∀ b ∈ U, b < a)
    {τ : Fin n → ℝ} (hf : ContDiffAt ℝ ((U.card + 1 : ℕ) : WithTop ℕ∞) f τ) :
    mixedPartial f (insert a U) τ = mixedPartial (partialAlong f a) U τ := by
  have hc : (insert a U).card = U.card + 1 :=
    Finset.card_insert_of_notMem fun h => lt_irrefl a (ha a h)
  rw [mixedPartial_of_card f _ τ hc, iteratedFDeriv_succ_apply_right, ← snoc_orderEmbOfFin_insert ha rfl hc]
  have hat : ContDiffAt ℝ (U.card : WithTop ℕ∞) (fderiv ℝ f) τ :=
    hf.fderiv_right (by push_cast; exact le_rfl)
  let ev : ((Fin n → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (Pi.single a 1)
  have e := ev.iteratedFDeriv_comp_left hat (i := U.card) le_rfl
  have e' : iteratedFDeriv ℝ U.card (partialAlong f a) τ =
      ev.compContinuousMultilinearMap (iteratedFDeriv ℝ U.card (fderiv ℝ f) τ) := e
  rw [mixedPartial, e']
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, ev,
    ContinuousLinearMap.apply_apply, Fin.snoc_last]
  refine congrArg (fun v => iteratedFDeriv ℝ U.card (fderiv ℝ f) τ v (Pi.single a 1)) ?_
  funext j
  simp [Fin.init, Fin.snoc_castSucc]
private theorem mixedPartial_congr {f g : (Fin n → ℝ) → ℝ} {τ : Fin n → ℝ} (h : f =ᶠ[𝓝 τ] g) (U : Finset (Fin n)) :
    mixedPartial f U τ = mixedPartial g U τ := by
  rw [mixedPartial, (h.iteratedFDeriv ℝ U.card).eq_of_nhds]
  rfl
private theorem contDiffAt_partialAlong {f : (Fin n → ℝ) → ℝ} {a : Fin n} {τ : Fin n → ℝ} {k : ℕ}
    (hf : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f τ) : ContDiffAt ℝ (k : WithTop ℕ∞) (partialAlong f a) τ :=
  (hf.fderiv_right (by push_cast; exact le_rfl)).clm_apply contDiffAt_const
private theorem mixedPartial_add {f g : (Fin n → ℝ) → ℝ} {U : Finset (Fin n)} {τ : Fin n → ℝ}
    (hf : ContDiffAt ℝ (U.card : WithTop ℕ∞) f τ) (hg : ContDiffAt ℝ (U.card : WithTop ℕ∞) g τ) :
    mixedPartial (fun x => f x + g x) U τ = mixedPartial f U τ + mixedPartial g U τ := by
  have := iteratedFDeriv_add_apply (i := U.card) hf hg
  have e : (fun x => f x + g x) = f + g := rfl
  rw [mixedPartial, e, this]
  rfl
private theorem eventually_differentiableAt {f : (Fin n → ℝ) → ℝ} {τ : Fin n → ℝ} {k : ℕ}
    (hf : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f τ) : ∀ᶠ x in 𝓝 τ, DifferentiableAt ℝ f x := by
  have h1 : ContDiffAt ℝ (1 : WithTop ℕ∞) f τ := hf.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
  filter_upwards [h1.eventually (by simp)] with x hx
  exact hx.differentiableAt (by simp)
private theorem mixedPartial_mul (U : Finset (Fin n)) : ∀ (f g : (Fin n → ℝ) → ℝ) (τ : Fin n → ℝ),
    ContDiffAt ℝ (U.card : WithTop ℕ∞) f τ → ContDiffAt ℝ (U.card : WithTop ℕ∞) g τ →
    mixedPartial (fun x => f x * g x) U τ = ∑ T ∈ U.powerset, mixedPartial f T τ * mixedPartial g (U \ T) τ := by
  induction U using Finset.induction_on_max with
  | empty =>
    intro f g τ _ _
    simp [mixedPartial_empty]
  | insert a U ha ih =>
    intro f g τ hf hg
    have haU : a ∉ U := fun h => lt_irrefl a (ha a h)
    have hc : (insert a U).card = U.card + 1 := Finset.card_insert_of_notMem haU
    rw [hc] at hf hg
    have hf0 : ContDiffAt ℝ (U.card : WithTop ℕ∞) f τ := hf.of_le (by exact_mod_cast Nat.le_succ _)
    have hg0 : ContDiffAt ℝ (U.card : WithTop ℕ∞) g τ := hg.of_le (by exact_mod_cast Nat.le_succ _)
    have hfa := contDiffAt_partialAlong (a := a) hf
    have hga := contDiffAt_partialAlong (a := a) hg
    rw [mixedPartial_insert ha (hf.mul hg)]
    have hev : partialAlong (fun x => f x * g x) a =ᶠ[𝓝 τ]
        fun x => partialAlong f a x * g x + f x * partialAlong g a x := by
      filter_upwards [eventually_differentiableAt hf, eventually_differentiableAt hg] with x h1 h2
      simp only [partialAlong]
      rw [fderiv_fun_mul h1 h2]
      simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
      ring
    rw [mixedPartial_congr hev, mixedPartial_add (hfa.mul hg0) (hf0.mul hga), ih _ _ _ hfa hg0, ih _ _ _ hf0 hga,
      Finset.sum_powerset_insert haU]
    have hsub : ∀ T ∈ U.powerset, ∀ b ∈ T, b < a := fun T hT b hb => ha b (Finset.mem_powerset.1 hT hb)
    have hT : ∀ T ∈ U.powerset, T.card + 1 ≤ U.card + 1 := fun T hT =>
      Nat.succ_le_succ (Finset.card_le_card (Finset.mem_powerset.1 hT))
    have hT' : ∀ T ∈ U.powerset, (U \ T).card + 1 ≤ U.card + 1 := fun T _ =>
      Nat.succ_le_succ (Finset.card_le_card Finset.sdiff_subset)
    rw [add_comm]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun T hTm => ?_
      have hn : a ∉ T := fun h => haU (Finset.mem_powerset.1 hTm h)
      rw [Finset.insert_sdiff_of_notMem _ hn, mixedPartial_insert (fun b hb => ha b (Finset.mem_sdiff.1 hb).1)
        (hg.of_le (by exact_mod_cast hT' T hTm))]
    · refine Finset.sum_congr rfl fun T hTm => ?_
      rw [mixedPartial_insert (hsub T hTm) (hf.of_le (by exact_mod_cast hT T hTm))]
      congr 2
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨Or.inr h1, fun h => h.elim (fun e => haU (e ▸ h1)) h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd (Or.inl h1) h2
        · exact ⟨h1, fun h => h2 (Or.inr h)⟩
private theorem mixedPartial_eq_mul_sum_log {f : (Fin n → ℝ) → ℝ} {τ : Fin n → ℝ} {N : ℕ}
    (hf : ContDiffAt ℝ (N : WithTop ℕ∞) f τ)
    (hpos : 0 < f τ) (U : Finset (Fin n)) : U.card ≤ N →
    mixedPartial f U τ = f τ * ∑ P ∈ partsFamily U, ∏ J ∈ P, mixedPartial (fun x => Real.log (f x)) J τ := by
  induction U using Finset.strongInduction with
  | H U ih =>
    intro hU
    rcases U.eq_empty_or_nonempty with rfl | hne
    · simp [partsFamily_empty, mixedPartial_empty]
    set a := U.max' hne with ha_def
    have haU : a ∈ U := Finset.max'_mem U hne
    set V := U.erase a with hV
    have hUV : U = insert a V := (Finset.insert_erase haU).symm
    have haV : a ∉ V := Finset.notMem_erase a U
    have hlt : ∀ b ∈ V, b < a := fun b hb =>
      lt_of_le_of_ne (Finset.le_max' U b (Finset.mem_of_mem_erase hb)) (Finset.ne_of_mem_erase hb)
    have hcV : V.card + 1 = U.card := by
      rw [hV]
      exact Finset.card_erase_add_one haU
    have hfV : ContDiffAt ℝ ((V.card + 1 : ℕ) : WithTop ℕ∞) f τ :=
      hf.of_le (by exact_mod_cast hcV.le.trans hU)
    have hl : ContDiffAt ℝ ((V.card + 1 : ℕ) : WithTop ℕ∞) (fun x => Real.log (f x)) τ :=
      hfV.log hpos.ne'
    have hla := contDiffAt_partialAlong (a := a) hl
    have hfV0 : ContDiffAt ℝ (V.card : WithTop ℕ∞) f τ := hfV.of_le (by exact_mod_cast Nat.le_succ _)
    have hev : partialAlong f a =ᶠ[𝓝 τ] fun x => partialAlong (fun y => Real.log (f y)) a x * f x := by
      filter_upwards [eventually_differentiableAt hfV, hfV.continuousAt.eventually (lt_mem_nhds hpos)] with x h1 h2
      simp only [partialAlong]
      rw [fderiv.log h1 h2.ne']
      simp only [_root_.smul_apply, smul_eq_mul]
      field_simp
    rw [hUV, mixedPartial_insert hlt hfV, mixedPartial_congr hev, mixedPartial_mul V _ _ _ hla hfV0,
      sum_partition_insert haV]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTV := Finset.mem_powerset.1 hT
    have hss : V \ T ⊂ U := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.sdiff_subset.trans (Finset.erase_subset _ _), ?_⟩
      intro h
      exact (Finset.mem_sdiff.1 (h ▸ haU : a ∈ V \ T)).1 |> haV
    rw [ih _ hss ((Finset.card_le_card hss.1).trans hU)]
    have hb : ∀ b ∈ T, b < a := fun b hb => hlt b (hTV hb)
    rw [← mixedPartial_insert hb (hl.of_le (by exact_mod_cast Nat.succ_le_succ (Finset.card_le_card hTV)))]
    have e : ∑ Q ∈ partsFamily (V \ T), ∏ J ∈ insert (insert a T) Q, mixedPartial (fun x => Real.log (f x)) J τ =
        mixedPartial (fun x => Real.log (f x)) (insert a T) τ *
          ∑ Q ∈ partsFamily (V \ T), ∏ J ∈ Q, mixedPartial (fun x => Real.log (f x)) J τ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun Q hQ => ?_
      have hn : insert a T ∉ Q := by
        intro h
        exact haV (Finset.mem_sdiff.1 ((mem_partsFamily.1 hQ).subset h (Finset.mem_insert_self a T))).1
      rw [Finset.prod_insert hn]
    rw [e]
    ring
end Calculus
section Families
variable {Ω : Type} [MeasurableSpace Ω] {n : ℕ} {μ : Measure Ω} {B : Set (Fin n → ℝ)}
private theorem aestronglyMeasurable_fderiv_apply (hB : IsOpen B) (G : (Fin n → ℝ) → Ω → ℝ)
    (hm : ∀ τ ∈ B, AEStronglyMeasurable (G τ) μ)
    {τ : Fin n → ℝ} (hτ : τ ∈ B) (e : Fin n → ℝ) (hd : ∀ᵐ ω ∂μ, DifferentiableAt ℝ (fun τ' => G τ' ω) τ) :
    AEStronglyMeasurable (fun ω => fderiv ℝ (fun τ' => G τ' ω) τ e) μ := by
  have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hev : ∀ᶠ k : ℕ in atTop, τ + ((1 : ℝ) / ((k : ℝ) + 1)) • e ∈ B := by
    have h1 : Tendsto (fun k : ℕ => τ + ((1 : ℝ) / ((k : ℝ) + 1)) • e) atTop (𝓝 τ) := by
      have := (h0.smul_const e).const_add τ
      simpa using this
    exact h1.eventually (hB.mem_nhds hτ)
  obtain ⟨M, hM⟩ := eventually_atTop.1 hev
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun (k : ℕ) ω => (((1 : ℝ) / (((k + M : ℕ) : ℝ) + 1))⁻¹) •
      (G (τ + ((1 : ℝ) / (((k + M : ℕ) : ℝ) + 1)) • e) ω - G τ ω)) ?_ ?_
  · intro k
    exact ((hm _ (hM (k + M) (by omega))).sub (hm τ hτ)).const_smul (((1 : ℝ) / (((k + M : ℕ) : ℝ) + 1))⁻¹)
  · filter_upwards [hd] with ω hω
    have hl : HasDerivAt (fun t : ℝ => τ + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add τ
    have hf : HasFDerivAt (fun τ' => G τ' ω) (fderiv ℝ (fun τ' => G τ' ω) τ) (τ + (0 : ℝ) • e) := by
      simpa using hω.hasFDerivAt
    have h1 : HasDerivAt ((fun τ' => G τ' ω) ∘ fun t : ℝ => τ + t • e)
        (fderiv ℝ (fun τ' => G τ' ω) τ e) 0 := hf.comp_hasDerivAt (0 : ℝ) hl
    have h2 := h1.tendsto_slope_zero
    have h3 : Tendsto (fun k : ℕ => (1 : ℝ) / (((k + M : ℕ) : ℝ) + 1)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact h0.comp (tendsto_add_atTop_nat M)
      · refine Eventually.of_forall fun k => ?_
        have : (0 : ℝ) < ((k + M : ℕ) : ℝ) + 1 := by positivity
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact (one_div_pos.2 this).ne'
    have h4 := h2.comp h3
    simpa [Function.comp_def] using h4
private theorem aestronglyMeasurable_mixedPartial (hB : IsOpen B) (U : Finset (Fin n)) :
    ∀ (k : ℕ) (G : (Fin n → ℝ) → Ω → ℝ), U.card ≤ k →
    (∀ τ ∈ B, AEStronglyMeasurable (G τ) μ) →
    (∀ᵐ ω ∂μ, ContDiffOn ℝ (k : WithTop ℕ∞) (fun τ => G τ ω) B) →
    ∀ τ ∈ B, AEStronglyMeasurable (fun ω => mixedPartial (fun τ' => G τ' ω) U τ) μ := by
  induction U using Finset.induction_on_max with
  | empty =>
    intro k G _ hm _ τ hτ
    simpa [mixedPartial_empty] using hm τ hτ
  | insert a U ha ih =>
    intro k G hk hm hs τ hτ
    have haU : a ∉ U := fun h => lt_irrefl a (ha a h)
    have hc : (insert a U).card = U.card + 1 := Finset.card_insert_of_notMem haU
    obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
    have hUl : U.card ≤ l := by omega
    have hat : ∀ᵐ ω ∂μ, ∀ x ∈ B, ContDiffAt ℝ ((l + 1 : ℕ) : WithTop ℕ∞) (fun τ => G τ ω) x := by
      filter_upwards [hs] with ω hω x hx
      exact hω.contDiffAt (hB.mem_nhds hx)
    have hG' := ih l (fun τ ω => partialAlong (fun τ' => G τ' ω) a τ) hUl
      (fun x hx => aestronglyMeasurable_fderiv_apply hB G hm hx _ (by
        filter_upwards [hat] with ω hω
        exact (hω x hx).differentiableAt (by simp)))
      (by
        filter_upwards [hat] with ω hω x hx
        exact (contDiffAt_partialAlong (hω x hx)).contDiffWithinAt) τ hτ
    refine hG'.congr ?_
    filter_upwards [hat] with ω hω
    exact (mixedPartial_insert ha ((hω τ hτ).of_le (by exact_mod_cast (by omega : U.card + 1 ≤ l + 1)))).symm
private theorem norm_mixedPartial_le {f : (Fin n → ℝ) → ℝ} {U : Finset (Fin n)} {τ : Fin n → ℝ} {K : ℝ}
    (h : ‖iteratedFDeriv ℝ U.card f τ‖ ≤ K) : ‖mixedPartial f U τ‖ ≤ K := by
  have h1 := (iteratedFDeriv ℝ U.card f τ).le_opNorm (fun j => Pi.single (U.orderEmbOfFin rfl j) (1 : ℝ))
  simp only [Pi.norm_single, norm_one, Finset.prod_const_one, mul_one] at h1
  exact h1.trans h
private theorem isDominatedSmoothFamily_mul (hB : IsOpen B) {G₁ G₂ : (Fin n → ℝ) → Ω → ℝ} {K₁ K₂ : ℝ}
    (hK₁ : IsDominatedSmoothFamily μ n B K₁ G₁) (hK₂ : IsDominatedSmoothFamily μ n B K₂ G₂) :
    ∃ K, IsDominatedSmoothFamily μ n B K (fun τ ω => G₁ τ ω * G₂ τ ω) := by
  refine ⟨∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * |K₁| * |K₂|,
    fun τ hτ => (hK₁.aestronglyMeasurable τ hτ).mul (hK₂.aestronglyMeasurable τ hτ), ?_, ?_⟩
  · filter_upwards [hK₁.contDiffOn, hK₂.contDiffOn] with ω a b
    exact a.mul b
  · filter_upwards [hK₁.contDiffOn, hK₂.contDiffOn, hK₁.norm_iteratedFDeriv_le, hK₂.norm_iteratedFDeriv_le]
      with ω a b c d j hj τ hτ
    have hle := norm_iteratedFDerivWithin_mul_le (n := j) a b hB.uniqueDiffOn hτ (by exact_mod_cast hj)
    rw [iteratedFDerivWithin_of_isOpen j hB hτ] at hle
    refine hle.trans ?_
    have hterm : ∀ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (fun τ => G₁ τ ω) B τ‖ *
          ‖iteratedFDerivWithin ℝ (j - i) (fun τ => G₂ τ ω) B τ‖ ≤ (j.choose i : ℝ) * |K₁| * |K₂| := by
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [iteratedFDerivWithin_of_isOpen i hB hτ, iteratedFDerivWithin_of_isOpen (j - i) hB hτ]
      have b1 := (c i (hij.trans hj) τ hτ).trans (le_abs_self K₁)
      have b2 := (d (j - i) ((Nat.sub_le _ _).trans hj) τ hτ).trans (le_abs_self K₂)
      have hc : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
      exact mul_le_mul (mul_le_mul_of_nonneg_left b1 hc) b2 (norm_nonneg _) (mul_nonneg hc (abs_nonneg _))
    refine (Finset.sum_le_sum hterm).trans ?_
    exact Finset.single_le_sum (f := fun j => ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * |K₁| * |K₂|)
      (fun j _ => Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) (abs_nonneg _))
      (Finset.mem_range.2 (by omega))
private theorem iteratedFDeriv_single_eq_mixedPartial_univ (f : (Fin n → ℝ) → ℝ) (τ : Fin n → ℝ) :
    iteratedFDeriv ℝ n f τ (fun i => Pi.single i 1) = mixedPartial f Finset.univ τ := by
  rw [mixedPartial_of_card f Finset.univ τ (Finset.card_fin n)]
  have e : ⇑((Finset.univ : Finset (Fin n)).orderEmbOfFin (Finset.card_fin n)) = id :=
    (Finset.orderEmbOfFin_unique (Finset.card_fin n) (f := id) (by simp) strictMono_id).symm
  simp only [e, id]
omit [MeasurableSpace Ω] in
private theorem jointCumulant_eq_cumulantOfMoments {α : Type} [DecidableEq α] (m : (Ω → ℝ) → ℝ) (S : Finset α)
    (f : α → Ω → ℝ) :
    jointCumulant m S f = cumulantOfMoments (fun J => m (blockProd f J)) S :=
  sum_finpartition_eq S (fun P => cumulantWeight P.card * ∏ J ∈ P, m (blockProd f J))
end Families
theorem densityMeanCumulantExpansion_of_gibbsMeanDifferentiation (h : GibbsMeanDifferentiation) :
    DensityMeanCumulantExpansion := by
  intro Ω _ μ _ n B K K' G Z hB h0 hG hZ
  have hI := h.1 Ω μ n n B
  obtain ⟨K'', hGZ⟩ := isDominatedSmoothFamily_mul hB hG hZ.dominated
  obtain ⟨hNs, hNd⟩ := hI K'' _ hB hGZ
  obtain ⟨hDs, hDd⟩ := hI K' _ hB hZ.dominated
  let D : (Fin n → ℝ) → ℝ := fun τ => ∫ ω, Z τ ω ∂μ
  let N : (Fin n → ℝ) → ℝ := fun τ => ∫ ω, G τ ω * Z τ ω ∂μ
  let r : (Fin n → ℝ) → ℝ := fun τ => densityMean μ (Z τ) (G τ)
  have hD0 : 0 < D 0 := hZ.integral_pos
  have hNa : ContDiffAt ℝ (n : WithTop ℕ∞) N 0 := hNs.contDiffAt (hB.mem_nhds h0)
  have hDa : ContDiffAt ℝ (n : WithTop ℕ∞) D 0 := hDs.contDiffAt (hB.mem_nhds h0)
  have hra : ContDiffAt ℝ (n : WithTop ℕ∞) r 0 := hNa.div hDa hD0.ne'
  refine ⟨hra, ?_⟩
  have hcard : ∀ S : Finset (Fin n), S.card ≤ n := fun S => (Finset.card_le_univ S).trans_eq (Fintype.card_fin n)
  have hcast : ∀ S : Finset (Fin n), (S.card : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := fun S => by exact_mod_cast hcard S
  let g : Finset (Fin n) → Ω → ℝ := fun I => mixedDerivAt G I
  let L : Finset (Fin n) → Ω → ℝ := fun J => mixedDerivAt (logDensity Z) J
  have hN : ∀ S : Finset (Fin n), mixedPartial N S 0 = ∫ ω, mixedPartial (fun τ => G τ ω * Z τ ω) S 0 ∂μ :=
    fun S => hNd 0 h0 S.card (hcard S) _
  have hD : ∀ S : Finset (Fin n), mixedPartial D S 0 = ∫ ω, mixedPartial (fun τ => Z τ ω) S 0 ∂μ :=
    fun S => hDd 0 h0 S.card (hcard S) _
  have hGa : ∀ᵐ ω ∂μ, ContDiffAt ℝ (n : WithTop ℕ∞) (fun τ => G τ ω) 0 := by
    filter_upwards [hG.contDiffOn] with ω hω
    exact hω.contDiffAt (hB.mem_nhds h0)
  have hZa : ∀ᵐ ω ∂μ, ContDiffAt ℝ (n : WithTop ℕ∞) (fun τ => Z τ ω) 0 := by
    filter_upwards [hZ.dominated.contDiffOn] with ω hω
    exact hω.contDiffAt (hB.mem_nhds h0)
  have hZf : ∀ᵐ ω ∂μ, ∀ U : Finset (Fin n),
      mixedPartial (fun τ => Z τ ω) U 0 = Z 0 ω * ∑ P ∈ partsFamily U, ∏ J ∈ P, L J ω := by
    filter_upwards [hZa, hZ.nonneg, hZ.iteratedFDeriv_eq_zero] with ω hz hn hf U
    rcases (hn 0 h0).eq_or_lt with e | e
    · rw [mixedPartial, hf 0 h0 e.symm _ (hcard U), ← e]
      simp
    · exact mixedPartial_eq_mul_sum_log hz e U (hcard U)
  have hLint : ∀ (S : Finset (Fin n)), ∀ P ∈ partsFamily S, Integrable (fun ω => (∏ J ∈ P, L J ω) * Z 0 ω) μ := by
    intro S P hP
    obtain ⟨π, -, rfl⟩ := Finset.mem_image.1 hP
    exact hZ.integrable_prod S π
  have hgm : ∀ I : Finset (Fin n), AEStronglyMeasurable (g I) μ := fun I =>
    aestronglyMeasurable_mixedPartial hB I n G (hcard I) hG.aestronglyMeasurable hG.contDiffOn 0 h0
  have hgb : ∀ I : Finset (Fin n), ∀ᵐ ω ∂μ, ‖g I ω‖ ≤ K := by
    intro I
    filter_upwards [hG.norm_iteratedFDeriv_le] with ω hω
    exact norm_mixedPartial_le (hω I.card (hcard I) 0 h0)
  have hQint : ∀ (I S : Finset (Fin n)), ∀ P ∈ partsFamily S,
      Integrable (fun ω => g I ω * ((∏ J ∈ P, L J ω) * Z 0 ω)) μ := fun I S P hP =>
    (hLint S P hP).bdd_mul (hgm I) (hgb I)
  have hN2 : ∀ S : Finset (Fin n), mixedPartial N S 0 =
      ∑ I ∈ S.powerset, ∑ P ∈ partsFamily (S \ I), ∫ ω, g I ω * ((∏ J ∈ P, L J ω) * Z 0 ω) ∂μ := by
    intro S
    have e : (fun ω => mixedPartial (fun τ => G τ ω * Z τ ω) S 0) =ᵐ[μ]
        fun ω => ∑ I ∈ S.powerset, ∑ P ∈ partsFamily (S \ I), g I ω * ((∏ J ∈ P, L J ω) * Z 0 ω) := by
      filter_upwards [hGa, hZa, hZf] with ω hg hz hf
      rw [mixedPartial_mul S _ _ 0 (hg.of_le (hcast S)) (hz.of_le (hcast S))]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [hf (S \ I), Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun P _ => ?_
      have : mixedPartial (fun τ => G τ ω) I 0 = g I ω := rfl
      rw [this]
      ring
    rw [hN S, integral_congr_ae e, integral_finsetSum _ fun I _ =>
      integrable_finsetSum _ fun P hP => hQint I _ P hP]
    refine Finset.sum_congr rfl fun I _ => ?_
    exact integral_finsetSum _ fun P hP => hQint I _ P hP
  have hD2 : ∀ U : Finset (Fin n), mixedPartial D U 0 =
      ∑ P ∈ partsFamily U, ∫ ω, (∏ J ∈ P, L J ω) * Z 0 ω ∂μ := by
    intro U
    have e : (fun ω => mixedPartial (fun τ => Z τ ω) U 0) =ᵐ[μ]
        fun ω => ∑ P ∈ partsFamily U, (∏ J ∈ P, L J ω) * Z 0 ω := by
      filter_upwards [hZf] with ω hf
      rw [hf U, Finset.mul_sum]
      exact Finset.sum_congr rfl fun P _ => mul_comm _ _
    rw [hD U, integral_congr_ae e]
    exact integral_finsetSum _ fun P hP => hLint U P hP
  let m : (Ω → ℝ) → ℝ := densityMean μ (Z 0)
  let μI : Finset (Fin n) → Finset (Option (Finset (Fin n))) → ℝ :=
    fun I S => m (blockProd (cumulantEntry G Z I) S)
  let R : Finset (Finset (Fin n)) → ℝ := fun P => m (fun ω => ∏ J ∈ P, L J ω)
  have hm1 : ∀ I, μI I ∅ = 1 := by
    intro I
    have e : ∫ ω, blockProd (cumulantEntry G Z I) ∅ ω * Z 0 ω ∂μ = D 0 := by
      simp [blockProd, D]
    simp only [μI, m, densityMean]
    rw [e]
    exact div_self hD0.ne'
  have hR : ∀ I P, μI I (P.image some) = R P := by
    intro I P
    simp only [μI, R]
    congr 1
    funext ω
    simp only [blockProd]
    rw [Finset.prod_image fun a _ b _ e => Option.some_injective _ e]
    rfl
  have hq : ∀ I P, μI I (insert none (P.image some)) =
      (∫ ω, g I ω * ((∏ J ∈ P, L J ω) * Z 0 ω) ∂μ) / D 0 := by
    intro I P
    simp only [μI, m, densityMean]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [blockProd]
    rw [Finset.prod_insert (by simp), Finset.prod_image fun a _ b _ e => Option.some_injective _ e, mul_assoc]
    rfl
  have hRq : ∀ P, R P = (∫ ω, (∏ J ∈ P, L J ω) * Z 0 ω ∂μ) / D 0 := fun P => rfl
  have hev : N =ᶠ[𝓝 0] fun x => r x * D x := by
    filter_upwards [hDa.continuousAt.eventually_ne hD0.ne'] with x hx
    exact (div_mul_cancel₀ _ hx).symm
  have hfin := eq_sum_cumulants_of_product_rule μI R hm1 hR (fun T => mixedPartial r T 0)
    (fun S => mixedPartial N S 0 / D 0)
    (by
      intro S
      rw [hN2 S, Finset.sum_div]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun P _ => (hq I P).symm)
    (by
      intro S
      rw [mixedPartial_congr hev, mixedPartial_mul S _ _ 0 (hra.of_le (hcast S)) (hDa.of_le (hcast S)),
        Finset.sum_div]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [mul_div_assoc, hD2 (S \ T), Finset.sum_div]
      exact congrArg _ (Finset.sum_congr rfl fun P _ => (hRq P).symm))
    Finset.univ
  rw [iteratedFDeriv_single_eq_mixedPartial_univ]
  refine hfin.trans ?_
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← sum_finpartition_eq (Finset.univ \ I) (fun P => cumulantOfMoments (μI I) (insert none (P.image some)))]
  exact Finset.sum_congr rfl fun π _ => (jointCumulant_eq_cumulantOfMoments _ _ _).symm
end YangMills.Construction.DensityMeans
end
