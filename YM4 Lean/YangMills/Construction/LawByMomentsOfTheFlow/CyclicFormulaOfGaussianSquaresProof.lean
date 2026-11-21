import YangMills.Construction.LawByMomentsOfTheFlow.CyclicFormulaOfGaussianSquares
import YangMills.Construction.LawInAState.MomentsOfWickPolynomialsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
section
open Finset
section SetPartitions
variable {ι : Type} [DecidableEq ι]
private def IsSetPartition (S : Finset ι) (P : Finset (Finset ι)) : Prop :=
  (∀ D ∈ P, D.Nonempty) ∧ (∀ D ∈ P, ∀ E ∈ P, D ≠ E → Disjoint D E) ∧ P.biUnion id = S
open Classical in
private def setPartitions (S : Finset ι) : Finset (Finset (Finset ι)) :=
  S.powerset.powerset.filter (IsSetPartition S)
private lemma subset_of_mem_setPartition {S : Finset ι} {P : Finset (Finset ι)} (h : IsSetPartition S P)
    {D : Finset ι} (hD : D ∈ P) : D ⊆ S := by
  rw [← h.2.2]
  exact subset_biUnion_of_mem id hD
private lemma mem_setPartitions {S : Finset ι} {P : Finset (Finset ι)} :
    P ∈ setPartitions S ↔ IsSetPartition S P := by
  classical
  simp only [setPartitions, mem_filter, mem_powerset, and_iff_right_iff_imp]
  intro h D hD
  rw [mem_powerset]
  exact subset_of_mem_setPartition h hD
abbrev _root_.YangMills.DeltaSharedProofs.p500779 := @mem_setPartitions
private lemma sum_finpartition_eq_sum_setPartitions (S : Finset ι) (g : Finset (Finset ι) → ℝ) :
    ∑ π : Finpartition S, g π.parts = ∑ P ∈ setPartitions S, g P := by
  refine Finset.sum_bij (fun π _ => π.parts) ?_ ?_ ?_ ?_
  · intro π _
    rw [mem_setPartitions]
    exact ⟨fun D hD => π.nonempty_of_mem_parts hD, fun D hD E hE hne => π.disjoint hD hE hne,
      π.biUnion_parts⟩
  · intro π _ π' _ h
    exact Finpartition.ext h
  · intro P hP
    rw [mem_setPartitions] at hP
    refine ⟨⟨P, ?_, ?_, ?_⟩, mem_univ _, rfl⟩
    · rw [Finset.supIndep_iff_pairwiseDisjoint]
      intro D hD E hE hne
      exact hP.2.1 D hD E hE hne
    · rw [Finset.sup_eq_biUnion]
      exact hP.2.2
    · intro h
      have := hP.1 _ h
      simp at this
  · intros
    rfl
abbrev _root_.YangMills.DeltaSharedProofs.p502077 := @sum_finpartition_eq_sum_setPartitions
private lemma notMem_of_mem_setPartitions_sdiff {S D : Finset ι} {P : Finset (Finset ι)} (hD : D.Nonempty)
    (hP : P ∈ setPartitions (S \ D)) : D ∉ P := by
  intro h
  obtain ⟨a, ha⟩ := hD
  have := subset_of_mem_setPartition (mem_setPartitions.1 hP) h ha
  simp [ha] at this
abbrev _root_.YangMills.DeltaSharedProofs.p502284 := @notMem_of_mem_setPartitions_sdiff
private lemma sum_setPartitions_sum_block (S : Finset ι) (f : Finset (Finset ι) → Finset ι → ℝ) :
    ∑ P ∈ setPartitions S, ∑ D ∈ P, f P D =
      ∑ D ∈ S.powerset.erase ∅, ∑ P ∈ setPartitions (S \ D), f (insert D P) D := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1.erase x.2⟩) (fun y => ⟨insert y.1 y.2, y.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨P, D⟩ hx
    simp only [mem_sigma] at hx
    obtain ⟨hP, hD⟩ := hx
    have hP' := mem_setPartitions.1 hP
    simp only [mem_sigma, mem_erase, mem_powerset]
    refine ⟨⟨?_, subset_of_mem_setPartition hP' hD⟩, mem_setPartitions.2 ⟨?_, ?_, ?_⟩⟩
    · exact Finset.nonempty_iff_ne_empty.1 (hP'.1 D hD)
    · intro E hE
      exact hP'.1 E (mem_of_mem_erase hE)
    · intro E hE F hF
      exact hP'.2.1 E (mem_of_mem_erase hE) F (mem_of_mem_erase hF)
    · ext a
      simp only [mem_biUnion, mem_erase, id, mem_sdiff]
      constructor
      · rintro ⟨E, ⟨hne, hE⟩, ha⟩
        refine ⟨subset_of_mem_setPartition hP' hE ha, fun had => ?_⟩
        exact Finset.disjoint_left.1 (hP'.2.1 E hE D hD hne) ha had
      · rintro ⟨haS, had⟩
        rw [← hP'.2.2] at haS
        obtain ⟨E, hE, ha⟩ := mem_biUnion.1 haS
        refine ⟨E, ⟨?_, hE⟩, ha⟩
        rintro rfl
        exact had ha
  · rintro ⟨D, P⟩ hy
    simp only [mem_sigma, mem_erase, mem_powerset] at hy
    obtain ⟨⟨hne, hDS⟩, hP⟩ := hy
    have hne' : D.Nonempty := Finset.nonempty_iff_ne_empty.2 hne
    have hP' := mem_setPartitions.1 hP
    simp only [mem_sigma, mem_insert, true_or, and_true]
    refine mem_setPartitions.2 ⟨?_, ?_, ?_⟩
    · intro E hE
      rcases mem_insert.1 hE with rfl | hE
      · exact hne'
      · exact hP'.1 E hE
    · have hdis : ∀ E ∈ P, Disjoint D E := fun E hE =>
        Finset.disjoint_of_subset_right (subset_of_mem_setPartition hP' hE) Finset.disjoint_sdiff
      intro E hE F hF hEF
      rcases mem_insert.1 hE with hE | hE <;> rcases mem_insert.1 hF with hF | hF
      · exact absurd (hE.trans hF.symm) hEF
      · exact hE ▸ hdis F hF
      · exact hF ▸ (hdis E hE).symm
      · exact hP'.2.1 E hE F hF hEF
    · rw [Finset.biUnion_insert, hP'.2.2]
      simpa using Finset.union_sdiff_of_subset hDS
  · rintro ⟨P, D⟩ hx
    simp only [mem_sigma] at hx
    simp only [insert_erase hx.2]
  · rintro ⟨D, P⟩ hy
    simp only [mem_sigma, mem_erase, mem_powerset] at hy
    have hne' : D.Nonempty := Finset.nonempty_iff_ne_empty.2 hy.1.1
    simp only [erase_insert (notMem_of_mem_setPartitions_sdiff hne' hy.2)]
  · rintro ⟨P, D⟩ hx
    simp only [mem_sigma] at hx
    simp only [insert_erase hx.2]
abbrev _root_.YangMills.DeltaSharedProofs.p502278 := @sum_setPartitions_sum_block
private def signedFactorial (k : ℕ) : ℝ := (-1) ^ k * (k.factorial : ℝ)
variable (M : Finset ι → ℝ)
private def momentInverse (S : Finset ι) : ℝ :=
  ∑ P ∈ setPartitions S, signedFactorial P.card * ∏ D ∈ P, M D
private def partitionCumulant (S : Finset ι) : ℝ :=
  ∑ P ∈ setPartitions S, signedFactorial (P.card - 1) * ∏ D ∈ P, M D
private lemma setPartitions_empty : setPartitions (∅ : Finset ι) = {∅} := by
  ext P
  simp only [mem_setPartitions, mem_singleton]
  constructor
  · intro h
    by_contra hne
    obtain ⟨D, hD⟩ := Finset.nonempty_iff_ne_empty.2 hne
    obtain ⟨a, ha⟩ := h.1 D hD
    have := subset_of_mem_setPartition h hD ha
    simp at this
  · rintro rfl
    exact ⟨by simp, by simp, by simp⟩
private lemma momentInverse_empty : momentInverse M ∅ = 1 := by
  simp [momentInverse, setPartitions_empty, signedFactorial]
private lemma card_pos_of_mem_setPartitions {S : Finset ι} (hS : S.Nonempty) {P : Finset (Finset ι)}
    (hP : P ∈ setPartitions S) : 0 < P.card := by
  rw [Finset.card_pos]
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  subst hne
  have := (mem_setPartitions.1 hP).2.2
  simp only [biUnion_empty] at this
  subst this
  simp at hS
abbrev _root_.YangMills.DeltaSharedProofs.p502120 := @card_pos_of_mem_setPartitions
private lemma momentInverse_eq {S : Finset ι} (hS : S.Nonempty) :
    momentInverse M S = - ∑ D ∈ S.powerset.erase ∅, M D * momentInverse M (S \ D) := by
  have h1 : momentInverse M S =
      ∑ P ∈ setPartitions S, ∑ _D ∈ P, - (signedFactorial (P.card - 1) * ∏ D ∈ P, M D) := by
    refine Finset.sum_congr rfl fun P hP => ?_
    have hc := card_pos_of_mem_setPartitions hS hP
    obtain ⟨k, hk⟩ : ∃ k, P.card = k + 1 := ⟨P.card - 1, by omega⟩
    rw [Finset.sum_const, hk, nsmul_eq_mul, Nat.add_sub_cancel, signedFactorial, signedFactorial,
      Nat.factorial_succ]
    push_cast
    ring
  rw [h1, sum_setPartitions_sum_block S (fun P _ => - (signedFactorial (P.card - 1) * ∏ D ∈ P, M D)),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun D hD => ?_
  have hne : D.Nonempty := Finset.nonempty_iff_ne_empty.2 (Finset.ne_of_mem_erase hD)
  rw [momentInverse, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun P hP => ?_
  have hn := notMem_of_mem_setPartitions_sdiff hne hP
  rw [Finset.card_insert_of_notMem hn, Finset.prod_insert hn, Nat.add_sub_cancel]
  ring
abbrev _root_.YangMills.DeltaSharedProofs.p502140 := @momentInverse_eq
private lemma sum_powerset_mul_momentInverse {S : Finset ι} (hS : S.Nonempty) (h0 : M ∅ = 1) :
    ∑ D ∈ S.powerset, M D * momentInverse M (S \ D) = 0 := by
  rw [← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset S), h0, one_mul, sdiff_empty,
    momentInverse_eq M hS]
  ring
abbrev _root_.YangMills.DeltaSharedProofs.p501735 := @sum_powerset_mul_momentInverse
private lemma sum_powerset_mul_momentInverse_eq_ite (S : Finset ι) (h0 : M ∅ = 1) :
    ∑ D ∈ S.powerset, M D * momentInverse M (S \ D) = if S = ∅ then 1 else 0 := by
  split_ifs with h
  · subst h
    simp [h0, momentInverse_empty]
  · exact sum_powerset_mul_momentInverse M (Finset.nonempty_iff_ne_empty.2 h) h0
private def subsetsContaining (i : ι) (S : Finset ι) : Finset (Finset ι) := S.powerset.filter (i ∈ ·)
private lemma partitionCumulant_eq {i : ι} {S : Finset ι} (hi : i ∈ S) :
    partitionCumulant M S = ∑ B ∈ subsetsContaining i S, M B * momentInverse M (S \ B) := by
  have h1 : partitionCumulant M S = ∑ P ∈ setPartitions S, ∑ D ∈ P,
      (if i ∈ D then signedFactorial (P.card - 1) * ∏ E ∈ P, M E else 0) := by
    refine Finset.sum_congr rfl fun P hP => ?_
    have hP' := mem_setPartitions.1 hP
    have hiP : i ∈ P.biUnion id := by rw [hP'.2.2]; exact hi
    obtain ⟨D₀, hD₀, hiD₀⟩ := mem_biUnion.1 hiP
    have hiD₀' : i ∈ D₀ := hiD₀
    rw [Finset.sum_eq_single_of_mem D₀ hD₀, if_pos hiD₀']
    intro E hE hne
    rw [if_neg]
    intro hiE
    exact Finset.disjoint_left.1 (hP'.2.1 E hE D₀ hD₀ hne) hiE hiD₀
  rw [h1, sum_setPartitions_sum_block S
      (fun P D => if i ∈ D then signedFactorial (P.card - 1) * ∏ E ∈ P, M E else 0),
    subsetsContaining, Finset.sum_filter]
  have h2 : ∀ D ∈ S.powerset, D ∉ S.powerset.erase ∅ →
      (if i ∈ D then M D * momentInverse M (S \ D) else 0) = 0 := by
    intro D hD hD'
    have : D = ∅ := by
      by_contra hne
      exact hD' (Finset.mem_erase.2 ⟨hne, hD⟩)
    subst this
    simp
  rw [← Finset.sum_subset (Finset.erase_subset _ _) h2]
  refine Finset.sum_congr rfl fun D hD => ?_
  have hne : D.Nonempty := Finset.nonempty_iff_ne_empty.2 (Finset.ne_of_mem_erase hD)
  split_ifs with hiD
  · rw [momentInverse, Finset.mul_sum]
    refine Finset.sum_congr rfl fun P hP => ?_
    have hn := notMem_of_mem_setPartitions_sdiff hne hP
    rw [Finset.card_insert_of_notMem hn, Finset.prod_insert hn, Nat.add_sub_cancel]
    ring
  · simp
abbrev _root_.YangMills.DeltaSharedProofs.p502294 := @partitionCumulant_eq
private theorem partitionCumulant_of_recursion (h0 : M ∅ = 1) (C : Finset ι → ℝ) (i : ι)
    (hrec : ∀ S, i ∈ S → M S = ∑ A ∈ subsetsContaining i S, C A * M (S \ A)) {S : Finset ι}
    (hi : i ∈ S) : partitionCumulant M S = C S := by
  have step1 : ∑ B ∈ subsetsContaining i S, M B * momentInverse M (S \ B) =
      ∑ B ∈ subsetsContaining i S, ∑ A ∈ subsetsContaining i B,
        C A * M (B \ A) * momentInverse M (S \ B) := by
    refine Finset.sum_congr rfl fun B hB => ?_
    rw [hrec B (Finset.mem_filter.1 hB).2, Finset.sum_mul]
  have step2 : ∑ B ∈ subsetsContaining i S, ∑ A ∈ subsetsContaining i B,
        C A * M (B \ A) * momentInverse M (S \ B) =
      ∑ A ∈ subsetsContaining i S, ∑ B ∈ S.powerset.filter (A ⊆ ·),
        C A * M (B \ A) * momentInverse M (S \ B) := by
    refine Finset.sum_comm' ?_
    intro B A
    simp only [subsetsContaining, mem_filter, mem_powerset]
    constructor
    · rintro ⟨⟨hBS, hiB⟩, hAB, hiA⟩
      exact ⟨⟨hBS, hAB⟩, hAB.trans hBS, hiA⟩
    · rintro ⟨⟨hBS, hAB⟩, hAS, hiA⟩
      exact ⟨⟨hBS, hAB hiA⟩, hAB, hiA⟩
  have step3 : ∀ A ∈ subsetsContaining i S, ∑ B ∈ S.powerset.filter (A ⊆ ·),
        C A * M (B \ A) * momentInverse M (S \ B) =
      C A * ∑ E ∈ (S \ A).powerset, M E * momentInverse M ((S \ A) \ E) := by
    intro A hA
    have hAS : A ⊆ S := Finset.mem_powerset.1 (Finset.mem_filter.1 hA).1
    rw [Finset.mul_sum]
    refine Finset.sum_nbij' (fun B => B \ A) (fun E => A ∪ E) ?_ ?_ ?_ ?_ ?_
    · intro B hB
      simp only [mem_filter, mem_powerset] at hB ⊢
      exact Finset.sdiff_subset_sdiff hB.1 (Finset.Subset.refl A)
    · intro E hE
      simp only [mem_filter, mem_powerset] at hE ⊢
      exact ⟨Finset.union_subset hAS (hE.trans Finset.sdiff_subset), Finset.subset_union_left⟩
    · intro B hB
      simp only [mem_filter, mem_powerset] at hB
      exact Finset.union_sdiff_of_subset hB.2
    · intro E hE
      simp only [mem_powerset] at hE
      rw [Finset.union_sdiff_cancel_left]
      exact Finset.disjoint_of_subset_right hE Finset.disjoint_sdiff
    · intro B hB
      simp only [mem_filter, mem_powerset] at hB
      have : (S \ A) \ (B \ A) = S \ B := by
        ext a
        simp only [mem_sdiff]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h1, fun h => h3 ⟨h, h2⟩⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, fun h => h2 (hB.2 h)⟩, fun h => h2 h.1⟩
      rw [this]
      ring
  rw [partitionCumulant_eq M hi, step1, step2, Finset.sum_congr rfl step3]
  have hS : S ∈ subsetsContaining i S :=
    Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.Subset.refl S), hi⟩
  rw [Finset.sum_eq_single_of_mem S hS]
  · rw [sum_powerset_mul_momentInverse_eq_ite M _ h0]
    simp
  · intro A hA hne
    rw [sum_powerset_mul_momentInverse_eq_ite M _ h0, if_neg, mul_zero]
    intro h
    have hAS : A ⊆ S := Finset.mem_powerset.1 (Finset.mem_filter.1 hA).1
    exact hne (Finset.Subset.antisymm hAS (Finset.sdiff_eq_empty_iff_subset.1 h))
end SetPartitions
end
section
open Finset
section Polynomials
open MvPolynomial Matrix
variable {σ : Type} [Fintype σ] [DecidableEq σ]
private def halfQuadraticForm (P : Matrix σ σ ℝ) : MvPolynomial σ ℝ :=
  C (1 / 2) * ∑ a, ∑ b, C (P a b) * (X a * X b)
private lemma pderiv_halfQuadraticForm {Q : Matrix σ σ ℝ} (hQ : Q.IsSymm) (c : σ) :
    pderiv c (halfQuadraticForm Q) = ∑ b, C (Q c b) * X b := by
  have h1 : ∀ a b, pderiv c (C (Q a b) * (X a * X b) : MvPolynomial σ ℝ) =
      (if a = c then C (Q a b) * X b else 0) + (if b = c then C (Q a b) * X a else 0) := by
    intro a b
    rw [pderiv_C_mul, pderiv_mul, pderiv_X, pderiv_X]
    by_cases ha : a = c <;> by_cases hb : b = c <;> simp [ha, hb, mul_add]
  have h2 : ∑ a, ∑ b, ((if a = c then C (Q a b) * X b else 0) +
      (if b = c then C (Q a b) * X a else 0) : MvPolynomial σ ℝ) =
      C 2 * ∑ b, C (Q c b) * X b := by
    simp only [Finset.sum_add_distrib]
    have e1 : ∑ a, ∑ b, (if a = c then C (Q a b) * X b else 0 : MvPolynomial σ ℝ) =
        ∑ b, C (Q c b) * X b := by
      rw [Finset.sum_eq_single c]
      · simp
      · intro a _ ha
        simp [ha]
      · simp
    have e2 : ∑ a, ∑ b, (if b = c then C (Q a b) * X a else 0 : MvPolynomial σ ℝ) =
        ∑ b, C (Q c b) * X b := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single c]
      · simp [hQ.apply a c]
      · intro b _ hb
        simp [hb]
      · simp
    rw [e1, e2, ← two_mul]
    simp [map_ofNat]
  rw [halfQuadraticForm, pderiv_C_mul, map_sum]
  simp only [map_sum, h1]
  rw [h2, ← mul_assoc, ← C_mul]
  norm_num
private lemma pderiv_finset_prod (c : σ) {ι : Type} [DecidableEq ι] (S : Finset ι)
    (f : ι → MvPolynomial σ ℝ) :
    pderiv c (∏ j ∈ S, f j) = ∑ j ∈ S, pderiv c (f j) * ∏ l ∈ S.erase j, f l := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, pderiv_mul, ih, Finset.sum_insert ha, Finset.erase_insert ha,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hne : a ≠ j := fun h => ha (h ▸ hj)
    rw [Finset.erase_insert_of_ne hne, Finset.prod_insert]
    · ring
    · simp [ha]
abbrev _root_.YangMills.SharedProofs.p117859 := @pderiv_finset_prod
variable (E : MvPolynomial σ ℝ →ₗ[ℝ] ℝ)
private lemma map_C_mul (r : ℝ) (H : MvPolynomial σ ℝ) : E (C r * H) = r * E H := by
  rw [← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
variable (hE : ∀ a H, E (X a * H) = E (pderiv a H))
include hE in
private lemma map_halfQuadraticForm_mul (P : Matrix σ σ ℝ) (F : MvPolynomial σ ℝ) :
    E (halfQuadraticForm P * F) = (1 / 2) * P.trace * E F +
      (1 / 2) * ∑ a, ∑ c, P a c * E (X a * pderiv c F) := by
  have h1 : ∀ a b, E (C (P a b) * (X a * X b) * F) =
      (if a = b then P a b * E F else 0) + P a b * E (X a * pderiv b F) := by
    intro a b
    have : (C (P a b) * (X a * X b) * F : MvPolynomial σ ℝ) = C (P a b) * (X b * (X a * F)) := by ring
    rw [this, map_C_mul, hE, pderiv_mul, pderiv_X, map_add]
    by_cases h : a = b
    · subst h
      simp [mul_add]
    · simp [h]
  rw [halfQuadraticForm, mul_assoc, map_C_mul, Finset.sum_mul, map_sum]
  simp only [Finset.sum_mul, map_sum, h1, Finset.sum_add_distrib]
  rw [mul_add]
  congr 1
  have : ∑ a, ∑ b, (if a = b then P a b * E F else 0) = P.trace * E F := by
    simp [Matrix.trace, Finset.sum_mul]
  rw [this]
  ring
private lemma halfQuadraticForm_mul_eq (P Q : Matrix σ σ ℝ) :
    halfQuadraticForm (P * Q) = C (1 / 2) * ∑ a, ∑ c, C (P a c) * (X a * ∑ b, C (Q c b) * X b) := by
  rw [halfQuadraticForm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.mul_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
  rw [C_mul]
  ring
variable {ι : Type} [DecidableEq ι] (Q : ι → Matrix σ σ ℝ)
include hE in
private lemma map_halfQuadraticForm_mul_prod_step (hQ : ∀ i, (Q i).IsSymm) (P : Matrix σ σ ℝ)
    (S : Finset ι) :
    E (halfQuadraticForm P * ∏ j ∈ S, halfQuadraticForm (Q j)) =
      (1 / 2) * P.trace * E (∏ j ∈ S, halfQuadraticForm (Q j)) +
        ∑ j ∈ S, E (halfQuadraticForm (P * Q j) * ∏ l ∈ S.erase j, halfQuadraticForm (Q l)) := by
  rw [map_halfQuadraticForm_mul E hE]
  congr 1
  simp only [pderiv_finset_prod, pderiv_halfQuadraticForm (hQ _)]
  have key : ∀ j ∈ S, E (halfQuadraticForm (P * Q j) * ∏ l ∈ S.erase j, halfQuadraticForm (Q l)) =
      (1 / 2) * ∑ a, ∑ c, P a c *
        E (X a * ((∑ b, C (Q j c b) * X b) * ∏ l ∈ S.erase j, halfQuadraticForm (Q l))) := by
    intro j _
    rw [halfQuadraticForm_mul_eq, mul_assoc, map_C_mul]
    congr 1
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_assoc, map_C_mul, mul_assoc]
  have hsum : ∀ a c, P a c * E (X a * ∑ j ∈ S, (∑ b, C (Q j c b) * X b) *
        ∏ l ∈ S.erase j, halfQuadraticForm (Q l)) =
      ∑ j ∈ S, P a c * E (X a * ((∑ b, C (Q j c b) * X b) *
        ∏ l ∈ S.erase j, halfQuadraticForm (Q l))) := by
    intro a c
    rw [Finset.mul_sum, map_sum, Finset.mul_sum]
  rw [Finset.sum_congr (s₁ := S) rfl key, ← Finset.mul_sum]
  congr 1
  simp only [hsum]
  calc _ = ∑ a, ∑ j ∈ S, ∑ c, P a c *
        E (X a * ((∑ b, C (Q j c b) * X b) * ∏ l ∈ S.erase j, halfQuadraticForm (Q l))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm
private def orderings (T : Finset ι) : Finset (List ι) := (T.val.lists).toFinset
private lemma mem_orderings {T : Finset ι} {l : List ι} : l ∈ orderings T ↔ T.val = ↑l := by
  simp [orderings, Multiset.mem_lists_iff]
private lemma sum_orderings {T : Finset ι} (hT : T.Nonempty) (g : List ι → ℝ) :
    ∑ l ∈ orderings T, g l = ∑ j ∈ T, ∑ l ∈ orderings (T.erase j), g (j :: l) := by
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => x.1 :: x.2) ?_ ?_ ?_ ?_
  · rintro ⟨j, l⟩ hx
    simp only [mem_sigma, mem_orderings] at hx ⊢
    rw [← Multiset.cons_coe, ← hx.2, Finset.erase_val, Multiset.cons_erase hx.1]
  · rintro ⟨j, l⟩ _ ⟨j', l'⟩ _ h
    simp only [List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · intro l hl
    rw [mem_orderings] at hl
    cases l with
    | nil =>
      have : T = ∅ := by
        apply Finset.val_eq_zero.1
        simpa using hl
      simp [this] at hT
    | cons j l =>
      have hj : j ∈ T := by
        rw [← Finset.mem_val, hl]
        simp
      refine ⟨⟨j, l⟩, ?_, rfl⟩
      simp only [mem_sigma, mem_orderings]
      refine ⟨hj, ?_⟩
      rw [Finset.erase_val, hl, ← Multiset.cons_coe, Multiset.erase_cons_head]
  · intros
    rfl
private def orderedTraceSum (P : Matrix σ σ ℝ) (T : Finset ι) : ℝ :=
  (1 / 2) * ∑ l ∈ orderings T, (P * (l.map Q).prod).trace
private lemma orderedTraceSum_empty (P : Matrix σ σ ℝ) :
    orderedTraceSum Q P (∅ : Finset ι) = (1 / 2) * P.trace := by
  have : orderings (∅ : Finset ι) = {[]} := by
    ext l
    simp only [mem_orderings, mem_singleton, Finset.empty_val]
    constructor
    · intro h
      simpa using h.symm
    · rintro rfl
      rfl
  simp [orderedTraceSum, this]
private lemma orderedTraceSum_rec {T : Finset ι} (hT : T.Nonempty) (P : Matrix σ σ ℝ) :
    orderedTraceSum Q P T = ∑ j ∈ T, orderedTraceSum Q (P * Q j) (T.erase j) := by
  rw [orderedTraceSum, sum_orderings hT, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [orderedTraceSum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [mul_assoc]
include hE in
private theorem map_halfQuadraticForm_mul_prod (hQ : ∀ i, (Q i).IsSymm) (S : Finset ι)
    (P : Matrix σ σ ℝ) :
    E (halfQuadraticForm P * ∏ j ∈ S, halfQuadraticForm (Q j)) =
      ∑ T ∈ S.powerset, orderedTraceSum Q P T * E (∏ j ∈ S \ T, halfQuadraticForm (Q j)) := by
  induction S using Finset.strongInduction generalizing P with
  | H S ih =>
    rw [map_halfQuadraticForm_mul_prod_step E hE Q hQ,
      ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset S), orderedTraceSum_empty, sdiff_empty]
    congr 1
    have h1 : ∀ j ∈ S, E (halfQuadraticForm (P * Q j) * ∏ l ∈ S.erase j, halfQuadraticForm (Q l)) =
        ∑ T ∈ (S.erase j).powerset, orderedTraceSum Q (P * Q j) T *
          E (∏ l ∈ (S.erase j) \ T, halfQuadraticForm (Q l)) :=
      fun j hj => ih _ (Finset.erase_ssubset hj) _
    rw [Finset.sum_congr (s₁ := S) rfl h1, Finset.sum_sigma']
    have h2 : ∀ T ∈ S.powerset.erase ∅,
        orderedTraceSum Q P T * E (∏ j ∈ S \ T, halfQuadraticForm (Q j)) =
        ∑ j ∈ T, orderedTraceSum Q (P * Q j) (T.erase j) *
          E (∏ l ∈ S \ T, halfQuadraticForm (Q l)) := by
      intro T hT
      rw [orderedTraceSum_rec Q (Finset.nonempty_iff_ne_empty.2 (Finset.ne_of_mem_erase hT)),
        Finset.sum_mul]
    rw [Finset.sum_congr (s₁ := S.powerset.erase ∅) rfl h2, Finset.sum_sigma']
    refine Finset.sum_nbij' (fun x => ⟨insert x.1 x.2, x.1⟩) (fun y => ⟨y.2, y.1.erase y.2⟩)
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨j, T⟩ hx
      simp only [mem_sigma, mem_powerset] at hx ⊢
      refine ⟨Finset.mem_erase.2 ⟨Finset.insert_ne_empty _ _, ?_⟩, Finset.mem_insert_self _ _⟩
      rw [Finset.mem_powerset]
      exact Finset.insert_subset hx.1 (hx.2.trans (Finset.erase_subset _ _))
    · rintro ⟨T, j⟩ hy
      simp only [mem_sigma, mem_erase, mem_powerset] at hy ⊢
      exact ⟨hy.1.2 hy.2, Finset.erase_subset_erase _ hy.1.2⟩
    · rintro ⟨j, T⟩ hx
      simp only [mem_sigma, mem_powerset] at hx
      have : j ∉ T := fun h => by simpa using hx.2 h
      simp [Finset.erase_insert this]
    · rintro ⟨T, j⟩ hy
      simp only [mem_sigma] at hy
      simp [Finset.insert_erase hy.2]
    · rintro ⟨j, T⟩ hx
      simp only [mem_sigma, mem_powerset] at hx
      have hjT : j ∉ T := fun h => by simpa using hx.2 h
      have e : S.erase j \ T = S \ insert j T := by
        ext a
        simp only [mem_sdiff, mem_erase, mem_insert, not_or]
        tauto
      simp only [Finset.erase_insert hjT, e]
include hE in
private theorem moment_recursion (hQ : ∀ i, (Q i).IsSymm) (i : ι) (S : Finset ι) (hi : i ∈ S) :
    E (∏ j ∈ S, halfQuadraticForm (Q j)) =
      ∑ A ∈ subsetsContaining i S, orderedTraceSum Q (Q i) (A.erase i) *
        E (∏ j ∈ S \ A, halfQuadraticForm (Q j)) := by
  rw [← Finset.mul_prod_erase S _ hi, map_halfQuadraticForm_mul_prod E hE Q hQ]
  refine Finset.sum_nbij' (fun T => insert i T) (fun A => A.erase i) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_powerset] at hT
    simp only [subsetsContaining, mem_filter, mem_powerset, mem_insert, true_or, and_true]
    exact Finset.insert_subset hi (hT.trans (Finset.erase_subset _ _))
  · intro A hA
    simp only [subsetsContaining, mem_filter, mem_powerset] at hA
    rw [Finset.mem_powerset]
    exact Finset.erase_subset_erase _ hA.1
  · intro T hT
    rw [Finset.mem_powerset] at hT
    have : i ∉ T := fun h => by simpa using hT h
    exact Finset.erase_insert this
  · intro A hA
    simp only [subsetsContaining, mem_filter] at hA
    exact Finset.insert_erase hA.2
  · intro T hT
    rw [Finset.mem_powerset] at hT
    have hjT : i ∉ T := fun h => by simpa using hT h
    have e : S.erase i \ T = S \ insert i T := by
      ext a
      simp only [mem_sdiff, mem_erase, mem_insert, not_or]
      tauto
    rw [Finset.erase_insert hjT, e]
include hE in
private theorem partitionCumulant_halfQuadraticForms (hQ : ∀ i, (Q i).IsSymm) (hE1 : E 1 = 1)
    (i : ι) (S : Finset ι) (hi : i ∈ S) :
    partitionCumulant (fun J => E (∏ j ∈ J, halfQuadraticForm (Q j))) S =
      orderedTraceSum Q (Q i) (S.erase i) := by
  refine partitionCumulant_of_recursion _ (by simpa using hE1)
    (fun A => orderedTraceSum Q (Q i) (A.erase i)) i ?_ hi
  intro S' hS'
  exact moment_recursion E hE Q hQ i S' hS'
end Polynomials
end
section
open Finset MeasureTheory ProbabilityTheory
section GaussianMoments
private def gaussianMoment (k : ℕ) : ℝ := ∫ x, x ^ k ∂(gaussianReal 0 1)
private lemma integrable_pow_gaussianReal (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by apply _root_.YangMills.SharedProofs.p8958 <;> assumption
private lemma gaussianMoment_zero : gaussianMoment 0 = 1 := by simp [gaussianMoment]
private lemma gaussianMoment_one : gaussianMoment 1 = 0 := by simp [gaussianMoment]
private lemma gaussianMoment_add_two (k : ℕ) :
    gaussianMoment (k + 2) = (k + 1) * gaussianMoment k := by apply _root_.YangMills.DeltaSharedProofs.p500965 <;> assumption
end GaussianMoments
section Expectation
open MvPolynomial
variable {σ : Type} [Fintype σ] [DecidableEq σ]
private def gaussianExpectation : MvPolynomial σ ℝ →ₗ[ℝ] ℝ :=
  (basisMonomials σ ℝ).constr ℝ fun m => ∏ s, gaussianMoment (m s)
private lemma gaussianExpectation_monomial (m : σ →₀ ℕ) (c : ℝ) :
    gaussianExpectation (monomial m c) = c * ∏ s, gaussianMoment (m s) := by
  have : (monomial m c : MvPolynomial σ ℝ) = c • basisMonomials σ ℝ m := by
    simp [MvPolynomial.smul_monomial]
  rw [this, map_smul, gaussianExpectation, Module.Basis.constr_basis, smul_eq_mul]
private lemma gaussianExpectation_one : gaussianExpectation (1 : MvPolynomial σ ℝ) = 1 := by
  have : (1 : MvPolynomial σ ℝ) = monomial 0 1 := rfl
  rw [this, gaussianExpectation_monomial]
  simp [gaussianMoment_zero]
private lemma gaussianExpectation_X_mul (a : σ) (H : MvPolynomial σ ℝ) :
    gaussianExpectation (X a * H) = gaussianExpectation (pderiv a H) := by
  induction H using MvPolynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, map_add, map_add, hp, hq]
  | monomial u c =>
    have h1 : (X a * monomial u c : MvPolynomial σ ℝ) = monomial (Finsupp.single a 1 + u) c := by
      rw [X, monomial_mul, one_mul]
    rw [h1, pderiv_monomial, gaussianExpectation_monomial, gaussianExpectation_monomial,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
    have h2 : ∏ s ∈ Finset.univ.erase a, gaussianMoment ((Finsupp.single a 1 + u : σ →₀ ℕ) s) =
        ∏ s ∈ Finset.univ.erase a, gaussianMoment ((u - Finsupp.single a 1 : σ →₀ ℕ) s) := by
      refine Finset.prod_congr rfl fun s hs => ?_
      have hne : a ≠ s := fun h => by simp [h] at hs
      simp [Finsupp.single_apply, hne]
    rw [h2]
    rcases hk : u a with _ | k
    · simp [hk, gaussianMoment_one]
    · simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.tsub_apply, hk]
      rw [show 1 + (k + 1) = k + 2 by ring, gaussianMoment_add_two, Nat.add_sub_cancel]
      push_cast
      ring
private structure IsStandardGaussianFamily {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
    (z : Ω → σ → ℝ) : Prop where
  integrable : ∀ m : σ → ℕ, Integrable (fun ω => ∏ s, z ω s ^ m s) ν
  integral : ∀ m : σ → ℕ, ∫ ω, ∏ s, z ω s ^ m s ∂ν = ∏ s, gaussianMoment (m s)
variable {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} {z : Ω → σ → ℝ}
private lemma IsStandardGaussianFamily.eval_polynomial (h : IsStandardGaussianFamily ν z)
    (H : MvPolynomial σ ℝ) :
    Integrable (fun ω => MvPolynomial.eval (z ω) H) ν ∧
      ∫ ω, MvPolynomial.eval (z ω) H ∂ν = gaussianExpectation H := by
  induction H using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add]
    exact ⟨hp.1.add hq.1, by rw [integral_add hp.1 hq.1, hp.2, hq.2]⟩
  | monomial u c =>
    have e : ∀ ω, MvPolynomial.eval (z ω) (monomial u c) = c * ∏ s, z ω s ^ u s := by
      intro ω
      rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
    simp only [e]
    exact ⟨(h.integrable u).const_mul c, by
      rw [integral_const_mul, h.integral u, gaussianExpectation_monomial]⟩
end Expectation
end
section
open Finset
section Cycles
open Matrix
variable {τ : Type} [Fintype τ] [DecidableEq τ]
private lemma mem_orderings_iff {ι : Type} [DecidableEq ι] {T : Finset ι} {l : List ι} :
    l ∈ orderings T ↔ l.Nodup ∧ ∀ x, x ∈ l ↔ x ∈ T := by
  rw [mem_orderings]
  constructor
  · intro h
    have hn : (↑l : Multiset ι).Nodup := h ▸ T.nodup
    refine ⟨Multiset.coe_nodup.1 hn, fun x => ?_⟩
    rw [← Finset.mem_val, h, Multiset.mem_coe]
  · rintro ⟨hn, hm⟩
    refine (Multiset.Nodup.ext T.nodup (Multiset.coe_nodup.2 hn)).2 fun x => ?_
    rw [Finset.mem_val, Multiset.mem_coe, hm]
private lemma sum_perm_fixing_zero {m : ℕ} (g : List (Fin (m + 1)) → ℝ) :
    ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin (m + 1)) => σ 0 = 0),
        g (List.ofFn fun c : Fin m => σ c.succ) =
      ∑ l ∈ orderings (Finset.univ.erase (0 : Fin (m + 1))), g l := by
  refine Finset.sum_bij (fun σ _ => List.ofFn fun c : Fin m => σ c.succ) ?_ ?_ ?_ ?_
  · intro σ hσ
    have h0 : σ 0 = 0 := (Finset.mem_filter.1 hσ).2
    rw [mem_orderings_iff]
    refine ⟨List.nodup_ofFn.2 fun a b h => Fin.succ_injective _ (σ.injective h), fun x => ?_⟩
    simp only [List.mem_ofFn, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨c, rfl⟩ hc
      have : σ c.succ = σ 0 := by rw [hc, h0]
      exact Fin.succ_ne_zero c (σ.injective this)
    · intro hx
      have hne : σ.symm x ≠ 0 := by
        intro h
        apply hx
        rw [← σ.apply_symm_apply x, h, h0]
      refine ⟨(σ.symm x).pred hne, ?_⟩
      simp
  · intro σ hσ σ' hσ' h
    have h0 : σ 0 = 0 := (Finset.mem_filter.1 hσ).2
    have h0' : σ' 0 = 0 := (Finset.mem_filter.1 hσ').2
    have h1 := List.ofFn_injective h
    ext c
    refine congrArg Fin.val ?_
    induction c using Fin.cases with
    | zero => rw [h0, h0']
    | succ c => exact congrFun h1 c
  · intro l hl
    obtain ⟨hn, hm⟩ := mem_orderings_iff.1 hl
    have hlen : l.length = m := by
      have h1 : l.toFinset = Finset.univ.erase (0 : Fin (m + 1)) := by
        ext x
        simp only [List.mem_toFinset, hm]
      have h2 := List.toFinset_card_of_nodup hn
      rw [h1] at h2
      simp at h2
      omega
    let g' : Fin m → Fin (m + 1) := fun c => l.get (c.cast hlen.symm)
    have hg : List.ofFn g' = l := by
      refine List.ext_getElem (by simp [hlen]) ?_
      intro i h1 h2
      simp [g']
    have hinj : Function.Injective g' := by
      rw [← List.nodup_ofFn, hg]
      exact hn
    have h0 : ∀ c, g' c ≠ 0 := by
      intro c h
      have : g' c ∈ l := by
        rw [← hg]
        exact List.mem_ofFn.2 ⟨c, rfl⟩
      rw [h, hm] at this
      simp at this
    let f : Fin (m + 1) → Fin (m + 1) := Fin.cons 0 g'
    have hf : Function.Injective f := by
      intro a b
      induction a using Fin.cases with
      | zero =>
        induction b using Fin.cases with
        | zero => simp
        | succ b =>
          intro h
          exact absurd h.symm (by simpa [f] using h0 b)
      | succ a =>
        induction b using Fin.cases with
        | zero =>
          intro h
          exact absurd h (by simpa [f] using h0 a)
        | succ b =>
          intro h
          have : g' a = g' b := by simpa [f] using h
          rw [hinj this]
    refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), ?_, ?_⟩
    · simp [f]
    · simpa [f] using hg
  · intros
    rfl
variable {m : ℕ}
private def cyclicTrace {n : ℕ} (R : Fin n → Matrix τ τ ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ((List.ofFn fun c : Fin n => R (σ c)).prod).trace
private lemma orderedTraceSum_eq_sum_fixing_zero (R : Fin (m + 1) → Matrix τ τ ℝ) :
    orderedTraceSum R (R 0) (Finset.univ.erase 0) =
      (1 / 2) * ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin (m + 1)) => σ 0 = 0),
        cyclicTrace R σ := by
  rw [orderedTraceSum, ← sum_perm_fixing_zero (fun l => (R 0 * (l.map R).prod).trace)]
  congr 1
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have h0 : σ 0 = 0 := (Finset.mem_filter.1 hσ).2
  rw [cyclicTrace, List.ofFn_succ, List.prod_cons, h0, List.map_ofFn]
  rfl
private lemma neg_succ_eq_succ_rev (i : Fin m) : -(i.succ : Fin (m + 1)) = (Fin.rev i).succ := by
  rw [neg_eq_iff_add_eq_zero]
  ext
  simp only [Fin.val_add, Fin.val_succ, Fin.val_rev, Fin.val_zero]
  have : (i : ℕ) < m := i.2
  rw [show (i : ℕ) + 1 + (m - (i + 1) + 1) = m + 1 by omega]
  simp
private lemma cyclicTrace_reverse (R : Fin (m + 1) → Matrix τ τ ℝ) (hR : ∀ i, (R i).IsSymm)
    (σ : Equiv.Perm (Fin (m + 1))) :
    cyclicTrace R ((Equiv.neg (Fin (m + 1))).trans σ) = cyclicTrace R σ := by
  set L : List (Matrix τ τ ℝ) := List.ofFn fun c : Fin m => R (σ c.succ) with hL
  have hrev : (List.ofFn fun c : Fin m => R (σ (-(c.succ : Fin (m + 1))))) = L.reverse := by
    refine List.ext_getElem (by simp [hL]) ?_
    intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_reverse, hL]
    have hi : i < m := by simpa using h1
    have e := neg_succ_eq_succ_rev (⟨i, hi⟩ : Fin m)
    have e2 : Fin.rev (⟨i, hi⟩ : Fin m) =
        ⟨(List.ofFn fun c : Fin m => R (σ c.succ)).length - 1 - i, by simp; omega⟩ := by
      ext
      simp only [Fin.val_rev, List.length_ofFn]
      omega
    rw [e2] at e
    simp only [Fin.succ_mk] at e ⊢
    rw [e]
  have hsym : L.map Matrix.transpose = L := by
    rw [hL, List.map_ofFn]
    congr 1
    ext1 c
    exact hR _
  have hT : (L.reverse.prod) = (L.prod)ᵀ := by
    rw [Matrix.transpose_list_prod, hsym]
  simp only [cyclicTrace, List.ofFn_succ, List.prod_cons, Equiv.trans_apply, Equiv.neg_apply,
    neg_zero]
  rw [hrev, ← hL, hT]
  calc (R (σ 0) * (L.prod)ᵀ).trace = ((R (σ 0) * (L.prod)ᵀ)ᵀ).trace :=
        (Matrix.trace_transpose _).symm
    _ = (L.prod * R (σ 0)).trace := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose, (hR _).eq]
    _ = _ := Matrix.trace_mul_comm _ _
private lemma one_ne_neg_one_of_two_le (hm : 2 ≤ m) : (1 : Fin (m + 1)) ≠ -1 := by
  intro h
  have h2 : (1 : Fin (m + 1)) + 1 = 0 := by
    nth_rw 1 [h]
    simp
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h3 := congrArg Fin.val h2
  simp only [Fin.val_add, Fin.val_one, Fin.val_zero] at h3
  rw [Nat.mod_eq_of_lt (by omega)] at h3
  omega
private lemma neg_one_eq_one_fin_two : (-1 : Fin 2) = 1 := by decide
private theorem orderedTraceSum_eq_cyclic {n : ℕ} [NeZero n] (hn : 2 ≤ n) (R : Fin n → Matrix τ τ ℝ)
    (hR : ∀ i, (R i).IsSymm) :
    orderedTraceSum R (R 0) (Finset.univ.erase 0) =
      (if n = 2 then 1 / 2 else 1) *
        ∑ σ ∈ CyclicFormula.unorientedCyclicOrders n, cyclicTrace R σ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [orderedTraceSum_eq_sum_fixing_zero]
  by_cases h2 : m + 1 = 2
  · obtain rfl : m = 1 := by omega
    rw [if_pos rfl]
    have hset : (Finset.univ.filter fun σ : Equiv.Perm (Fin (1 + 1)) => σ 0 = 0) =
        CyclicFormula.unorientedCyclicOrders (1 + 1) := by
      ext σ
      simp only [CyclicFormula.unorientedCyclicOrders, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        refine ⟨h, ?_⟩
        have : (-1 : Fin (1 + 1)) = 1 := neg_one_eq_one_fin_two
        rw [this]
      · exact fun h => h.1
    rw [hset]
  · rw [if_neg h2, one_mul]
    have hm : 2 ≤ m := by omega
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter fun σ : Equiv.Perm (Fin (m + 1)) => σ 0 = 0)
      (fun σ => σ 1 ≤ σ (-1)) (cyclicTrace R)
    have hcyc : (Finset.univ.filter fun σ : Equiv.Perm (Fin (m + 1)) => σ 0 = 0).filter
        (fun σ => σ 1 ≤ σ (-1)) = CyclicFormula.unorientedCyclicOrders (m + 1) := by
      rw [Finset.filter_filter]
      rfl
    have hother : ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin (m + 1)) => σ 0 = 0).filter
        (fun σ => ¬ σ 1 ≤ σ (-1)), cyclicTrace R σ =
        ∑ σ ∈ CyclicFormula.unorientedCyclicOrders (m + 1), cyclicTrace R σ := by
      refine Finset.sum_nbij' (fun σ => (Equiv.neg (Fin (m + 1))).trans σ)
        (fun σ => (Equiv.neg (Fin (m + 1))).trans σ) ?_ ?_ ?_ ?_ ?_
      · intro σ hσ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
        simp only [CyclicFormula.unorientedCyclicOrders, Finset.mem_filter, Finset.mem_univ, true_and,
          Equiv.trans_apply, Equiv.neg_apply, neg_zero, neg_neg]
        exact ⟨hσ.1, (not_le.1 hσ.2).le⟩
      · intro σ hσ
        simp only [CyclicFormula.unorientedCyclicOrders, Finset.mem_filter, Finset.mem_univ,
          true_and] at hσ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.trans_apply,
          Equiv.neg_apply, neg_zero, neg_neg]
        refine ⟨hσ.1, fun h => ?_⟩
        exact one_ne_neg_one_of_two_le hm (σ.injective (le_antisymm hσ.2 h))
      · intro σ _
        ext c
        simp
      · intro σ _
        ext c
        simp
      · intro σ _
        exact (cyclicTrace_reverse R hR σ).symm
    rw [← hsplit, hcyc, hother]
    ring
private lemma trace_prod_mul_sq_eq (A G : Matrix τ τ ℝ) (hG : A * A = G) (L : List (Matrix τ τ ℝ)) :
    ((L.map fun q => q * G).prod).trace = ((L.map fun q => A * q * A).prod).trace := by
  have h : ∀ L : List (Matrix τ τ ℝ), A * (L.map fun q => q * G).prod =
      (L.map fun q => A * q * A).prod * A := by
    intro L
    induction L with
    | nil => simp
    | cons q L ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [← hG]
      rw [← hG] at ih
      calc A * (q * (A * A) * (L.map fun q => q * (A * A)).prod)
          = A * q * A * (A * (L.map fun q => q * (A * A)).prod) := by
            simp only [mul_assoc]
        _ = _ := by
            rw [ih]
            simp only [mul_assoc]
  cases L with
  | nil => simp
  | cons q L =>
    simp only [List.map_cons, List.prod_cons]
    calc (q * G * (L.map fun q => q * G).prod).trace
        = (q * A * (A * (L.map fun q => q * G).prod)).trace := by
          rw [← hG]
          simp only [mul_assoc]
      _ = (q * A * ((L.map fun q => A * q * A).prod * A)).trace := by rw [h]
      _ = (A * (q * A * (L.map fun q => A * q * A).prod)).trace := by
          rw [← Matrix.mul_assoc (q * A) _ A, Matrix.trace_mul_comm]
      _ = _ := by simp only [mul_assoc]
private def threeCopies (r : Matrix τ τ ℝ) : Matrix (τ × Fin 3) (τ × Fin 3) ℝ :=
  Matrix.blockDiagonal fun _ => r
private lemma threeCopies_isSymm {r : Matrix τ τ ℝ} (h : r.IsSymm) : (threeCopies r).IsSymm := by
  rw [Matrix.IsSymm, threeCopies, Matrix.blockDiagonal_transpose, h.eq]
private lemma trace_threeCopies_prod (L : List (Matrix τ τ ℝ)) :
    ((L.map threeCopies).prod).trace = 3 * (L.prod).trace := by
  have h : (L.map threeCopies).prod = threeCopies L.prod := by
    induction L with
    | nil =>
      simp only [List.map_nil, List.prod_nil, threeCopies]
      exact (Matrix.blockDiagonal_one).symm
    | cons q L ih =>
      simp only [List.map_cons, List.prod_cons, ih, threeCopies]
      exact (Matrix.blockDiagonal_mul _ _).symm
  rw [h, threeCopies, Matrix.trace_blockDiagonal]
  simp
private lemma cyclicTrace_threeCopies {n : ℕ} (R : Fin n → Matrix τ τ ℝ) (σ : Equiv.Perm (Fin n)) :
    cyclicTrace (fun i => threeCopies (R i)) σ = 3 * cyclicTrace R σ := by
  have : (List.ofFn fun c : Fin n => threeCopies (R (σ c))) =
      (List.ofFn fun c : Fin n => R (σ c)).map threeCopies := by
    rw [List.map_ofFn]
    rfl
  rw [cyclicTrace, this, trace_threeCopies_prod]
  rfl
end Cycles
end
section
open Finset MeasureTheory ProbabilityTheory MvPolynomial Matrix
open scoped MatrixOrder
section GaussianLaw
variable {k : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]
private theorem jointCumulant_halfQuadraticForms [NeZero k] {Ω : Type} [MeasurableSpace Ω]
    {ν : Measure Ω} {z : Ω → σ → ℝ} (h : IsStandardGaussianFamily ν z) (Q : Fin k → Matrix σ σ ℝ)
    (hQ : ∀ i, (Q i).IsSymm) :
    jointCumulant ν (fun i ω => MvPolynomial.eval (z ω) (halfQuadraticForm (Q i))) =
      orderedTraceSum Q (Q 0) (Finset.univ.erase 0) := by
  have hM : ∀ J : Finset (Fin k), ∫ ω, ∏ i ∈ J, MvPolynomial.eval (z ω) (halfQuadraticForm (Q i)) ∂ν =
      gaussianExpectation (∏ j ∈ J, halfQuadraticForm (Q j)) := by
    intro J
    rw [← (h.eval_polynomial _).2]
    simp only [map_prod]
  rw [← partitionCumulant_halfQuadraticForms gaussianExpectation gaussianExpectation_X_mul Q hQ
      gaussianExpectation_one 0 Finset.univ (Finset.mem_univ 0), partitionCumulant,
    ← sum_finpartition_eq_sum_setPartitions Finset.univ (fun P => signedFactorial (P.card - 1) *
      ∏ D ∈ P, gaussianExpectation (∏ j ∈ D, halfQuadraticForm (Q j)))]
  simp only [jointCumulant, hM, signedFactorial]
private lemma jointCumulant_map {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {ν : Measure Ω} {T : Ω → Ω'} (hT : Measurable T) {X : Fin k → Ω' → ℝ}
    (hX : ∀ i, Measurable (X i)) :
    jointCumulant (ν.map T) X = jointCumulant ν (fun i ω => X i (T ω)) := by
  unfold jointCumulant
  refine Finset.sum_congr rfl fun π _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun J _ => ?_
  rw [integral_map hT.aemeasurable
    (Finset.measurable_prod _ (fun i _ => hX i)).aestronglyMeasurable]
abbrev _root_.YangMills.SharedProofs.p3362 := @jointCumulant_map
private lemma isStandardGaussianFamily_pi (τ : Type) [Fintype τ] [DecidableEq τ] :
    IsStandardGaussianFamily (Measure.pi fun _ : τ => gaussianReal 0 1) (fun w : τ → ℝ => w) where
  integrable m := Integrable.fintype_prod (f := fun s x => x ^ m s)
    (fun s => integrable_pow_gaussianReal (m s))
  integral m := integral_fintype_prod_eq_prod (fun s (x : ℝ) => x ^ m s)
private lemma isStandardGaussianFamily_threeCopies (τ : Type) [Fintype τ] [DecidableEq τ] :
    IsStandardGaussianFamily (Measure.pi fun _ : Fin 3 => Measure.pi fun _ : τ => gaussianReal 0 1)
      (fun (W : Fin 3 → τ → ℝ) (p : τ × Fin 3) => W p.2 p.1) where
  integrable m := by
    simp only [Fintype.prod_prod_type_right]
    exact Integrable.fintype_prod (f := fun e (w : τ → ℝ) => ∏ a, w a ^ m (a, e))
      (fun e => (isStandardGaussianFamily_pi τ).integrable fun a => m (a, e))
  integral m := by
    simp only [Fintype.prod_prod_type_right]
    rw [integral_fintype_prod_eq_prod (fun e (w : τ → ℝ) => ∏ a, w a ^ m (a, e))]
    exact Finset.prod_congr rfl fun e _ => (isStandardGaussianFamily_pi τ).integral fun a => m (a, e)
private lemma eval_halfQuadraticForm (w : σ → ℝ) (P : Matrix σ σ ℝ) :
    MvPolynomial.eval w (halfQuadraticForm P) = (1 / 2) * (w ⬝ᵥ P *ᵥ w) := by
  simp only [halfQuadraticForm, map_mul, map_sum, eval_C, eval_X, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
private def sqrtMap {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (w : Fin N → ℝ) :
    EuclideanSpace ℝ (Fin N) :=
  toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 w)
private lemma measurable_sqrtMap {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : Measurable (sqrtMap A) := by
  unfold sqrtMap
  fun_prop
private lemma multivariateGaussian_eq_map_sqrtMap {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) :
    multivariateGaussian 0 G =
      (Measure.pi fun _ : Fin N => gaussianReal 0 1).map (sqrtMap (CFC.sqrt G)) := by
  rw [multivariateGaussian, ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext1 w
  simp [sqrtMap]
private lemma sqrtMap_apply {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (w : Fin N → ℝ) :
    (fun a => sqrtMap A w a) = A *ᵥ w := by
  ext a
  simp [sqrtMap]
private lemma halfQuadraticForm_sqrtMap {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsSymm)
    (Q : Matrix (Fin N) (Fin N) ℝ) (w : Fin N → ℝ) :
    (1 / 2) * ((fun a => sqrtMap A w a) ⬝ᵥ Q.mulVec fun a => sqrtMap A w a) =
      MvPolynomial.eval w (halfQuadraticForm (A * Q * A)) := by
  rw [eval_halfQuadraticForm, sqrtMap_apply]
  congr 1
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w A,
    ← Matrix.mulVec_transpose, hA.eq]
private lemma eval_threeCopies {τ : Type} [Fintype τ] [DecidableEq τ] (W : Fin 3 → τ → ℝ)
    (R : Matrix τ τ ℝ) :
    MvPolynomial.eval (fun p : τ × Fin 3 => W p.2 p.1) (halfQuadraticForm (threeCopies R)) =
      ∑ e : Fin 3, MvPolynomial.eval (W e) (halfQuadraticForm R) := by
  simp only [eval_halfQuadraticForm, ← Finset.mul_sum]
  congr 1
  simp only [dotProduct, mulVec, Fintype.sum_prod_type_right, threeCopies, Matrix.blockDiagonal_apply]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp
private lemma measurable_halfQuadraticForm {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℝ) :
    Measurable fun x : EuclideanSpace ℝ (Fin N) =>
      (1 / 2 : ℝ) * ((fun a => x a) ⬝ᵥ Q.mulVec fun a => x a) := by
  simp only [dotProduct, mulVec]
  fun_prop
end GaussianLaw
theorem gaussianQuadraticCumulant : gaussianQuadraticCumulantStatement := by
  intro N G hG n _ hn Qs hQs
  obtain ⟨A, hAdef⟩ : ∃ A, A = CFC.sqrt G := ⟨_, rfl⟩
  have hmap : multivariateGaussian 0 G =
      (Measure.pi fun _ : Fin N => gaussianReal 0 1).map (sqrtMap A) := by
    rw [hAdef]
    exact multivariateGaussian_eq_map_sqrtMap G
  have hAA : A * A = G := by
    rw [hAdef]
    exact CFC.sqrt_mul_sqrt_self _ hG.nonneg
  have hA : A.IsSymm := by
    have h1 : IsSelfAdjoint A := by
      rw [hAdef]
      exact (CFC.sqrt_nonneg G).isSelfAdjoint
    have h2 : A.conjTranspose = A := h1
    rw [Matrix.IsSymm, ← Matrix.conjTranspose_eq_transpose_of_trivial, h2]
  have hR : ∀ i, (A * Qs i * A).IsSymm := by
    intro i
    rw [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_mul, hA.eq, (hQs i).eq, mul_assoc]
  have hval : ∀ σ : Equiv.Perm (Fin n), Matrix.trace (List.ofFn fun c : Fin n => Qs (σ c) * G).prod =
      cyclicTrace (fun i => A * Qs i * A) σ := by
    intro σ
    have h1 : (List.ofFn fun c : Fin n => Qs (σ c) * G) =
        (List.ofFn fun c : Fin n => Qs (σ c)).map fun q => q * G := by
      rw [List.map_ofFn]
      rfl
    rw [h1, trace_prod_mul_sq_eq A G hAA, List.map_ofFn]
    rfl
  simp only [hval]
  refine ⟨?_, ?_⟩
  · rw [hmap, jointCumulant_map (measurable_sqrtMap A) fun i => measurable_halfQuadraticForm (Qs i)]
    simp only [halfQuadraticForm_sqrtMap hA]
    rw [jointCumulant_halfQuadraticForms (isStandardGaussianFamily_pi (Fin N)) (fun i => A * Qs i * A) hR,
      orderedTraceSum_eq_cyclic hn (fun i => A * Qs i * A) hR]
  · haveI : IsProbabilityMeasure
        ((Measure.pi fun _ : Fin N => gaussianReal 0 1).map (sqrtMap A)) :=
      Measure.isProbabilityMeasure_map (measurable_sqrtMap A).aemeasurable
    have hpi : (Measure.pi fun _ : Fin 3 => multivariateGaussian (0 : EuclideanSpace ℝ (Fin N)) G) =
        (Measure.pi fun _ : Fin 3 => Measure.pi fun _ : Fin N => gaussianReal 0 1).map
          (fun W e => sqrtMap A (W e)) := by
      rw [hmap]
      exact (Measure.pi_map_pi fun _ => (measurable_sqrtMap A).aemeasurable).symm
    have hT : Measurable fun (W : Fin 3 → Fin N → ℝ) (e : Fin 3) => sqrtMap A (W e) :=
      measurable_pi_lambda _ fun e => (measurable_sqrtMap A).comp (measurable_pi_apply e)
    have hX : ∀ i, Measurable fun X : Fin 3 → EuclideanSpace ℝ (Fin N) =>
        ∑ e : Fin 3, (1 / 2 : ℝ) * ((fun a => X e a) ⬝ᵥ (Qs i).mulVec fun a => X e a) := by
      intro i
      exact Finset.measurable_sum _ fun e _ =>
        (measurable_halfQuadraticForm (Qs i)).comp (measurable_pi_apply e)
    rw [hpi, jointCumulant_map hT hX]
    simp only [halfQuadraticForm_sqrtMap hA, ← eval_threeCopies]
    rw [jointCumulant_halfQuadraticForms (isStandardGaussianFamily_threeCopies (Fin N))
        (fun i => threeCopies (A * Qs i * A)) fun i => threeCopies_isSymm (hR i),
      orderedTraceSum_eq_cyclic hn (fun i => threeCopies (A * Qs i * A))
        fun i => threeCopies_isSymm (hR i)]
    simp only [cyclicTrace_threeCopies, ← Finset.mul_sum]
    ring
end
end YangMills.Construction.MomentLaw
end
