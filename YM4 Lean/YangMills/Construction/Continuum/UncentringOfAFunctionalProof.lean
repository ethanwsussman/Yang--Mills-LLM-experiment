import YangMills.Construction.Continuum.MultilinearityAndInversionOfTheConnectedFunctions
import YangMills.Construction.Continuum.UncentringOfAFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TestSpaces.Uncentring
open SetPartition
variable {n : ℕ}
def singletonSupport (η : Partitions (Finset.univ : Finset (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter fun i => ({i} : Finset (Fin n)) ∈ η.parts
theorem isPartition_addSingletons (A : Finset (Fin n)) (ρ : Partitions Aᶜ) :
    ClusterExpansion.SymGraph.IsPartition
      (ρ.parts ∪ A.image fun i => ({i} : Finset (Fin n))) := by
  have hdisj : ∀ B ∈ ρ.parts, ∀ i ∈ A, Disjoint B ({i} : Finset (Fin n)) := by
    intro B hB i hi
    rw [Finset.disjoint_singleton_right]
    intro hiB
    exact Finset.mem_compl.1 (ρ.le hB hiB) hi
  refine ⟨fun b hb => ?_, fun b hb c hc hbc => ?_, ?_⟩
  · rcases Finset.mem_union.1 hb with hb | hb
    · exact ρ.nonempty_of_mem_parts hb
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb
      exact Finset.singleton_nonempty i
  · have hb' := Finset.mem_union.1 (Finset.mem_coe.1 hb)
    have hc' := Finset.mem_union.1 (Finset.mem_coe.1 hc)
    change Disjoint b c
    rcases hb' with hb' | hb' <;> rcases hc' with hc' | hc'
    · exact ρ.disjoint (Finset.mem_coe.2 hb') (Finset.mem_coe.2 hc') hbc
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc'
      exact hdisj b hb' i hi
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hb'
      exact (hdisj c hc' i hi).symm
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb'
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hc'
      exact Finset.disjoint_singleton.2 fun h => hbc (by rw [h])
  · have hcover : (ρ.parts ∪ A.image fun i => ({i} : Finset (Fin n))).biUnion id =
        Finset.univ := by
      refine Finset.eq_univ_of_forall fun i => ?_
      rw [Finset.mem_biUnion]
      by_cases hi : i ∈ A
      · exact ⟨{i}, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi),
          Finset.mem_singleton_self i⟩
      · obtain ⟨B, hB, hiB⟩ := ρ.exists_mem (Finset.mem_compl.2 hi)
        exact ⟨B, Finset.mem_union_left _ hB, hiB⟩
    convert hcover
def addSingletons (A : Finset (Fin n)) (ρ : Partitions Aᶜ) :
    Partitions (Finset.univ : Finset (Fin n)) :=
  finpartitionOfIsPartition (isPartition_addSingletons A ρ)
theorem parts_addSingletons (A : Finset (Fin n)) (ρ : Partitions Aᶜ) :
    (addSingletons A ρ).parts = ρ.parts ∪ A.image fun i => ({i} : Finset (Fin n)) :=
  rfl
theorem filter_parts_addSingletons (A : Finset (Fin n)) {ρ : Partitions Aᶜ}
    (hρ : ρ ∈ atLeastTwoPartitions Aᶜ) :
    (addSingletons A ρ).parts.filter (fun B => 2 ≤ B.card) = ρ.parts := by
  ext B
  rw [parts_addSingletons, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hB | hB, h2⟩
    · exact hB
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hB
      simp at h2
  · intro hB
    exact ⟨Or.inl hB, two_le_card_of_mem_atLeastTwoPartitions hρ hB⟩
theorem singletonSupport_addSingletons (A : Finset (Fin n)) {ρ : Partitions Aᶜ}
    (hρ : ρ ∈ atLeastTwoPartitions Aᶜ) :
    singletonSupport (addSingletons A ρ) = A := by
  ext i
  simp only [singletonSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    parts_addSingletons, Finset.mem_union, Finset.mem_image, Finset.singleton_inj,
    exists_eq_right]
  constructor
  · rintro (h | h)
    · have := two_le_card_of_mem_atLeastTwoPartitions hρ h
      simp at this
    · exact h
  · exact Or.inr
def nonSingletonPart (η : Partitions (Finset.univ : Finset (Fin n))) :
    Partitions (singletonSupport η)ᶜ where
  parts := η.parts.filter fun B => 2 ≤ B.card
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.2
    (η.disjoint.subset (Finset.coe_subset.2 (Finset.filter_subset _ _)))
  sup_parts := by
    rw [Finset.sup_eq_biUnion]
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_filter, id, Finset.mem_compl,
      singletonSupport, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨B, ⟨hB, h2⟩, hiB⟩ hi
      have hBi : B = {i} := η.eq_of_mem_parts hB hi hiB (Finset.mem_singleton_self i)
      rw [hBi] at h2
      simp at h2
    · intro hi
      obtain ⟨B, hB, hiB⟩ := η.exists_mem (Finset.mem_univ i)
      refine ⟨B, ⟨hB, ?_⟩, hiB⟩
      by_contra h2
      have hle : B.card ≤ 1 := by omega
      have hBi : B = {i} := by
        refine Finset.eq_singleton_iff_unique_mem.2 ⟨hiB, fun j hj => ?_⟩
        exact Finset.card_le_one.1 hle j hj i hiB
      exact hi (hBi ▸ hB)
  bot_notMem := fun h => η.bot_notMem (Finset.mem_filter.1 h).1
theorem addSingletons_nonSingletonPart (η : Partitions (Finset.univ : Finset (Fin n))) :
    addSingletons (singletonSupport η) (nonSingletonPart η) = η := by
  refine Finpartition.ext ?_
  ext B
  rw [parts_addSingletons, Finset.mem_union]
  constructor
  · rintro (hB | hB)
    · exact (Finset.mem_filter.1 hB).1
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hB
      exact (Finset.mem_filter.1 hi).2
  · intro hB
    by_cases h2 : 2 ≤ B.card
    · exact Or.inl (Finset.mem_filter.2 ⟨hB, h2⟩)
    · obtain ⟨i, hi⟩ := η.nonempty_of_mem_parts hB
      have hle : B.card ≤ 1 := by omega
      have hBi : B = {i} := by
        refine Finset.eq_singleton_iff_unique_mem.2 ⟨hi, fun j hj => ?_⟩
        exact Finset.card_le_one.1 hle j hj i hi
      refine Or.inr (Finset.mem_image.2 ⟨i, ?_, hBi.symm⟩)
      exact Finset.mem_filter.2 ⟨Finset.mem_univ i, hBi ▸ hB⟩
theorem sum_partitions_prod_eq_sum_subsets (g : Finset (Fin n) → ℝ) :
    ∑ η : Partitions (Finset.univ : Finset (Fin n)), ∏ J ∈ η.parts, g J =
      ∑ A : Finset (Fin n), (∏ i ∈ A, g {i}) *
        ∑ ρ ∈ atLeastTwoPartitions Aᶜ, ∏ C ∈ ρ.parts, g C := by
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := singletonSupport)]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_bij (fun ρ _ => addSingletons A ρ) (fun ρ hρ => ?_)
    (fun ρ hρ ρ' hρ' h => ?_) (fun η hη => ?_) (fun ρ hρ => ?_)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, singletonSupport_addSingletons A hρ⟩
  · refine Finpartition.ext ?_
    rw [← filter_parts_addSingletons A hρ, ← filter_parts_addSingletons A hρ', h]
  · have hA : singletonSupport η = A := (Finset.mem_filter.1 hη).2
    subst hA
    refine ⟨nonSingletonPart η, ?_, addSingletons_nonSingletonPart η⟩
    exact mem_atLeastTwoPartitions.2 fun J hJ => (Finset.mem_filter.1 hJ).2
  · have hdisj : Disjoint ρ.parts (A.image fun i => ({i} : Finset (Fin n))) := by
      refine Finset.disjoint_left.2 fun B hB hB' => ?_
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hB'
      have := two_le_card_of_mem_atLeastTwoPartitions hρ hB
      simp at this
    rw [parts_addSingletons, Finset.prod_union hdisj,
      Finset.prod_image fun i _ j _ h => Finset.singleton_injective h, mul_comm]
theorem cumulant_of_card_eq_one {σ : SepTuple → ℝ} {c : ℝ}
    (h₁ : ∀ X : SepTupleOfCard 1, cumulant σ X = c * ∫ u, X.1 0 u) {m : ℕ} (hm : m = 1)
    (Y : SepTupleOfCard m) (f : (Fin 4 → ℝ) → ℝ) (hY : ∀ k, Y.1 k = f) :
    cumulant σ Y = c * ∫ u, f u := by
  subst hm
  rw [h₁ Y, hY 0]
theorem sepRestrict_singleton_apply (X : SepTupleOfCard n) (i : Fin n)
    (k : Fin ({i} : Finset (Fin n)).card) : (sepRestrict X {i}).1 k = X.1 i := by
  have h : ({i} : Finset (Fin n)).orderEmbOfFin rfl k = i :=
    Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ rfl k)
  change X.1 (({i} : Finset (Fin n)).orderEmbOfFin rfl k) = X.1 i
  rw [h]
theorem uncentringFormula_of_inversion (hInv : CumulantMultilinearInversion) :
    UncentringFormula := by
  intro σ c hσ h₁
  obtain ⟨hform, -, -, -, hinv⟩ := hInv.1 σ hσ fun _ _ Y => cumulant σ Y
  refine ⟨fun n hn X => ?_, centredOfCumulants_nil _, fun X => centredOfCumulants_single _ X⟩
  have hcentred : ∀ A : Finset (Fin n), centredPart σ ⟨Aᶜ.card, sepRestrict X Aᶜ⟩ =
      ∑ ρ ∈ atLeastTwoPartitions Aᶜ, ∏ C ∈ ρ.parts, cumulant σ (sepRestrict X C) := by
    intro A
    refine ((hform n hn X Aᶜ).2).trans ?_
    refine Eq.trans ?_ (Finset.sum_attach _ fun ρ : Partitions Aᶜ => ∏ C ∈ ρ.parts,
      cumulant σ (sepRestrict X C))
    refine Finset.sum_congr rfl fun ρ _ => ?_
    exact Finset.prod_attach ρ.1.parts fun C => cumulant σ (sepRestrict X C)
  have hsingle : ∀ i : Fin n, cumulant σ (sepRestrict X {i}) = c * ∫ u, X.1 i u :=
    fun i => cumulant_of_card_eq_one h₁ (Finset.card_singleton i) _ _
      (sepRestrict_singleton_apply X i)
  have hmain := sum_partitions_prod_eq_sum_subsets fun J => cumulant σ (sepRestrict X J)
  rw [hinv n hn X |>.trans hmain]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [hcentred A]
  congr 1
  exact Finset.prod_congr rfl fun i _ => hsingle i
end YangMills.Construction.TestSpaces.Uncentring
