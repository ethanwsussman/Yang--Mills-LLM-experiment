import YangMills.Construction.Continuum.MultilinearityAndInversionOfTheConnectedFunctions
import YangMills.Construction.Continuum.RecentringMapOnCombinationsOfFourSpace
import YangMills.Construction.Continuum.TheRecursionOfTheConnectedFunctionsIsTriangular
import YangMills.Construction.Continuum.ValueOfAFunctionalAtARecentredTuple
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CentredTupleValue
open TupleLists (ofList ofList_toList sepTupleEquivList toList)
open SetPartition
open TestSpaces
open SeparatedTuples (FormalSpan TupleFunctional)
variable {k : ℕ}
def nonSingletonSupport {I : Finset (Fin k)} (η : Partitions I) : Finset (Fin k) :=
  I.filter fun i => ({i} : Finset (Fin k)) ∉ η.parts
theorem part_disjoint_singleton_of_not_mem {C : Finset (Fin k)} (ρ : Partitions C)
    {B : Finset (Fin k)} (hB : B ∈ ρ.parts) {i : Fin k} (hi : i ∉ C) :
    Disjoint B ({i} : Finset (Fin k)) :=
  Finset.disjoint_singleton_right.2 fun hiB => hi (ρ.le hB hiB)
def extendBySingletons {I C : Finset (Fin k)} (hC : C ⊆ I) (ρ : Partitions C) : Partitions I where
  parts := ρ.parts ∪ (I \ C).image fun i => ({i} : Finset (Fin k))
  supIndep := by
    refine Finset.supIndep_iff_pairwiseDisjoint.2 fun b hb c hc hbc => ?_
    have hb' := Finset.mem_union.1 (Finset.mem_coe.1 hb)
    have hc' := Finset.mem_union.1 (Finset.mem_coe.1 hc)
    change Disjoint b c
    rcases hb' with hb' | hb' <;> rcases hc' with hc' | hc'
    · exact ρ.disjoint (Finset.mem_coe.2 hb') (Finset.mem_coe.2 hc') hbc
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc'
      exact part_disjoint_singleton_of_not_mem ρ hb' (Finset.mem_sdiff.1 hi).2
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hb'
      exact (part_disjoint_singleton_of_not_mem ρ hc' (Finset.mem_sdiff.1 hi).2).symm
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb'
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hc'
      exact Finset.disjoint_singleton.2 fun h => hbc (by rw [h])
  sup_parts := by
    rw [Finset.sup_eq_biUnion]
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_image, id]
    constructor
    · rintro ⟨B, hB | ⟨j, hj, rfl⟩, hi⟩
      · exact hC (ρ.le hB hi)
      · rw [Finset.mem_singleton.1 hi]
        exact (Finset.mem_sdiff.1 hj).1
    · intro hi
      by_cases hiC : i ∈ C
      · obtain ⟨B, hB, hiB⟩ := ρ.exists_mem hiC
        exact ⟨B, Or.inl hB, hiB⟩
      · exact ⟨{i}, Or.inr ⟨i, Finset.mem_sdiff.2 ⟨hi, hiC⟩, rfl⟩, Finset.mem_singleton_self i⟩
  bot_notMem := fun h => by
    rcases Finset.mem_union.1 h with h | h
    · exact ρ.bot_notMem h
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
      exact Finset.singleton_ne_empty i hi
theorem parts_extendBySingletons {I C : Finset (Fin k)} (hC : C ⊆ I) (ρ : Partitions C) :
    (extendBySingletons hC ρ).parts =
      ρ.parts ∪ (I \ C).image fun i => ({i} : Finset (Fin k)) :=
  rfl
theorem filter_two_le_parts_extendBySingletons {I C : Finset (Fin k)} (hC : C ⊆ I)
    {ρ : Partitions C} (hρ : ρ ∈ atLeastTwoPartitions C) :
    (extendBySingletons hC ρ).parts.filter (fun B => 2 ≤ B.card) = ρ.parts := by
  ext B
  rw [parts_extendBySingletons, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hB | hB, h2⟩
    · exact hB
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hB
      simp at h2
  · intro hB
    exact ⟨Or.inl hB, two_le_card_of_mem_atLeastTwoPartitions hρ hB⟩
theorem nonSingletonSupport_extendBySingletons {I C : Finset (Fin k)} (hC : C ⊆ I)
    {ρ : Partitions C} (hρ : ρ ∈ atLeastTwoPartitions C) :
    nonSingletonSupport (extendBySingletons hC ρ) = C := by
  refine Finset.ext fun i => ?_
  rw [nonSingletonSupport, Finset.mem_filter, parts_extendBySingletons]
  constructor
  · rintro ⟨hiI, h⟩
    by_contra hiC
    exact h (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_sdiff.2 ⟨hiI, hiC⟩)))
  · intro hiC
    refine ⟨hC hiC, fun h => ?_⟩
    rcases Finset.mem_union.1 h with h | h
    · have := two_le_card_of_mem_atLeastTwoPartitions hρ h
      simp at this
    · obtain ⟨j, hj, hji⟩ := Finset.mem_image.1 h
      rw [Finset.singleton_injective hji] at hj
      exact (Finset.mem_sdiff.1 hj).2 hiC
theorem eq_singleton_of_card_lt_two {B : Finset (Fin k)} {i : Fin k} (hi : i ∈ B)
    (h2 : ¬2 ≤ B.card) : B = {i} := by
  have hle : B.card ≤ 1 := by omega
  exact Finset.eq_singleton_iff_unique_mem.2 ⟨hi, fun j hj => Finset.card_le_one.1 hle j hj i hi⟩
def nonSingletonPart {I : Finset (Fin k)} (η : Partitions I) :
    Partitions (nonSingletonSupport η) where
  parts := η.parts.filter fun B => 2 ≤ B.card
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.2
    (η.disjoint.subset (Finset.coe_subset.2 (Finset.filter_subset _ _)))
  sup_parts := by
    rw [Finset.sup_eq_biUnion]
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_filter, id, nonSingletonSupport]
    constructor
    · rintro ⟨B, ⟨hB, h2⟩, hiB⟩
      refine ⟨η.le hB hiB, fun hi => ?_⟩
      have hBi : B = {i} := η.eq_of_mem_parts hB hi hiB (Finset.mem_singleton_self i)
      rw [hBi] at h2
      simp at h2
    · rintro ⟨hiI, hi⟩
      obtain ⟨B, hB, hiB⟩ := η.exists_mem hiI
      refine ⟨B, ⟨hB, ?_⟩, hiB⟩
      by_contra h2
      exact hi (eq_singleton_of_card_lt_two hiB h2 ▸ hB)
  bot_notMem := fun h => η.bot_notMem (Finset.mem_filter.1 h).1
theorem extendBySingletons_nonSingletonPart {I : Finset (Fin k)} (η : Partitions I)
    (h : nonSingletonSupport η ⊆ I) : extendBySingletons h (nonSingletonPart η) = η := by
  refine Finpartition.ext ?_
  ext B
  rw [parts_extendBySingletons, Finset.mem_union]
  constructor
  · rintro (hB | hB)
    · exact (Finset.mem_filter.1 hB).1
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hB
      obtain ⟨hiI, hi'⟩ := Finset.mem_sdiff.1 hi
      by_contra hn
      exact hi' (Finset.mem_filter.2 ⟨hiI, hn⟩)
  · intro hB
    by_cases h2 : 2 ≤ B.card
    · exact Or.inl (Finset.mem_filter.2 ⟨hB, h2⟩)
    · obtain ⟨i, hi⟩ := η.nonempty_of_mem_parts hB
      have hBi := eq_singleton_of_card_lt_two hi h2
      refine Or.inr (Finset.mem_image.2 ⟨i, Finset.mem_sdiff.2 ⟨η.le hB hi, fun hoff => ?_⟩,
        hBi.symm⟩)
      exact (Finset.mem_filter.1 hoff).2 (hBi ▸ hB)
theorem sum_partitions_eq_sum_powerset (I : Finset (Fin k)) (g : Finset (Fin k) → ℝ) :
    ∑ η : Partitions I, ∏ J ∈ η.parts, g J =
      ∑ C ∈ I.powerset, (∏ i ∈ I \ C, g {i}) *
        ∑ ρ ∈ atLeastTwoPartitions C, ∏ B ∈ ρ.parts, g B := by
  refine (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := I.powerset)
    (g := nonSingletonSupport)
    (fun η _ => Finset.mem_powerset.2 (Finset.filter_subset _ _)) _).symm.trans ?_
  refine Finset.sum_congr rfl fun C hC => ?_
  have hCI := Finset.mem_powerset.1 hC
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_bij (fun ρ _ => extendBySingletons hCI ρ) (fun ρ hρ => ?_)
    (fun ρ hρ ρ' hρ' h => ?_) (fun η hη => ?_) (fun ρ hρ => ?_)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, nonSingletonSupport_extendBySingletons hCI hρ⟩
  · refine Finpartition.ext ?_
    rw [← filter_two_le_parts_extendBySingletons hCI hρ,
      ← filter_two_le_parts_extendBySingletons hCI hρ', h]
  · have hA : nonSingletonSupport η = C := (Finset.mem_filter.1 hη).2
    subst hA
    refine ⟨nonSingletonPart η, ?_, extendBySingletons_nonSingletonPart η hCI⟩
    exact mem_atLeastTwoPartitions.2 fun J hJ => (Finset.mem_filter.1 hJ).2
  · have hdisj : Disjoint ρ.parts ((I \ C).image fun i => ({i} : Finset (Fin k))) := by
      refine Finset.disjoint_left.2 fun B hB hB' => ?_
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hB'
      have := two_le_card_of_mem_atLeastTwoPartitions hρ hB
      simp at this
    rw [parts_extendBySingletons, Finset.prod_union hdisj,
      Finset.prod_image fun i _ j _ h => Finset.singleton_injective h, mul_comm]
theorem sum_supersets_prod_neg (a : Fin k → ℝ) (C : Finset (Fin k)) :
    ∑ A ∈ Finset.univ.filter (C ⊆ ·), (∏ i ∈ Aᶜ, -a i) * ∏ i ∈ A \ C, a i =
      ∏ i ∈ Cᶜ, (a i + -a i) := by
  rw [Finset.prod_add]
  refine Finset.sum_nbij' (fun A => A \ C) (fun D => D ∪ C) (fun A _ => ?_) (fun D _ => ?_)
    (fun A hA => ?_) (fun D hD => ?_) (fun A hA => ?_)
  · exact Finset.mem_powerset.2 fun i hi => Finset.mem_compl.2 (Finset.mem_sdiff.1 hi).2
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.subset_union_right⟩
  · exact Finset.sdiff_union_of_subset (Finset.mem_filter.1 hA).2
  · have hD' := Finset.mem_powerset.1 hD
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact h
      · exact absurd h h'
    · exact fun h => ⟨Or.inl h, Finset.mem_compl.1 (hD' h)⟩
  · have hCA := (Finset.mem_filter.1 hA).2
    have hc : Cᶜ \ (A \ C) = Aᶜ := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_compl]
      constructor
      · rintro ⟨h, h'⟩ hiA
        exact h' ⟨hiA, h⟩
      · exact fun h => ⟨fun hiC => h (hCA hiC), fun h' => h h'.1⟩
    rw [hc, mul_comm]
theorem alternating_sum_eq_top (a : Fin k → ℝ) (g h : Finset (Fin k) → ℝ)
    (hg : ∀ I, g I = ∑ C ∈ I.powerset, (∏ i ∈ I \ C, a i) * h C) :
    ∑ A : Finset (Fin k), (∏ i ∈ Aᶜ, -a i) * g A = h Finset.univ := by
  calc ∑ A : Finset (Fin k), (∏ i ∈ Aᶜ, -a i) * g A
      = ∑ A : Finset (Fin k), ∑ C ∈ A.powerset,
          (∏ i ∈ Aᶜ, -a i) * ((∏ i ∈ A \ C, a i) * h C) :=
        Finset.sum_congr rfl fun A _ => by rw [hg A, Finset.mul_sum]
    _ = ∑ C : Finset (Fin k), ∑ A ∈ Finset.univ.filter (C ⊆ ·),
          (∏ i ∈ Aᶜ, -a i) * ((∏ i ∈ A \ C, a i) * h C) :=
        Finset.sum_comm' fun A C => by simp [Finset.mem_powerset]
    _ = ∑ C : Finset (Fin k), (∏ i ∈ Cᶜ, (a i + -a i)) * h C :=
        Finset.sum_congr rfl fun C _ => by
          rw [← sum_supersets_prod_neg, Finset.sum_mul]
          exact Finset.sum_congr rfl fun A _ => by ring
    _ = h Finset.univ := by
        rw [Finset.sum_eq_single Finset.univ (fun C _ hC => ?_) (fun h' => absurd (Finset.mem_univ _) h')]
        · simp
        · obtain ⟨i, hi⟩ : ∃ i, i ∉ C := by
            by_contra hn
            exact hC (Finset.eq_univ_of_forall fun i => by
              by_contra hi
              exact hn ⟨i, hi⟩)
          rw [Finset.prod_eq_zero (Finset.mem_compl.2 hi) (add_neg_cancel _), zero_mul]
theorem ofList_subtuple_toList (X : SepTupleOfCard k) (A : Finset (Fin k)) :
    ofList ((toList ⟨k, X⟩).subtuple (A.image fun i : Fin k => (i : ℕ) + 1)) =
      ⟨A.card, sepRestrict X A⟩ := by
  have h : (toList ⟨k, X⟩).subtuple (A.image fun i : Fin k => (i : ℕ) + 1) =
      toList ⟨A.card, sepRestrict X A⟩ :=
    Subtype.ext (Continuum.SeparatedFourTuples.sublistOn_ofFn X.1 A)
  rw [h, ofList_toList]
theorem centringCoeff_image_succ (s : SepTuple → ℝ) (X : SepTupleOfCard k)
    (A : Finset (Fin k)) :
    centringCoeff s (toList ⟨k, X⟩) (A.image fun i : Fin k => (i : ℕ) + 1) =
      ∏ i ∈ Aᶜ, ((-cumulantOne s (X.1 i) (X.2.1 i) : ℝ) : ℂ) := by
  have hlen : (toList ⟨k, X⟩).1.length = k := List.length_ofFn
  symm
  refine Finset.prod_bij (fun i _ => Fin.cast hlen.symm i) (fun i hi => ?_)
    (fun i _ j _ h => ?_) (fun l hl => ?_) (fun i _ => ?_)
  · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun h => ?_⟩
    exact Finset.mem_compl.1 hi
      ((Continuum.SeparatedFourTuples.mem_image_val_succ_iff A i).1 h)
  · exact Fin.cast_injective _ h
  · refine ⟨Fin.cast hlen l, ?_, rfl⟩
    have hl' := (Finset.mem_filter.1 hl).2
    refine Finset.mem_compl.2 fun hA => hl' ?_
    exact (Continuum.SeparatedFourTuples.mem_image_val_succ_iff A (Fin.cast hlen l)).2 hA
  · have h : (toList ⟨k, X⟩).1 = List.ofFn X.1 := rfl
    have he :=
      Continuum.SeparatedFourTuples.get_eq_of_eq_ofFn X.1 h (Fin.cast hlen.symm i) i rfl
    exact congrArg (fun t : ℝ => ((-t : ℝ) : ℂ))
      (Continuum.SeparatedFourTuples.cumulantOne_congr s he.symm _ _)
theorem cumulant_of_card_one (s : SepTuple → ℝ) {m : ℕ} (hm : m = 1)
    (Y : SepTupleOfCard m) (f : (Fin 4 → ℝ) → ℝ)
    (hf : f ∈ c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) (hY : ∀ j, Y.1 j = f) :
    cumulant s Y = cumulantOne s f hf := by
  subst hm
  exact congrArg (cumulant s) (Subtype.ext (funext hY))
theorem cumulant_sepRestrict_singleton (s : SepTuple → ℝ) (X : SepTupleOfCard k)
    (i : Fin k) :
    cumulant s (sepRestrict X {i}) = cumulantOne s (X.1 i) (X.2.1 i) := by
  refine cumulant_of_card_one s (Finset.card_singleton i) _ _ _ fun j => ?_
  have h : ({i} : Finset (Fin k)).orderEmbOfFin rfl j = i :=
    Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ rfl j)
  change X.1 (({i} : Finset (Fin k)).orderEmbOfFin rfl j) = X.1 i
  rw [h]
theorem value_sepRestrict (hTri : CumulantRecursionTriangular)
    (s : SepTuple → ℝ) (hs : IsMultilinearSepFunctional s) (X : SepTupleOfCard k)
    (I : Finset (Fin k)) :
    s ⟨I.card, sepRestrict X I⟩ = ∑ C ∈ I.powerset,
      (∏ i ∈ I \ C, cumulantOne s (X.1 i) (X.2.1 i)) *
        ∑ ρ ∈ atLeastTwoPartitions C, ∏ B ∈ ρ.parts,
          cumulant s (sepRestrict X B) := by
  rcases I.eq_empty_or_nonempty with rfl | hI
  · rw [sepRestrict_empty, hs.1, Finset.powerset_empty, Finset.sum_singleton,
      atLeastTwoPartitions_empty, Finset.sum_singleton, prod_parts_of_empty]
    simp
  · have hk : 1 ≤ k := by
      obtain ⟨i, -⟩ := hI
      exact i.pos
    have hc : ∀ J : Finset (Fin k), J.Nonempty →
        cumulantRec s J.card (sepRestrict X J) =
          cumulant s (sepRestrict X J) :=
      fun J hJ => ((hTri.2.2.2 s hs).1 J.card hJ.card_pos).2.1 _
    rw [(hTri.1 s k hk X).1 I hI]
    have h₂ : ∑ π : Partitions I, ∏ J ∈ π.parts,
          cumulantRec s J.card (sepRestrict X J) =
        ∑ π : Partitions I, ∏ J ∈ π.parts, cumulant s (sepRestrict X J) :=
      Finset.sum_congr rfl fun π _ =>
        Finset.prod_congr rfl fun J hJ => hc J (π.nonempty_of_mem_parts hJ)
    rw [h₂, sum_partitions_eq_sum_powerset I fun J => cumulant s (sepRestrict X J)]
    refine Finset.sum_congr rfl fun C _ => ?_
    congr 1
    exact Finset.prod_congr rfl fun i _ => cumulant_sepRestrict_singleton s X i
theorem value_centredTuple (hTri : CumulantRecursionTriangular)
    (s : SepTuple → ℝ) (hs : IsMultilinearSepFunctional s) (F : TupleFunctional)
    (hF : ∀ X, F X = s (ofList X)) (X : SepTupleOfCard k) :
    F.spanExtension (centredTuple s (toList ⟨k, X⟩)) =
      ((∑ π ∈ atLeastTwoPartitions (Finset.univ : Finset (Fin k)),
        ∏ B ∈ π.parts, cumulant s (sepRestrict X B) : ℝ) : ℂ) := by
  have hlen : (toList ⟨k, X⟩).size = k := List.length_ofFn
  have hsum := alternating_sum_eq_top (fun i => cumulantOne s (X.1 i) (X.2.1 i))
    (fun I => s ⟨I.card, sepRestrict X I⟩)
    (fun C => ∑ ρ ∈ atLeastTwoPartitions C, ∏ B ∈ ρ.parts,
      cumulant s (sepRestrict X B))
    (value_sepRestrict hTri s hs X)
  refine Eq.trans ?_ (congrArg (fun t : ℝ => (t : ℂ)) hsum)
  rw [centredTuple, map_sum, Complex.ofReal_sum]
  symm
  refine Finset.sum_bij (fun A _ => A.image fun i : Fin k => (i : ℕ) + 1)
    (fun A _ => ?_) (fun A _ A' _ h => ?_) (fun B hB => ?_) (fun A _ => ?_)
  · refine Finset.mem_powerset.2 fun n hn => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hn
    have := i.2
    simp only [Finset.mem_Icc, hlen]
    omega
  · ext i
    have h' : (A.image fun i : Fin k => (i : ℕ) + 1) = A'.image fun i : Fin k => (i : ℕ) + 1 := h
    rw [← Continuum.SeparatedFourTuples.mem_image_val_succ_iff A i,
      ← Continuum.SeparatedFourTuples.mem_image_val_succ_iff A' i, h']
  · refine ⟨Finset.univ.filter fun i : Fin k => (i : ℕ) + 1 ∈ B, Finset.mem_univ _, ?_⟩
    ext n
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hn
      have hI := Finset.mem_Icc.1 (Finset.mem_powerset.1 hB hn)
      rw [hlen] at hI
      exact ⟨⟨n - 1, by omega⟩, by simpa [Nat.sub_add_cancel hI.1] using hn,
        by simp [Nat.sub_add_cancel hI.1]⟩
  · have hval : F.spanExtension (SeparatedTuples.basisVec
        ((toList ⟨k, X⟩).subtuple (A.image fun i : Fin k => (i : ℕ) + 1))) =
        (s ⟨A.card, sepRestrict X A⟩ : ℂ) := by
      simp only [TupleFunctional.spanExtension, SeparatedTuples.linearExtend_basisVec]
      rw [hF, ofList_subtuple_toList]
    rw [map_smul, hval, smul_eq_mul, centringCoeff_image_succ, Complex.ofReal_mul,
      Complex.ofReal_prod]
theorem centredValueFormula_of_cumulants (hInv : CumulantMultilinearInversion)
    (hTri : CumulantRecursionTriangular) :
    centredValueFormula := by
  intro s hs F hF
  have hval := fun (n : ℕ) (X : SepTupleOfCard n) => value_centredTuple hTri s hs F hF X
  refine ⟨fun Z => ?_, hval, centredOfCumulants_nil _, fun f hf => centredOfCumulants_single _ _,
    (hInv.1 s hs fun _ _ Y => cumulant s Y).2.2.2.1⟩
  have h : (centredPartFunctional s).spanExtension = F.spanExtension ∘ₗ centring s := by
    refine Finsupp.lhom_ext' fun Y => LinearMap.ext_ring ?_
    obtain ⟨⟨n, X⟩, rfl⟩ := sepTupleEquivList.surjective Y
    change (centredPartFunctional s).spanExtension (SeparatedTuples.basisVec (toList ⟨n, X⟩)) =
      F.spanExtension (centring s (SeparatedTuples.basisVec (toList ⟨n, X⟩)))
    rw [centredPartFunctional_spanExtension_basisVec, centring_basisVec, hval,
      centredPart_eq_sum_atLeastTwoPartitions]
  exact LinearMap.congr_fun h Z
end YangMills.Construction.CentredTupleValue
end
