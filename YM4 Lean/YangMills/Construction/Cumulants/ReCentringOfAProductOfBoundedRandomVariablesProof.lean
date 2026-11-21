import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMoments
import YangMills.Construction.Cumulants.ReCentringOfAProductOfBoundedRandomVariables
import YangMills.Construction.Cumulants.SetOfThePartitionsOfAFiniteSet
import YangMills.Construction.Cumulants.SmallestPartitionsBlocksAndTransportByABijection
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants.ProductRecentering
open YangMills.Construction.Probability (IsBoundedRealRV complexExpectation)
open YangMills.Construction.SetPartition (Partitions PartitionsFin atLeastTwoPartitions
  singletonFree blockImage partitionImage mem_blockImage mem_partitionImage
  mem_atLeastTwoPartitions atLeastTwoPartitions_univ exists_partition_parts_eq_iff
  two_le_card_of_mem_atLeastTwoPartitions)
open YangMills.Construction.SetPartition.Elementary (TransportUnderEquiv)
theorem sum_singletonFree_transport (hTr : TransportUnderEquiv) {m k : ℕ} {A : Finset (Fin k)}
    (σ : (Finset.univ : Finset (Fin m)) ≃ A) {R : Type*} [CommSemiring R]
    (F : Finset (Fin k) → R) :
    ∑ π ∈ singletonFree m, ∏ J ∈ π.parts, F (blockImage σ J) =
      ∑ π' ∈ atLeastTwoPartitions A, ∏ J ∈ π'.parts, F J := by
  obtain ⟨hbij, hblocks⟩ := hTr (Fin m) (Fin k) Finset.univ A σ
  have hex : ∀ π : PartitionsFin m, ∃ π' : Partitions A,
      π'.parts = partitionImage σ π := fun π => hbij.mapsTo (Set.mem_univ π)
  choose T hTp using hex
  rw [← atLeastTwoPartitions_univ]
  refine Finset.sum_bij (fun π _ => T π) ?_ ?_ ?_ ?_
  · intro π hπ
    refine mem_atLeastTwoPartitions.mpr fun J hJ => ?_
    rw [hTp, mem_partitionImage] at hJ
    obtain ⟨J₀, hJ₀, rfl⟩ := hJ
    rw [(hblocks π).2.1 J₀ hJ₀]
    exact mem_atLeastTwoPartitions.mp hπ J₀ hJ₀
  · intro π₁ _ π₂ _ h
    exact hbij.injOn (Set.mem_univ _) (Set.mem_univ _) (by rw [← hTp, ← hTp, h])
  · intro π' hπ'
    obtain ⟨π, -, hπ⟩ := hbij.surjOn
      (⟨π', rfl⟩ : π'.parts ∈ SetPartition.partitionSets A)
    have hT' : T π = π' := Finpartition.ext (by rw [hTp, hπ])
    refine ⟨π, mem_atLeastTwoPartitions.mpr fun J hJ => ?_, hT'⟩
    have hmem : blockImage σ J ∈ π'.parts := by
      rw [← hπ]
      exact (mem_partitionImage σ π _).mpr ⟨J, hJ, rfl⟩
    rw [← (hblocks π).2.1 J hJ]
    exact mem_atLeastTwoPartitions.mp hπ' _ hmem
  · intro π _
    rw [hTp, partitionImage, Finset.prod_image]
    exact fun a ha b hb h => (hblocks π).1.injOn ha hb h
def increasingEquiv {m k : ℕ} (A : Finset (Fin k)) (h : A.card = m) :
    (Finset.univ : Finset (Fin m)) ≃ A :=
  (Equiv.subtypeUnivEquiv Finset.mem_univ).trans (A.orderIsoOfFin h).toEquiv
theorem blockImage_increasingEquiv {m k : ℕ} (A : Finset (Fin k)) (h : A.card = m)
    (J : Finset (Fin m)) :
    blockImage (increasingEquiv A h) J = J.image (A.orderEmbOfFin h) := by
  ext y
  simp only [mem_blockImage, Finset.mem_image]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, by simp [increasingEquiv]⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, Finset.mem_univ l⟩, hl, by simp [increasingEquiv]⟩
theorem mixedCumulant_congr {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) {p p' : ℕ}
    (hp : p = p') (f : Fin p → Ω → ℝ) (g : Fin p' → Ω → ℝ)
    (h : ∀ a, f a = g (Fin.cast hp a)) : mixedCumulant ν f = mixedCumulant ν g := by
  subst hp
  have hfg : f = g := funext fun a => by simpa using h a
  rw [hfg]
theorem finsetCumulant_comp_strictMono {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    {k m : ℕ} (X : Fin k → Ω → ℝ) (e : Fin m → Fin k) (he : StrictMono e) (J : Finset (Fin m)) :
    finsetCumulant ν (fun l => X (e l)) J = finsetCumulant ν X (J.image e) := by
  have hc : (J.image e).card = J.card := Finset.card_image_of_injective _ he.injective
  have hf : (fun b : Fin (J.image e).card => e (J.orderEmbOfFin rfl (Fin.cast hc b))) =
      (J.image e).orderEmbOfFin rfl :=
    Finset.orderEmbOfFin_unique rfl
      (fun b => Finset.mem_image_of_mem e (Finset.orderEmbOfFin_mem _ _ _))
      (fun a b hab => he ((J.orderEmbOfFin rfl).strictMono (show (a : ℕ) < (b : ℕ) from hab)))
  refine mixedCumulant_congr ν hc.symm _ _ fun a => ?_
  have h := congrFun hf (Fin.cast hc.symm a)
  simp only [restrictTuple]
  rw [← h]
  simp
theorem prod_eq_prod_orderEmbOfFin {k : ℕ} {R : Type*} [CommMonoid R] (A : Finset (Fin k))
    (g : Fin k → R) : ∏ i ∈ A, g i = ∏ l : Fin A.card, g (A.orderEmbOfFin rfl l) := by
  rw [← Finset.prod_coe_sort A g, ← Equiv.prod_comp (A.orderIsoOfFin rfl).toEquiv]
  simp
theorem isBoundedRealRV_prod {Ω ι : Type*} [MeasurableSpace Ω] (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i, IsBoundedRealRV (f i)) :
    IsBoundedRealRV fun ω => ∏ i ∈ s, f i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, 1, by simp⟩
  | insert a s ha ih =>
    obtain ⟨C₁, h₁⟩ := (hf a).bounded
    obtain ⟨C₂, h₂⟩ := ih.bounded
    refine ⟨?_, C₁ * C₂, fun ω => ?_⟩
    · simp only [Finset.prod_insert ha]
      exact (hf a).measurable.mul ih.measurable
    · rw [Finset.prod_insert ha, abs_mul]
      exact mul_le_mul (h₁ ω) (h₂ ω) (abs_nonneg _) ((abs_nonneg _).trans (h₁ ω))
theorem centredMoment_eq_sum_atLeastTwoPartitions (hC : CumulantMomentRelations)
    (hTr : TransportUnderEquiv) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {k : ℕ} (X : Fin k → Ω → ℝ)
    (hX : ∀ i, IsBoundedRealRV (X i)) (A : Finset (Fin k)) :
    ((∫ ω, ∏ i ∈ A, (X i ω - ∫ ω', X i ω' ∂μ) ∂μ : ℝ) : ℂ) =
      ∑ π ∈ atLeastTwoPartitions A, ∏ J ∈ π.parts, finsetCumulant μ X J := by
  obtain ⟨-, -, -, -, -, hCentred, -⟩ :=
    hC Ω μ A.card (fun l => X (A.orderEmbOfFin rfl l)) (fun l => hX _)
  have hR : ∑ π ∈ singletonFree A.card, ∏ J ∈ π.parts,
        finsetCumulant μ X (blockImage (increasingEquiv A rfl) J) =
      ∑ π ∈ singletonFree A.card, ∏ J ∈ π.parts,
        finsetCumulant μ (fun l => X (A.orderEmbOfFin rfl l)) J :=
    Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ => by
      rw [blockImage_increasingEquiv,
        finsetCumulant_comp_strictMono μ X _ (A.orderEmbOfFin rfl).strictMono]
  rw [← sum_singletonFree_transport hTr (increasingEquiv A rfl) (finsetCumulant μ X), hR,
    ← hCentred, complexExpectation, ← integral_complex_ofReal]
  refine congrArg (fun f : Ω → ℂ => ∫ ω, f ω ∂μ) (funext fun ω => ?_)
  have hexp : ∀ i, (complexExpectation μ fun ω' => (X i ω' : ℂ)) =
      ((∫ ω', X i ω' ∂μ : ℝ) : ℂ) :=
    fun i => integral_complex_ofReal
  simp only [hexp]
  rw [prod_eq_prod_orderEmbOfFin A]
  push_cast
  rfl
theorem realExpect_prod_sub_eq_sum {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {k : ℕ} (X : Fin k → Ω → ℝ) (c : Fin k → ℝ)
    (hX : ∀ i, IsBoundedRealRV (X i)) :
    realExpect μ (fun ω => ∏ i, (X i ω - c i)) =
      ∑ I : Finset (Fin k), (∏ i ∈ I, centeredMean μ X c i) *
        ∫ ω, ∏ i ∈ Finset.univ \ I, (X i ω - ∫ ω', X i ω' ∂μ) ∂μ := by
  have hp : (fun ω => ∏ i, (X i ω - c i)) = fun ω => ∑ I : Finset (Fin k),
      (∏ i ∈ I, centeredMean μ X c i) * ∏ i ∈ Finset.univ \ I, (X i ω - ∫ ω', X i ω' ∂μ) := by
    funext ω
    have h := Finset.prod_add (fun i => centeredMean μ X c i)
      (fun i => X i ω - ∫ ω', X i ω' ∂μ) Finset.univ
    rw [Finset.powerset_univ] at h
    rw [← h]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [centeredMean, realExpect]
    ring
  have hb : ∀ i, IsBoundedRealRV fun ω => X i ω - ∫ ω', X i ω' ∂μ := by
    intro i
    obtain ⟨C, hCb⟩ := (hX i).bounded
    exact ⟨(hX i).measurable.sub_const _, C + |∫ ω', X i ω' ∂μ|,
      fun ω => (abs_sub _ _).trans (add_le_add (hCb ω) le_rfl)⟩
  have hint : ∀ I : Finset (Fin k), Integrable
      (fun ω => ∏ i ∈ Finset.univ \ I, (X i ω - ∫ ω', X i ω' ∂μ)) μ := by
    intro I
    have h := isBoundedRealRV_prod (Finset.univ \ I) (fun i ω => X i ω - ∫ ω', X i ω' ∂μ) hb
    obtain ⟨C, hCb⟩ := h.bounded
    exact Integrable.of_bound h.measurable.aestronglyMeasurable C
      (Filter.Eventually.of_forall hCb)
  rw [realExpect, hp, integral_finsetSum _ fun I _ => (hint I).const_mul _]
  exact Finset.sum_congr rfl fun I _ => integral_const_mul _ _
def singletonSet {k : ℕ} (π' : PartitionsFin k) : Finset (Fin k) :=
  Finset.univ.filter fun i => ({i} : Finset (Fin k)) ∈ π'.parts
theorem exists_partition_union_singletons {k : ℕ} (I : Finset (Fin k))
    (π : Partitions (Finset.univ \ I)) :
    ∃ π' : PartitionsFin k, π'.parts = π.parts ∪ I.image fun i => {i} := by
  have hd : ∀ J ∈ π.parts, ∀ i ∈ I, Disjoint J ({i} : Finset (Fin k)) := by
    intro J hJ i hi
    rw [Finset.disjoint_singleton_right]
    intro hiJ
    exact (Finset.mem_sdiff.mp (π.le hJ hiJ)).2 hi
  refine exists_partition_parts_eq_iff.mpr ⟨?_, ?_, ?_⟩
  · intro J hJ
    rcases Finset.mem_union.mp hJ with h | h
    · exact ⟨π.nonempty_of_mem_parts h, Finset.subset_univ J⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h
      exact ⟨Finset.singleton_nonempty i, Finset.subset_univ _⟩
  · intro J₁ h₁ J₂ h₂ hne
    show Disjoint J₁ J₂
    rcases Finset.mem_union.mp (Finset.mem_coe.mp h₁) with h₁ | h₁ <;>
      rcases Finset.mem_union.mp (Finset.mem_coe.mp h₂) with h₂ | h₂
    · exact π.disjoint h₁ h₂ hne
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h₂
      exact hd _ h₁ i hi
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h₁
      exact (hd _ h₂ i hi).symm
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h₁
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp h₂
      rw [Finset.disjoint_singleton]
      exact fun h => hne (by rw [h])
  · ext i
    simp only [Finset.mem_biUnion, id, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      iff_true]
    by_cases hi : i ∈ I
    · exact ⟨{i}, Or.inr ⟨i, hi, rfl⟩, Finset.mem_singleton_self i⟩
    · obtain ⟨J, hJ, hiJ⟩ := π.exists_mem (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)
      exact ⟨J, Or.inl hJ, hiJ⟩
theorem exists_partition_of_large_blocks {k : ℕ} (π' : PartitionsFin k) (I : Finset (Fin k))
    (hI : ∀ i, ({i} : Finset (Fin k)) ∈ π'.parts ↔ i ∈ I) :
    ∃ π : Partitions (Finset.univ \ I), π.parts = π'.parts.filter fun J => 2 ≤ J.card := by
  have hnot : ∀ J ∈ π'.parts, 2 ≤ J.card → ∀ i ∈ J, i ∉ I := by
    intro J hp hc i hi hiI
    have hJ : J = {i} :=
      π'.eq_of_mem_parts hp ((hI i).mpr hiI) hi (Finset.mem_singleton_self i)
    rw [hJ] at hc
    simp at hc
  refine exists_partition_parts_eq_iff.mpr ⟨?_, ?_, ?_⟩
  · intro J hJ
    obtain ⟨hp, hc⟩ := Finset.mem_filter.mp hJ
    exact ⟨π'.nonempty_of_mem_parts hp, fun i hi =>
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hnot J hp hc i hi⟩⟩
  · exact π'.disjoint.subset (Finset.coe_subset.mpr (Finset.filter_subset _ _))
  · ext i
    simp only [Finset.mem_biUnion, id, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨J, ⟨hp, hc⟩, hi⟩
      exact hnot J hp hc i hi
    · intro hiI
      obtain ⟨J, hJ, hi⟩ := π'.exists_mem (Finset.mem_univ i)
      refine ⟨J, ⟨hJ, ?_⟩, hi⟩
      by_contra hc
      have h1 : J.card = 1 := by
        have := (π'.nonempty_of_mem_parts hJ).card_pos
        omega
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h1
      rw [Finset.mem_singleton] at hi
      subst hi
      exact hiI ((hI _).mp hJ)
theorem sum_singletons_mul_sum_atLeastTwoPartitions {k : ℕ} {R : Type*} [CommSemiring R]
    (κ : Finset (Fin k) → R) :
    ∑ I : Finset (Fin k), (∏ i ∈ I, κ {i}) *
        ∑ π ∈ atLeastTwoPartitions (Finset.univ \ I), ∏ J ∈ π.parts, κ J =
      ∑ π' : PartitionsFin k, ∏ J ∈ π'.parts, κ J := by
  rw [← Finset.sum_fiberwise Finset.univ singletonSet]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.mul_sum]
  choose T hT using exists_partition_union_singletons I
  refine Finset.sum_bij (fun π _ => T π) ?_ ?_ ?_ ?_
  · intro π hπ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    ext i
    simp only [singletonSet, Finset.mem_filter, Finset.mem_univ, true_and, hT]
    constructor
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · have := two_le_card_of_mem_atLeastTwoPartitions hπ h
        simp at this
      · obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
        rwa [← Finset.singleton_injective hji]
    · exact fun h => Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
  · intro π₁ h₁ π₂ h₂ h
    have hf : ∀ π (_ : π ∈ atLeastTwoPartitions (Finset.univ \ I)),
        (T π).parts.filter (fun J => 2 ≤ J.card) = π.parts := by
      intro π hπ
      ext J
      simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨h | ⟨i, -, rfl⟩, hc⟩
        · exact h
        · simp at hc
      · exact fun h => ⟨Or.inl h, two_le_card_of_mem_atLeastTwoPartitions hπ h⟩
    exact Finpartition.ext (by rw [← hf π₁ h₁, ← hf π₂ h₂, h])
  · intro π' hπ'
    have hI : ∀ i, ({i} : Finset (Fin k)) ∈ π'.parts ↔ i ∈ I := by
      intro i
      rw [← (Finset.mem_filter.mp hπ').2]
      simp [singletonSet]
    obtain ⟨π, hπ⟩ := exists_partition_of_large_blocks π' I hI
    refine ⟨π, mem_atLeastTwoPartitions.mpr fun J hJ => ?_, Finpartition.ext ?_⟩
    · rw [hπ] at hJ
      exact (Finset.mem_filter.mp hJ).2
    · rw [hT, hπ]
      ext J
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro (⟨h, -⟩ | ⟨i, hi, rfl⟩)
        · exact h
        · exact (hI i).mpr hi
      · intro h
        by_cases hc : 2 ≤ J.card
        · exact Or.inl ⟨h, hc⟩
        · have h1 : J.card = 1 := by
            have := (π'.nonempty_of_mem_parts h).card_pos
            omega
          obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
          exact Or.inr ⟨i, (hI i).mp h, rfl⟩
  · intro π hπ
    have hdisj : Disjoint π.parts (I.image fun i => ({i} : Finset (Fin k))) := by
      refine Finset.disjoint_left.mpr fun J hJ hJ' => ?_
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hJ'
      have := two_le_card_of_mem_atLeastTwoPartitions hπ hJ
      simp at this
    rw [hT, Finset.prod_union hdisj,
      Finset.prod_image fun a _ b _ h => Finset.singleton_injective h, mul_comm]
theorem prod_parts_prod {k : ℕ} {A : Finset (Fin k)} (π : Partitions A) (b : Fin k → ℝ) :
    ∏ J ∈ π.parts, ∏ i ∈ J, b i = ∏ i ∈ A, b i := by
  have h := Finset.prod_biUnion (f := b) π.disjoint
  rw [← Finset.sup_eq_biUnion, π.sup_parts] at h
  exact h.symm
theorem productRecenteringExpansion_holds (hC : CumulantMomentRelations)
    (hS : SetPartition.Elementary.BasicFacts) :
    ProductRecenteringExpansion := by
  have hTr : TransportUnderEquiv := hS.2.2.1
  intro Ω _ μ _ k _ X c hX
  have hfirst : (realExpect μ (fun ω => ∏ i, (X i ω - c i)) : ℂ) =
      ∑ I : Finset (Fin k), (∏ i ∈ I, (centeredMean μ X c i : ℂ)) *
        ∑ π ∈ atLeastTwoPartitions (Finset.univ \ I),
          ∏ J ∈ π.parts, recenteredCumulant μ X c J := by
    rw [realExpect_prod_sub_eq_sum μ X c hX, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Complex.ofReal_mul, Complex.ofReal_prod,
      centredMoment_eq_sum_atLeastTwoPartitions hC hTr μ X hX]
    refine congrArg _ (Finset.sum_congr rfl fun π hπ => Finset.prod_congr rfl fun J hJ => ?_)
    exact (recenteredCumulant_of_two_le_card μ X c
      (two_le_card_of_mem_atLeastTwoPartitions hπ hJ)).symm
  have hsecond := sum_singletons_mul_sum_atLeastTwoPartitions (recenteredCumulant μ X c)
  simp only [recenteredCumulant_singleton] at hsecond
  refine ⟨⟨hfirst, hsecond⟩, ?_⟩
  intro D b _ _ hδ hκ
  have habs : |realExpect μ fun ω => ∏ i, (X i ω - c i)| =
      ‖(realExpect μ (fun ω => ∏ i, (X i ω - c i)) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [habs, hfirst, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  have hprod : ‖∏ i ∈ I, (centeredMean μ X c i : ℂ)‖ ≤ D 1 ^ I.card * ∏ i ∈ I, b i := by
    rw [norm_prod]
    calc ∏ i ∈ I, ‖(centeredMean μ X c i : ℂ)‖ ≤ ∏ i ∈ I, (D 1 * b i) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => by
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact hδ i
      _ = D 1 ^ I.card * ∏ i ∈ I, b i := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hsum : ‖∑ π ∈ atLeastTwoPartitions (Finset.univ \ I),
        ∏ J ∈ π.parts, recenteredCumulant μ X c J‖ ≤
      (∑ π ∈ atLeastTwoPartitions (Finset.univ \ I), ∏ J ∈ π.parts, D J.card) *
        ∏ i ∈ Finset.univ \ I, b i := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun π hπ => ?_)
    rw [norm_prod, ← prod_parts_prod π b, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun J hJ =>
      hκ J (two_le_card_of_mem_atLeastTwoPartitions hπ hJ)
  have hcard : (Finset.univ \ I).card = k - I.card := by
    rw [Finset.card_univ_sdiff, Fintype.card_fin]
  have hmove : ∑ π ∈ atLeastTwoPartitions (Finset.univ \ I),
        ∏ J ∈ π.parts, D J.card =
      ∑ π ∈ singletonFree (k - I.card), ∏ J ∈ π.parts, D J.card := by
    rw [← sum_singletonFree_transport hTr (increasingEquiv (Finset.univ \ I) hcard)
      fun J => D J.card]
    refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J hJ => ?_
    rw [((hTr _ _ _ _ (increasingEquiv (Finset.univ \ I) hcard)).2 π).2.1 J hJ]
  have hb := Finset.prod_sdiff (f := b) (Finset.subset_univ I)
  rw [hmove] at hsum
  calc ‖(∏ i ∈ I, (centeredMean μ X c i : ℂ)) *
        ∑ π ∈ atLeastTwoPartitions (Finset.univ \ I),
          ∏ J ∈ π.parts, recenteredCumulant μ X c J‖
      ≤ (D 1 ^ I.card * ∏ i ∈ I, b i) *
        ((∑ π ∈ singletonFree (k - I.card), ∏ J ∈ π.parts, D J.card) *
          ∏ i ∈ Finset.univ \ I, b i) := by
        rw [norm_mul]
        exact mul_le_mul hprod hsum (norm_nonneg _) ((norm_nonneg _).trans hprod)
    _ = D 1 ^ I.card * (∑ π ∈ singletonFree (k - I.card), ∏ J ∈ π.parts, D J.card) *
        ∏ i, b i := by
        rw [← hb]
        ring
end YangMills.Construction.Cumulants.ProductRecentering
