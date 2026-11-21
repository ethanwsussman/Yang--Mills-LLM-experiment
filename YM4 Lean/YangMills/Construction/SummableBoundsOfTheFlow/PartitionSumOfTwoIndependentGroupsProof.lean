import YangMills.Construction.SummableBoundsOfTheFlow.PartitionSumOfTwoIndependentGroups
import Mathlib
set_option autoImplicit false
noncomputable section
open Polynomial Finset
namespace YangMills.Construction.Cumulants.IndependentGroups
section Colourings
variable {α : Type} [Fintype α] [DecidableEq α]
def colourFibre {N : ℕ} (c : α → Fin N) (j : Fin N) : Finset α := univ.filter fun a => c a = j
theorem mem_colourFibre {N : ℕ} {c : α → Fin N} {j : Fin N} {a : α} : a ∈ colourFibre c j ↔ c a = j := by
  simp [colourFibre]
theorem colourFibre_injective_on_image {N : ℕ} {c : α → Fin N} {j j' : Fin N} (hj : j ∈ univ.image c)
    (h : colourFibre c j = colourFibre c j') : j = j' := by
  obtain ⟨a, -, rfl⟩ := mem_image.mp hj
  have : a ∈ colourFibre c j' := by
    rw [← h]
    exact mem_colourFibre.mpr rfl
  exact mem_colourFibre.mp this
def fibrePartition {N : ℕ} (c : α → Fin N) : Finpartition (univ : Finset α) where
  parts := (univ.image c).image (colourFibre c)
  supIndep := by
    apply Finset.supIndep_iff_pairwiseDisjoint.mpr
    intro J hJ J' hJ' hne
    obtain ⟨j, -, rfl⟩ := mem_image.mp (mem_coe.mp hJ)
    obtain ⟨j', -, rfl⟩ := mem_image.mp (mem_coe.mp hJ')
    have hjj : j ≠ j' := fun h => hne (by rw [h])
    refine Finset.disjoint_left.mpr fun a ha ha' => hjj ?_
    rw [← mem_colourFibre.mp ha, ← mem_colourFibre.mp ha']
  sup_parts := by
    ext a
    simp only [Finset.mem_sup, mem_image, mem_univ, true_and, id, iff_true]
    exact ⟨colourFibre c (c a), ⟨c a, ⟨a, rfl⟩, rfl⟩, mem_colourFibre.mpr rfl⟩
  bot_notMem := by
    intro h
    obtain ⟨j, hj, hj'⟩ := mem_image.mp h
    obtain ⟨a, -, rfl⟩ := mem_image.mp hj
    have : a ∈ colourFibre c (c a) := mem_colourFibre.mpr rfl
    rw [hj'] at this
    simp at this
theorem mem_fibrePartition_parts {N : ℕ} {c : α → Fin N} {J : Finset α} :
    J ∈ (fibrePartition c).parts ↔ ∃ a, colourFibre c (c a) = J := by
  simp only [fibrePartition, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨j, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨c a, ⟨a, rfl⟩, rfl⟩
theorem prod_colourFibre_eq_prod_parts {N : ℕ} (m : Finset α → ℝ) (hm : m ∅ = 1) (c : α → Fin N) :
    ∏ j, m (colourFibre c j) = ∏ J ∈ (fibrePartition c).parts, m J := by
  have h1 : ∏ J ∈ (fibrePartition c).parts, m J = ∏ j ∈ univ.image c, m (colourFibre c j) := by
    change ∏ J ∈ (univ.image c).image (colourFibre c), m J = _
    rw [prod_image]
    intro j hj j' _ h
    exact colourFibre_injective_on_image (mem_coe.mp hj) h
  rw [h1]
  symm
  apply prod_subset (subset_univ _)
  intro j _ hj
  have : colourFibre c j = ∅ := by
    ext a
    simp only [mem_colourFibre, notMem_empty, iff_false]
    intro h
    exact hj (mem_image.mpr ⟨a, mem_univ _, h⟩)
  rw [this, hm]
def colouringOfEmbedding {N : ℕ} (π : Finpartition (univ : Finset α)) (e : π.parts ↪ Fin N) : α → Fin N :=
  fun a => e ⟨π.part a, π.part_mem.mpr (mem_univ a)⟩
theorem part_eq_of_colouringOfEmbedding_eq {N : ℕ} (π : Finpartition (univ : Finset α)) (e : π.parts ↪ Fin N)
    {a b : α} (h : colouringOfEmbedding π e a = colouringOfEmbedding π e b) : π.part a = π.part b := by
  have := e.injective h
  exact congrArg Subtype.val this
theorem colourFibre_colouringOfEmbedding {N : ℕ} (π : Finpartition (univ : Finset α)) (e : π.parts ↪ Fin N)
    (a : α) : colourFibre (colouringOfEmbedding π e) (colouringOfEmbedding π e a) = π.part a := by
  ext b
  rw [mem_colourFibre]
  constructor
  · intro h
    rw [← part_eq_of_colouringOfEmbedding_eq π e h]
    exact π.mem_part_self.mpr (mem_univ b)
  · intro h
    have hb : π.part b = π.part a := π.part_eq_of_mem (π.part_mem.mpr (mem_univ a)) h
    simp only [colouringOfEmbedding, hb]
theorem fibrePartition_colouringOfEmbedding {N : ℕ} (π : Finpartition (univ : Finset α))
    (e : π.parts ↪ Fin N) : fibrePartition (colouringOfEmbedding π e) = π := by
  apply Finpartition.ext
  ext J
  rw [mem_fibrePartition_parts]
  constructor
  · rintro ⟨a, rfl⟩
    rw [colourFibre_colouringOfEmbedding]
    exact π.part_mem.mpr (mem_univ a)
  · intro hJ
    obtain ⟨a, ha⟩ := π.nonempty_of_mem_parts hJ
    exact ⟨a, by rw [colourFibre_colouringOfEmbedding]; exact π.part_eq_of_mem hJ ha⟩
theorem part_eq_colourFibre {N : ℕ} {π : Finpartition (univ : Finset α)} {c : α → Fin N}
    (h : fibrePartition c = π) (a : α) : π.part a = colourFibre c (c a) := by
  have hm : colourFibre c (c a) ∈ π.parts := by
    rw [← h]
    exact mem_fibrePartition_parts.mpr ⟨a, rfl⟩
  exact π.part_eq_of_mem hm (mem_colourFibre.mpr rfl)
theorem card_colourings_with_fibrePartition (N : ℕ) (π : Finpartition (univ : Finset α)) :
    (univ.filter fun c : α → Fin N => fibrePartition c = π).card = N.descFactorial π.parts.card := by
  have hcard : Fintype.card (π.parts ↪ Fin N) = N.descFactorial π.parts.card := by
    rw [Fintype.card_embedding_eq]
    simp
  rw [← hcard, ← Fintype.card_coe]
  symm
  refine Fintype.card_of_bijective (f := fun e => ⟨colouringOfEmbedding π e, ?_⟩) ⟨?_, ?_⟩
  · exact mem_filter.mpr ⟨mem_univ _, fibrePartition_colouringOfEmbedding π e⟩
  · intro e e' hee
    have hc : colouringOfEmbedding π e = colouringOfEmbedding π e' := congrArg Subtype.val hee
    ext J
    obtain ⟨a, ha⟩ := π.nonempty_of_mem_parts J.2
    have hJ : π.part a = J.1 := π.part_eq_of_mem J.2 ha
    have := congrFun hc a
    simp only [colouringOfEmbedding] at this
    have hJ' : (⟨π.part a, π.part_mem.mpr (mem_univ a)⟩ : π.parts) = J := Subtype.ext hJ
    rw [hJ'] at this
    rw [this]
  · rintro ⟨c, hc⟩
    have hk : fibrePartition c = π := (mem_filter.mp hc).2
    have hrep : ∀ J : π.parts, ∃ a, a ∈ J.1 := fun J => π.nonempty_of_mem_parts J.2
    choose rep hrep using hrep
    have hinj : Function.Injective fun J : π.parts => c (rep J) := by
      intro J J' h
      have h1 : π.part (rep J) = J.1 := π.part_eq_of_mem J.2 (hrep J)
      have h2 : π.part (rep J') = J'.1 := π.part_eq_of_mem J'.2 (hrep J')
      apply Subtype.ext
      rw [← h1, ← h2, part_eq_colourFibre hk, part_eq_colourFibre hk]
      simp only at h
      rw [h]
    refine ⟨⟨_, hinj⟩, ?_⟩
    apply Subtype.ext
    funext a
    have hmem : rep ⟨π.part a, π.part_mem.mpr (mem_univ a)⟩ ∈ π.part a := hrep _
    exact show c (rep ⟨π.part a, π.part_mem.mpr (mem_univ a)⟩) = c a from
      mem_colourFibre.mp ((Finset.ext_iff.mp (part_eq_colourFibre hk a) _).mp hmem)
def colouringSum (m : Finset α → ℝ) (N : ℕ) : ℝ := ∑ c : α → Fin N, ∏ j, m (colourFibre c j)
def partitionPolynomial (m : Finset α → ℝ) : ℝ[X] :=
  ∑ π : Finpartition (univ : Finset α), C (∏ J ∈ π.parts, m J) * descPochhammer ℝ π.parts.card
theorem eval_partitionPolynomial (m : Finset α → ℝ) (hm : m ∅ = 1) (N : ℕ) :
    (partitionPolynomial m).eval (N : ℝ) = colouringSum m N := by
  have h : colouringSum m N = ∑ π : Finpartition (univ : Finset α),
      ∑ c ∈ univ.filter (fun c : α → Fin N => fibrePartition c = π), ∏ j, m (colourFibre c j) := by
    rw [colouringSum, sum_fiberwise]
  rw [h, partitionPolynomial, eval_finsetSum]
  apply sum_congr rfl
  intro π _
  rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial]
  have : ∀ c ∈ univ.filter (fun c : α → Fin N => fibrePartition c = π),
      ∏ j, m (colourFibre c j) = ∏ J ∈ π.parts, m J := by
    intro c hc
    rw [prod_colourFibre_eq_prod_parts m hm, (mem_filter.mp hc).2]
  rw [sum_congr rfl this, sum_const, card_colourings_with_fibrePartition, nsmul_eq_mul, mul_comm]
theorem descPochhammer_succ_coeff_zero (n : ℕ) : (descPochhammer ℝ (n + 1)).coeff 0 = 0 := by
  rw [descPochhammer_succ_left]
  simp
theorem descPochhammer_succ_coeff_one (n : ℕ) :
    (descPochhammer ℝ (n + 1)).coeff 1 = (-1) ^ n * (n.factorial : ℝ) := by
  induction n with
  | zero => simp [descPochhammer_one]
  | succ n ih =>
    rw [descPochhammer_succ_right, mul_coeff_one, descPochhammer_succ_coeff_zero, ih]
    have h0 : (X - ((n + 1 : ℕ) : ℝ[X])).coeff 0 = -((n + 1 : ℕ) : ℝ) := by
      rw [← map_natCast C, coeff_sub, coeff_X_zero, coeff_C_zero]
      simp
    rw [h0, Nat.factorial_succ]
    push_cast
    ring
theorem card_parts_pos_of_nonempty [Nonempty α] (π : Finpartition (univ : Finset α)) :
    0 < π.parts.card := by
  have a : α := Classical.arbitrary α
  exact card_pos.mpr ⟨π.part a, π.part_mem.mpr (mem_univ a)⟩
theorem partitionPolynomial_coeff_zero [Nonempty α] (m : Finset α → ℝ) :
    (partitionPolynomial m).coeff 0 = 0 := by
  rw [partitionPolynomial, finsetSum_coeff]
  apply sum_eq_zero
  intro π _
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (card_parts_pos_of_nonempty π).ne'
  rw [coeff_C_mul, hn, descPochhammer_succ_coeff_zero, mul_zero]
theorem partitionPolynomial_coeff_one [Nonempty α] (m : Finset α → ℝ) :
    (partitionPolynomial m).coeff 1 = ∑ π : Finpartition (univ : Finset α),
      (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) * ∏ J ∈ π.parts, m J := by
  rw [partitionPolynomial, finsetSum_coeff]
  apply sum_congr rfl
  intro π _
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (card_parts_pos_of_nonempty π).ne'
  rw [coeff_C_mul, hn, descPochhammer_succ_coeff_one]
  simp only [Nat.succ_sub_one]
  ring
end Colourings
section Split
variable {α : Type} [Fintype α] [DecidableEq α]
def liftInside (A : Finset α) (U : Finset {a // a ∈ A}) : Finset α := U.map (Function.Embedding.subtype _)
def liftOutside (A : Finset α) (U : Finset {a // a ∉ A}) : Finset α := U.map (Function.Embedding.subtype _)
theorem colouringSum_split (A : Finset α) (f g : Finset α → ℝ) (N : ℕ) :
    colouringSum (fun J => f (J ∩ A) * g (J \ A)) N =
      colouringSum (fun U => f (liftInside A U)) N * colouringSum (fun U => g (liftOutside A U)) N := by
  rw [colouringSum, colouringSum, colouringSum, sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (fun a => a ∈ A) fun _ => Fin N) _ _ ?_
  intro c
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  have h1 : colourFibre c j ∩ A = liftInside A (colourFibre (fun a : {a // a ∈ A} => c a) j) := by
    ext a
    simp only [mem_inter, mem_colourFibre, liftInside, mem_map, Function.Embedding.subtype_apply,
      Subtype.exists, exists_and_right, exists_eq_right]
    constructor
    · rintro ⟨h, ha⟩
      exact ⟨ha, h⟩
    · rintro ⟨ha, h⟩
      exact ⟨h, ha⟩
  have h2 : colourFibre c j \ A = liftOutside A (colourFibre (fun a : {a // a ∉ A} => c a) j) := by
    ext a
    simp only [mem_sdiff, mem_colourFibre, liftOutside, mem_map, Function.Embedding.subtype_apply,
      Subtype.exists, exists_and_right, exists_eq_right]
    constructor
    · rintro ⟨h, ha⟩
      exact ⟨ha, h⟩
    · rintro ⟨ha, h⟩
      exact ⟨h, ha⟩
  rw [h1, h2]
  rfl
theorem partitionPolynomial_split (A : Finset α) (f g : Finset α → ℝ) (hf : f ∅ = 1) (hg : g ∅ = 1) :
    partitionPolynomial (fun J => f (J ∩ A) * g (J \ A)) =
      partitionPolynomial (fun U => f (liftInside A U)) *
        partitionPolynomial (fun U => g (liftOutside A U)) := by
  apply eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℝ))).mono
  rintro _ ⟨N, rfl⟩
  have e1 : ((∅ : Finset α) ∩ A) = ∅ := by simp
  have e2 : ((∅ : Finset α) \ A) = ∅ := by simp
  have e3 : liftInside A ∅ = ∅ := by simp [liftInside]
  have e4 : liftOutside A ∅ = ∅ := by simp [liftOutside]
  change eval (N : ℝ) _ = eval (N : ℝ) _
  rw [eval_mul, eval_partitionPolynomial _ (by simp only [e1, e2, hf, hg, mul_one]),
    eval_partitionPolynomial _ (by simp only [e3, hf]), eval_partitionPolynomial _ (by simp only [e4, hg]),
    colouringSum_split]
theorem alternating_partition_sum_eq_zero (A : Finset α) (f g : Finset α → ℝ) (hA : A.Nonempty)
    (hA' : Aᶜ.Nonempty) (hf : f ∅ = 1) (hg : g ∅ = 1) :
    ∑ π : Finpartition (univ : Finset α),
      (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) *
        ∏ J ∈ π.parts, (f (J ∩ A) * g (J \ A)) = 0 := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hA'
  have hb' : b ∉ A := by simpa using hb
  have : Nonempty α := ⟨a⟩
  have : Nonempty {a // a ∈ A} := ⟨⟨a, ha⟩⟩
  have : Nonempty {a // a ∉ A} := ⟨⟨b, hb'⟩⟩
  rw [← partitionPolynomial_coeff_one (fun J => f (J ∩ A) * g (J \ A)), partitionPolynomial_split A f g hf hg,
    mul_coeff_one, partitionPolynomial_coeff_zero, partitionPolynomial_coeff_zero]
  simp
end Split
theorem cumulantOfIndependentGroupsZero_holds : YangMills.Construction.Cumulants.CumulantOfIndependentGroupsZero := by
  intro p A f g hA hA' hf hg
  exact alternating_partition_sum_eq_zero A f g hA hA' hf hg
end YangMills.Construction.Cumulants.IndependentGroups
end
