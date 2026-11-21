import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMoments
import YangMills.Construction.Cumulants.JointCumulantThroughMoments
import YangMills.Construction.Cumulants.MomentExpansionUnderTwoMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants.MomentComparison
open YangMills.Construction.Probability (IsBoundedRealRV)
def finShiftEmb (n : ℕ) : Fin n ↪ ℕ :=
  ⟨fun i => i + 1, fun _ _ h => Fin.ext (Nat.succ_injective h)⟩
theorem finShiftEmb_mem_Icc {n : ℕ} (i : Fin n) : finShiftEmb n i ∈ Finset.Icc 1 n := by
  have := i.2
  change (i : ℕ) + 1 ∈ Finset.Icc 1 n
  rw [Finset.mem_Icc]
  omega
theorem exists_finShiftEmb_eq {n x : ℕ} (hx : x ∈ Finset.Icc 1 n) :
    ∃ i : Fin n, finShiftEmb n i = x := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hx
  refine ⟨⟨x - 1, by omega⟩, ?_⟩
  change x - 1 + 1 = x
  omega
def shiftedParts {n : ℕ} (σ : YangMills.Construction.SetPartition.PartitionsFin n) :
    Finset (Finset ℕ) :=
  σ.parts.image (Finset.map (finShiftEmb n))
theorem isFinsetPartition_shiftedParts {n : ℕ}
    (σ : YangMills.Construction.SetPartition.PartitionsFin n) :
    IsFinsetPartition (Finset.Icc 1 n) (shiftedParts σ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hB
    exact (σ.nonempty_of_mem_parts hA).map
  · intro B hB x hx
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hB
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hx
    exact finShiftEmb_mem_Icc i
  · intro B hB B' hB' hne
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hB)
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hB')
    have hAA : A ≠ A' := fun e => hne (by rw [e])
    exact (Finset.disjoint_map _).2 (σ.disjoint (Finset.mem_coe.2 hA) (Finset.mem_coe.2 hA') hAA)
  · ext x
    simp only [Finset.mem_biUnion, id]
    constructor
    · rintro ⟨B, hB, hx⟩
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hB
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hx
      exact finShiftEmb_mem_Icc i
    · intro hx
      obtain ⟨i, rfl⟩ := exists_finShiftEmb_eq hx
      have hi : i ∈ σ.parts.biUnion id := by
        rw [σ.biUnion_parts]
        exact Finset.mem_univ i
      obtain ⟨A, hA, hiA⟩ := Finset.mem_biUnion.1 hi
      exact ⟨_, Finset.mem_image_of_mem _ hA, Finset.mem_map_of_mem _ hiA⟩
def preimageFin (n : ℕ) (B : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => finShiftEmb n i ∈ B
theorem map_preimageFin {n : ℕ} {B : Finset ℕ} (hB : B ⊆ Finset.Icc 1 n) :
    (preimageFin n B).map (finShiftEmb n) = B := by
  ext x
  simp only [Finset.mem_map, preimageFin, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    obtain ⟨i, rfl⟩ := exists_finShiftEmb_eq (hB hx)
    exact ⟨i, hx, rfl⟩
def finpartitionOfIcc {n : ℕ} {P : Finset (Finset ℕ)}
    (h : IsFinsetPartition (Finset.Icc 1 n) P) :
    YangMills.Construction.SetPartition.PartitionsFin n where
  parts := P.image (preimageFin n)
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.2 (by
    intro A hA A' hA' hne
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hA)
    obtain ⟨B', hB', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hA')
    have hBB : B ≠ B' := fun e => hne (by rw [e])
    have hd : Disjoint B B' := h.pairwiseDisjoint (Finset.mem_coe.2 hB) (Finset.mem_coe.2 hB') hBB
    refine Finset.disjoint_left.2 fun i hi hi' => ?_
    exact Finset.disjoint_left.1 hd (Finset.mem_filter.1 hi).2 (Finset.mem_filter.1 hi').2)
  sup_parts := by
    rw [Finset.sup_eq_biUnion]
    ext i
    simp only [Finset.mem_biUnion, id, Finset.mem_univ, iff_true]
    have hx : finShiftEmb n i ∈ P.biUnion id := by
      rw [h.union]
      exact finShiftEmb_mem_Icc i
    obtain ⟨B, hB, hiB⟩ := Finset.mem_biUnion.1 hx
    exact ⟨_, Finset.mem_image_of_mem _ hB, Finset.mem_filter.2 ⟨Finset.mem_univ _, hiB⟩⟩
  bot_notMem := by
    intro hbot
    obtain ⟨B, hB, hBe⟩ := Finset.mem_image.1 hbot
    obtain ⟨x, hx⟩ := h.nonempty B hB
    have hm : x ∈ (preimageFin n B).map (finShiftEmb n) := by
      rw [map_preimageFin (h.subset B hB)]
      exact hx
    rw [hBe] at hm
    simp at hm
theorem sum_partitionsIcc_eq_sum_finpartition {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : Finset (Finset ℕ) → M) :
    ∑ P ∈ partitionsIcc n, f P =
      ∑ σ : YangMills.Construction.SetPartition.PartitionsFin n, f (shiftedParts σ) := by
  symm
  refine Finset.sum_bij (fun σ _ => shiftedParts σ)
    (fun σ _ => mem_finsetPartitions.2 (isFinsetPartition_shiftedParts σ))
    (fun σ _ σ' _ h => ?_) (fun P hP => ?_) (fun _ _ => rfl)
  · exact Finpartition.ext (Finset.image_injective (Finset.map_injective _) h)
  · have hP' : IsFinsetPartition (Finset.Icc 1 n) P :=
      mem_finsetPartitions.1 (show P ∈ finsetPartitions (Finset.Icc 1 n) from hP)
    refine ⟨finpartitionOfIcc hP', Finset.mem_univ _, ?_⟩
    change (P.image (preimageFin n)).image (Finset.map (finShiftEmb n)) = P
    rw [Finset.image_image]
    ext B
    simp only [Finset.mem_image, Function.comp]
    constructor
    · rintro ⟨B', hB', rfl⟩
      rwa [map_preimageFin (hP'.subset B' hB')]
    · intro hB
      exact ⟨B, hB, map_preimageFin (hP'.subset B hB)⟩
theorem blockCount_shiftedParts {n : ℕ}
    (σ : YangMills.Construction.SetPartition.PartitionsFin n) :
    YangMills.Construction.Cumulants.blockCount (shiftedParts σ) =
      YangMills.Construction.SetPartition.blockCount σ :=
  Finset.card_image_of_injective _ (Finset.map_injective _)
variable {Ω : Type*} [MeasurableSpace Ω]
theorem prod_blockMoment_shiftedParts (μ : Measure Ω) (X : ℕ → Ω → ℝ) {n : ℕ}
    (σ : YangMills.Construction.SetPartition.PartitionsFin n) :
    ∏ B ∈ shiftedParts σ, blockMoment μ X B =
      ∏ B ∈ σ.parts, ∫ ω, ∏ l ∈ B, shiftedFamily n X l ω ∂μ := by
  rw [shiftedParts, Finset.prod_image fun _ _ _ _ h => Finset.map_injective _ h]
  refine Finset.prod_congr rfl fun B _ => ?_
  simp only [blockMoment, Finset.prod_map]
  rfl
theorem ofReal_partitionMomentSum (μ : Measure Ω) (X : ℕ → Ω → ℝ) (n : ℕ) :
    (partitionMomentSum μ X n : ℂ) =
      ∑ σ : YangMills.Construction.SetPartition.PartitionsFin n,
        (-1 : ℂ) ^ (YangMills.Construction.SetPartition.blockCount σ - 1) *
        ((YangMills.Construction.SetPartition.blockCount σ - 1).factorial : ℂ) *
          ∏ B ∈ σ.parts, ((∫ ω, ∏ l ∈ B, shiftedFamily n X l ω ∂μ : ℝ) : ℂ) := by
  rw [partitionMomentSum, sum_partitionsIcc_eq_sum_finpartition, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [blockCount_shiftedParts, prod_blockMoment_shiftedParts]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_natCast, Complex.ofReal_prod]
theorem abs_prod_sub_prod_le_card_mul {ι : Type*} (s : Finset ι) (x y B : ι → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hx : ∀ j ∈ s, |x j| ≤ B j) (hy : ∀ j ∈ s, |y j| ≤ B j)
    (hxy : ∀ j ∈ s, |x j - y j| ≤ ε * B j) :
    |∏ j ∈ s, x j - ∏ j ∈ s, y j| ≤ s.card * ε * ∏ j ∈ s, B j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ih' := ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))
      (fun j hj => hy j (Finset.mem_insert_of_mem hj))
      (fun j hj => hxy j (Finset.mem_insert_of_mem hj))
    have hxa := hx a (Finset.mem_insert_self a s)
    have hya := hy a (Finset.mem_insert_self a s)
    have hxya := hxy a (Finset.mem_insert_self a s)
    have hBa : 0 ≤ B a := (abs_nonneg _).trans hxa
    have hP : |∏ j ∈ s, x j| ≤ ∏ j ∈ s, B j := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun _ _ => abs_nonneg _)
        fun j hj => hx j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha,
      Finset.card_insert_of_notMem ha]
    have e : x a * ∏ j ∈ s, x j - y a * ∏ j ∈ s, y j =
        (x a - y a) * ∏ j ∈ s, x j + y a * (∏ j ∈ s, x j - ∏ j ∈ s, y j) := by ring
    rw [e]
    calc |(x a - y a) * ∏ j ∈ s, x j + y a * (∏ j ∈ s, x j - ∏ j ∈ s, y j)|
        ≤ |x a - y a| * |∏ j ∈ s, x j| + |y a| * |∏ j ∈ s, x j - ∏ j ∈ s, y j| := by
          rw [← abs_mul, ← abs_mul]
          exact abs_add_le _ _
      _ ≤ (ε * B a) * ∏ j ∈ s, B j + B a * (s.card * ε * ∏ j ∈ s, B j) :=
          add_le_add (mul_le_mul hxya hP (abs_nonneg _) (mul_nonneg hε hBa))
            (mul_le_mul hya ih' (abs_nonneg _) hBa)
      _ = ((s.card + 1 : ℕ) : ℝ) * ε * (B a * ∏ j ∈ s, B j) := by
          push_cast
          ring
theorem abs_blockMoment_le (μ : Measure Ω) [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    {c : ℕ → ℝ} {B : Finset ℕ} (h : ∀ i ∈ B, ∀ ω, |X i ω| ≤ c i) :
    |blockMoment μ X B| ≤ ∏ i ∈ B, c i := by
  have hc : ∀ ω, ‖∏ i ∈ B, X i ω‖ ≤ ∏ i ∈ B, c i := fun ω => by
    rw [Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i hi => h i hi ω
  have hI := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hc)
  have h1 : μ.real Set.univ = 1 := by simp
  rw [h1, mul_one] at hI
  rw [blockMoment, ← Real.norm_eq_abs]
  exact hI
theorem abs_partitionMomentSum_sub_le (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {X : ℕ → Ω → ℝ} {n : ℕ} {c : ℕ → ℝ} {ε : ℝ}
    (hc : ∀ i ∈ Finset.Icc 1 n, 0 ≤ c i) (hε : 0 ≤ ε)
    (hX : ∀ i ∈ Finset.Icc 1 n, ∀ ω, |X i ω| ≤ c i)
    (hB : ∀ B : Finset ℕ, B.Nonempty → B ⊆ Finset.Icc 1 n →
      |blockMoment μ X B - blockMoment ν X B| ≤ ε * ∏ i ∈ B, c i) :
    |partitionMomentSum μ X n - partitionMomentSum ν X n| ≤
      (partitionWeight n : ℝ) * ε * ∏ i ∈ Finset.Icc 1 n, c i := by
  rw [partitionMomentSum, partitionMomentSum, ← Finset.sum_sub_distrib, partitionWeight,
    Nat.cast_sum, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun P hP => ?_)
  have hP' : IsFinsetPartition (Finset.Icc 1 n) P :=
    mem_finsetPartitions.1 (show P ∈ finsetPartitions (Finset.Icc 1 n) from hP)
  have hd := abs_prod_sub_prod_le_card_mul P (blockMoment μ X) (blockMoment ν X)
    (fun B => ∏ i ∈ B, c i) hε
    (fun B hB' => abs_blockMoment_le μ fun i hi ω => hX i (hP'.subset B hB' hi) ω)
    (fun B hB' => abs_blockMoment_le ν fun i hi ω => hX i (hP'.subset B hB' hi) ω)
    (fun B hB' => hB B (hP'.nonempty B hB') (hP'.subset B hB'))
  have hprod : ∏ B ∈ P, ∏ i ∈ B, c i = ∏ i ∈ Finset.Icc 1 n, c i := by
    have hU := Finset.prod_biUnion (f := c) hP'.pairwiseDisjoint
    rw [hP'.union] at hU
    exact hU.symm
  rw [hprod] at hd
  have hc0 : 0 ≤ ∏ i ∈ Finset.Icc 1 n, c i := Finset.prod_nonneg hc
  simp only [YangMills.Construction.Cumulants.blockCount]
  have hk : (P.card : ℝ) ≤ ((2 ^ P.card - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_sub_one_of_lt Nat.lt_two_pow_self
  have e : (-1 : ℝ) ^ (P.card - 1) * ((P.card - 1).factorial : ℝ) * ∏ B ∈ P, blockMoment μ X B -
      (-1 : ℝ) ^ (P.card - 1) * ((P.card - 1).factorial : ℝ) * ∏ B ∈ P, blockMoment ν X B =
      ((-1 : ℝ) ^ (P.card - 1) * ((P.card - 1).factorial : ℝ)) *
        (∏ B ∈ P, blockMoment μ X B - ∏ B ∈ P, blockMoment ν X B) := by ring
  rw [e, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast,
    Nat.cast_mul, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left (hd.trans ?_) (Nat.cast_nonneg _)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right hk (mul_nonneg hε hc0)
theorem momentExpansionAndStability_holds (hMixed : MixedCumulantMomentExpansion)
    (hRel : CumulantMomentRelations) :
    momentExpansionAndStability := by
  intro Ω _ n X hn hX
  have hY : ∀ l, IsBoundedRealRV (shiftedFamily n X l) :=
    fun l => hX _ (finShiftEmb_mem_Icc l)
  have hcum : ∀ (μ : Measure Ω) [IsProbabilityMeasure μ],
      mixedCumulant μ (shiftedFamily n X) = (partitionMomentSum μ X n : ℂ) := fun μ _ => by
    rw [ofReal_partitionMomentSum]
    exact hMixed Ω μ n _ hn hY
  refine ⟨fun μ _ => ?_, fun μ ν _ _ c ε hc hε _ hbound hB => ?_⟩
  · have hA := (hRel Ω μ n (shiftedFamily n X) hY).1 n (shiftedFamily n X) (fun _ => 0) hn hY
      ⟨measurable_const, 0, fun _ => by simp⟩
    refine ⟨rfl, hcum μ, hA.1, hA.2.1, fun l G G' a a' hG hG' => ?_⟩
    have hZ : ∀ i, IsBoundedRealRV (Function.update (shiftedFamily n X) l G i) := by
      intro i
      by_cases h : i = l
      · subst h
        rw [Function.update_self]
        exact hG
      · rw [Function.update_of_ne h]
        exact hY i
    have hL := ((hRel Ω μ n (shiftedFamily n X) hY).1 n _ G' hn hZ hG').2.2 l a a'
    simpa only [Function.update_self, Function.update_idem] using hL
  · rw [hcum μ, hcum ν, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_partitionMomentSum_sub_le μ ν hc hε hbound hB
end YangMills.Construction.Cumulants.MomentComparison
