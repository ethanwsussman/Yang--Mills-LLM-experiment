import YangMills.Construction.SystemOfAdmissibleConstants.CumulantOfVariablesWithBoundedCentredMomentsProof
import YangMills.Construction.Cumulants.FactorialSumOverThePartitions
import YangMills.Construction.Cumulants.JointCumulantThroughMoments
import YangMills.Construction.Cumulants.JointCumulantsAreRealSymmetricAndMultilinear
import YangMills.Construction.Cumulants.MomentsLinearityBoundsAndTelescopingOfJointCumulants
import YangMills.Construction.Cumulants.MultilinearityShiftsAndMomentsOfJointCumulants
import YangMills.Construction.SourcesAndGluing.CumulantsOfBoundedVariablesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Cumulants.MixedCumulantFacts
open YangMills.Construction.Probability (IsBoundedRealRV)
open YangMills.Construction.SetPartition (PartitionsFin blockCount blockFactorialSum)
def blockMin {k : ℕ} (π : PartitionsFin k) (i : Fin k) : Fin k :=
  (π.part i).min' ⟨i, π.mem_part (Finset.mem_univ i)⟩
theorem blockMin_mem {k : ℕ} (π : PartitionsFin k) (i : Fin k) :
    blockMin π i ∈ π.part i :=
  Finset.min'_mem _ _
theorem part_blockMin {k : ℕ} (π : PartitionsFin k) (i : Fin k) :
    π.part (blockMin π i) = π.part i :=
  π.part_eq_of_mem (π.part_mem.2 (Finset.mem_univ i)) (blockMin_mem π i)
theorem blockMin_le {k : ℕ} (π : PartitionsFin k) (i : Fin k) : blockMin π i ≤ i :=
  Finset.min'_le _ _ (π.mem_part (Finset.mem_univ i))
theorem blockMin_eq_iff {k : ℕ} (π : PartitionsFin k) (a b : Fin k) :
    blockMin π a = blockMin π b ↔ π.part a = π.part b := by
  constructor
  · intro h
    rw [← part_blockMin π a, h, part_blockMin]
  · intro h
    simp only [blockMin, h]
theorem blockMin_blockMin {k : ℕ} (π : PartitionsFin k) (i : Fin k) :
    blockMin π (blockMin π i) = blockMin π i :=
  (blockMin_eq_iff π _ _).2 (part_blockMin π i)
theorem blockCount_eq_card_fixed {k : ℕ} (π : PartitionsFin k) :
    blockCount π = (Finset.univ.filter fun i => blockMin π i = i).card := by
  have hinj : Set.InjOn π.part
      (Finset.univ.filter fun i => blockMin π i = i : Finset (Fin k)) := by
    intro a ha b hb hab
    have ha' : blockMin π a = a := by simpa using ha
    have hb' : blockMin π b = b := by simpa using hb
    rw [← ha', ← hb']
    exact (blockMin_eq_iff π a b).2 hab
  rw [← Finset.card_image_of_injOn hinj, blockCount]
  congr 1
  ext J
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hJ
    obtain ⟨a, ha⟩ := π.nonempty_of_mem_parts hJ
    have hp : π.part a = J := π.part_eq_of_mem hJ ha
    exact ⟨blockMin π a, blockMin_blockMin π a, by rw [part_blockMin, hp]⟩
  · rintro ⟨a, -, rfl⟩
    exact π.part_mem.2 (Finset.mem_univ a)
theorem blockMin_injective {k : ℕ} :
    Function.Injective (blockMin (k := k)) := by
  have key : ∀ π π' : PartitionsFin k, blockMin π = blockMin π' →
      π.parts ⊆ π'.parts := by
    intro π π' h J hJ
    obtain ⟨a, ha⟩ := π.nonempty_of_mem_parts hJ
    have hp : π.part a = π'.part a := by
      ext b
      rw [π.mem_part_iff_part_eq_part (Finset.mem_univ b) (Finset.mem_univ a),
        π'.mem_part_iff_part_eq_part (Finset.mem_univ b) (Finset.mem_univ a),
        ← blockMin_eq_iff, ← blockMin_eq_iff, h]
    rw [← π.part_eq_of_mem hJ ha, hp]
    exact π'.part_mem.2 (Finset.mem_univ a)
  intro π π' h
  exact Finpartition.ext (Finset.Subset.antisymm (key _ _ h) (key _ _ h.symm))
def fixedPointFactorial {k : ℕ} (f : Fin k → Fin k) : ℕ :=
  ((Finset.univ.filter fun i => f i = i).card - 1).factorial
def decreasingIdempotents (k : ℕ) : Finset (Fin k → Fin k) :=
  Finset.univ.filter fun f => ∀ i, f i ≤ i ∧ f (f i) = f i
theorem blockFactorialSum_le (k : ℕ) :
    blockFactorialSum k ≤ ∑ f ∈ decreasingIdempotents k, fixedPointFactorial f := by
  have h : blockFactorialSum k =
      ∑ f ∈ Finset.univ.image (blockMin (k := k)), fixedPointFactorial f := by
    rw [Finset.sum_image blockMin_injective.injOn, blockFactorialSum]
    exact Finset.sum_congr rfl fun π _ => by rw [blockCount_eq_card_fixed, fixedPointFactorial]
  rw [h]
  refine Finset.sum_le_sum_of_subset fun f hf => ?_
  obtain ⟨π, -, rfl⟩ := Finset.mem_image.1 hf
  simp only [decreasingIdempotents, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun i => ⟨blockMin_le π i, blockMin_blockMin π i⟩
theorem blockFactorialSum_le_const {k : ℕ} (h1 : 1 ≤ k) (h4 : k ≤ 4) :
    (blockFactorialSum k : ℝ) ≤ cumulantBoundConst k := by
  have e1 : ∑ f ∈ decreasingIdempotents 1, fixedPointFactorial f = 1 := by decide +kernel
  have e2 : ∑ f ∈ decreasingIdempotents 2, fixedPointFactorial f = 2 := by decide +kernel
  have e3 : ∑ f ∈ decreasingIdempotents 3, fixedPointFactorial f = 6 := by decide +kernel
  have e4 : ∑ f ∈ decreasingIdempotents 4, fixedPointFactorial f = 26 := by decide +kernel
  have hk := blockFactorialSum_le k
  interval_cases k
  · rw [e1] at hk
    rw [show cumulantBoundConst 1 = ((1 : ℕ) : ℝ) by norm_num [cumulantBoundConst]]
    exact Nat.cast_le.2 hk
  · rw [e2] at hk
    rw [show cumulantBoundConst 2 = ((2 : ℕ) : ℝ) by norm_num [cumulantBoundConst]]
    exact Nat.cast_le.2 hk
  · rw [e3] at hk
    rw [show cumulantBoundConst 3 = ((6 : ℕ) : ℝ) by norm_num [cumulantBoundConst]]
    exact Nat.cast_le.2 hk
  · rw [e4] at hk
    rw [show cumulantBoundConst 4 = ((26 : ℕ) : ℝ) by norm_num [cumulantBoundConst]]
    exact Nat.cast_le.2 hk
theorem eLpNorm_ne_top_of_isBoundedRealRV {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] {x : Ω → ℝ} (hx : IsBoundedRealRV x) (p : ℝ≥0∞) :
    eLpNorm x p ν ≠ ⊤ := by
  obtain ⟨C, hC⟩ := hx.bounded
  exact (MemLp.of_bound hx.measurable.aestronglyMeasurable C (ae_of_all _ hC)).eLpNorm_ne_top
theorem enorm_finset_prod_real {ι : Type*} (J : Finset ι) (f : ι → ℝ) :
    ‖∏ i ∈ J, f i‖ₑ = ∏ i ∈ J, ‖f i‖ₑ := by
  simp only [Real.enorm_eq_ofReal_abs, Finset.abs_prod]
  exact ENNReal.ofReal_prod_of_nonneg fun _ _ => abs_nonneg _
theorem abs_integral_prod_le_prod_eLpNorm_four {Ω ι : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] (J : Finset ι) (x h : ι → Ω → ℝ) (hJ0 : J.Nonempty)
    (hJ : J.card ≤ 4) (hm : ∀ i ∈ J, AEStronglyMeasurable (h i) ν)
    (hfin : ∀ i ∈ J, eLpNorm (h i) 4 ν ≠ ⊤)
    (hle : ∀ i ∈ J, ∀ᵐ ω ∂ν, ‖x i ω‖ₑ ≤ ‖h i ω‖ₑ) :
    |∫ ω, ∏ i ∈ J, x i ω ∂ν| ≤ ∏ i ∈ J, (eLpNorm (h i) 4 ν).toReal := by
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = J.card := ⟨_, rfl⟩
  have hmpos : 0 < m := by
    rw [hmdef]
    exact_mod_cast hJ0.card_pos
  have hm4 : ENNReal.ofReal m ≤ 4 := by
    have : m ≤ 4 := by
      rw [hmdef]
      exact_mod_cast hJ
    simpa using ENNReal.ofReal_le_ofReal this
  have hae : ∀ᵐ ω ∂ν, ∀ i ∈ J, ‖x i ω‖ₑ ≤ ‖h i ω‖ₑ :=
    (ae_ball_iff J.countable_toSet).2 hle
  have h1 : ∫⁻ ω, ‖∏ i ∈ J, x i ω‖ₑ ∂ν ≤ ∫⁻ ω, ∏ i ∈ J, (‖h i ω‖ₑ ^ m) ^ (1 / m) ∂ν := by
    refine lintegral_mono_ae (hae.mono fun ω hω => ?_)
    rw [enorm_finset_prod_real]
    refine Finset.prod_le_prod' fun i hi => ?_
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hmpos.ne', ENNReal.rpow_one]
    exact hω i hi
  have h2 := ENNReal.lintegral_prod_norm_pow_le (μ := ν) J
    (f := fun i ω => ‖h i ω‖ₑ ^ m) (p := fun _ => 1 / m)
    (fun i hi => (hm i hi).enorm.pow_const m)
    (by rw [Finset.sum_const, nsmul_eq_mul, ← hmdef]; field_simp)
    (fun _ _ => by positivity)
  have h3 : ∀ i ∈ J, (∫⁻ ω, ‖h i ω‖ₑ ^ m ∂ν) ^ (1 / m) ≤ eLpNorm (h i) 4 ν := by
    intro i hi
    have e : (∫⁻ ω, ‖h i ω‖ₑ ^ m ∂ν) ^ (1 / m) = eLpNorm (h i) (ENNReal.ofReal m) ν := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hmpos) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hmpos.le]
    rw [e]
    exact eLpNorm_le_eLpNorm_of_exponent_le hm4 (hm i hi)
  have h4 : ‖∫ ω, ∏ i ∈ J, x i ω ∂ν‖ₑ ≤ ∏ i ∈ J, eLpNorm (h i) 4 ν :=
    (enorm_integral_le_lintegral_enorm _).trans
      (h1.trans (h2.trans (Finset.prod_le_prod' h3)))
  have hfinP : ∏ i ∈ J, eLpNorm (h i) 4 ν ≠ ⊤ := ENNReal.prod_ne_top hfin
  calc |∫ ω, ∏ i ∈ J, x i ω ∂ν| = (‖∫ ω, ∏ i ∈ J, x i ω ∂ν‖ₑ).toReal := by
        rw [toReal_enorm, Real.norm_eq_abs]
    _ ≤ (∏ i ∈ J, eLpNorm (h i) 4 ν).toReal := ENNReal.toReal_mono hfinP h4
    _ = ∏ i ∈ J, (eLpNorm (h i) 4 ν).toReal := ENNReal.toReal_prod _ _
theorem abs_blockMoment_le {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {k : ℕ} (X : Fin k → Ω → ℝ) (hX : ∀ i, IsBoundedRealRV (X i))
    (I J : Finset (Fin k)) (hJ0 : J.Nonempty) (hJ : J.card ≤ 4) :
    |∫ ω, ∏ i ∈ J, X i ω ∂ν| ≤ ∏ i ∈ J,
      if i ∈ I then (eLpNorm (X i) ⊤ ν).toReal else (eLpNorm (X i) 4 ν).toReal := by
  classical
  have hconst : ∀ i, eLpNorm (fun _ : Ω => (eLpNorm (X i) ⊤ ν).toReal) 4 ν =
      ‖(eLpNorm (X i) ⊤ ν).toReal‖ₑ := fun i => by
    rw [eLpNorm_const _ (by norm_num) (IsProbabilityMeasure.ne_zero ν)]
    simp
  have hb := abs_integral_prod_le_prod_eLpNorm_four ν J X
    (fun i => if i ∈ I then fun _ => (eLpNorm (X i) ⊤ ν).toReal else X i) hJ0 hJ
    (fun i _ => by
      by_cases hi : i ∈ I
      · simpa [hi] using aestronglyMeasurable_const
      · simpa [hi] using (hX i).measurable.aestronglyMeasurable)
    (fun i _ => by
      by_cases hi : i ∈ I
      · simp only [hi, if_true]
        rw [hconst]
        exact enorm_ne_top
      · simpa [hi] using eLpNorm_ne_top_of_isBoundedRealRV ν (hX i) 4)
    (fun i _ => by
      by_cases hi : i ∈ I
      · simp only [hi, if_true]
        have ha : ∀ᵐ ω ∂ν, ‖X i ω‖ₑ ≤ eLpNorm (X i) ⊤ ν := by
          simpa [eLpNorm_exponent_top] using ae_le_eLpNormEssSup (f := X i) (μ := ν)
        refine ha.mono fun ω hω => hω.trans_eq ?_
        rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (eLpNorm_ne_top_of_isBoundedRealRV ν (hX i) ⊤)]
      · simp [hi])
  refine hb.trans_eq (Finset.prod_congr rfl fun i _ => ?_)
  by_cases hi : i ∈ I
  · simp only [hi, if_true]
    rw [hconst, toReal_enorm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  · simp [hi]
theorem prod_parts_prod {k : ℕ} (π : PartitionsFin k) (w : Fin k → ℝ) :
    ∏ J ∈ π.parts, ∏ i ∈ J, w i = ∏ i, w i := by apply _root_.YangMills.DeltaSharedProofs.p21832 <;> assumption
theorem norm_mixedCumulant_le {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν]
    {k : ℕ} (X : Fin k → Ω → ℝ) (hX : ∀ i, IsBoundedRealRV (X i)) (hk1 : 1 ≤ k)
    (hk4 : k ≤ 4) (I : Finset (Fin k))
    (hA : mixedCumulant ν X =
      ∑ π : PartitionsFin k, (-1 : ℂ) ^ (blockCount π - 1) *
        ((blockCount π - 1).factorial : ℂ) *
          ∏ J ∈ π.parts, ((∫ ω, ∏ i ∈ J, X i ω ∂ν : ℝ) : ℂ)) :
    ‖mixedCumulant ν X‖ ≤ cumulantBoundConst k * (∏ i ∈ I, (eLpNorm (X i) ⊤ ν).toReal) *
      ∏ i ∈ Iᶜ, (eLpNorm (X i) 4 ν).toReal := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : Fin k → ℝ, w = fun i =>
      if i ∈ I then (eLpNorm (X i) ⊤ ν).toReal else (eLpNorm (X i) 4 ν).toReal := ⟨_, rfl⟩
  have hw0 : ∀ i, 0 ≤ w i := fun i => by
    rw [hw]
    dsimp only
    split_ifs <;> exact ENNReal.toReal_nonneg
  have hW0 : 0 ≤ ∏ i, w i := Finset.prod_nonneg fun i _ => hw0 i
  have hterm : ∀ π : PartitionsFin k,
      ‖(-1 : ℂ) ^ (blockCount π - 1) * ((blockCount π - 1).factorial : ℂ) *
        ∏ J ∈ π.parts, ((∫ ω, ∏ i ∈ J, X i ω ∂ν : ℝ) : ℂ)‖ ≤
      ((blockCount π - 1).factorial : ℝ) * ∏ i, w i := fun π => by
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast,
      norm_prod, ← prod_parts_prod π w]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun J hJ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, hw]
    have hcard : J.card ≤ 4 := by
      refine (Finset.card_le_univ J).trans ?_
      simpa using hk4
    exact abs_blockMoment_le ν X hX I J (π.nonempty_of_mem_parts hJ) hcard
  have hsplit : ∏ i, w i = (∏ i ∈ I, (eLpNorm (X i) ⊤ ν).toReal) *
      ∏ i ∈ Iᶜ, (eLpNorm (X i) 4 ν).toReal := by
    rw [← Finset.prod_mul_prod_compl I w]
    congr 1
    · exact Finset.prod_congr rfl fun i hi => by rw [hw]; simp [hi]
    · exact Finset.prod_congr rfl fun i hi => by
        rw [hw]
        simp [Finset.mem_compl.1 hi]
  calc ‖mixedCumulant ν X‖
      ≤ ∑ π : PartitionsFin k, ((blockCount π - 1).factorial : ℝ) * ∏ i, w i := by
        rw [hA]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => hterm π)
    _ = (blockFactorialSum k : ℝ) * ∏ i, w i := by
        rw [← Finset.sum_mul, blockFactorialSum]
        push_cast
        rfl
    _ ≤ cumulantBoundConst k * ∏ i, w i :=
        mul_le_mul_of_nonneg_right (blockFactorialSum_le_const hk1 hk4) hW0
    _ = _ := by rw [hsplit, mul_assoc]
theorem isBoundedRealRV_update {Ω : Type} [MeasurableSpace Ω] {k : ℕ} {W : Fin k → Ω → ℝ}
    (hW : ∀ j, IsBoundedRealRV (W j)) (i : Fin k) {Y : Ω → ℝ}
    (hY : IsBoundedRealRV Y) (j : Fin k) :
    IsBoundedRealRV (Function.update W i Y j) := by apply _root_.YangMills.Construction.SourcesAndGluing.BoundedCumulants.isBoundedRealRV_update <;> assumption
theorem mixedCumulant_update_linear
    (hLin : RealSymmetricMultilinear.CumulantIsRealSymmetricMultilinear)
    {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] {k : ℕ} (hk : 1 ≤ k)
    {W : Fin k → Ω → ℝ} (hW : ∀ j, IsBoundedRealRV (W j)) (i : Fin k)
    (Y Y' : Ω → ℝ) (a a' : ℝ) (hY : IsBoundedRealRV Y)
    (hY' : IsBoundedRealRV Y') :
    mixedCumulant ν (Function.update W i fun ω => a * Y ω + a' * Y' ω) =
      (a : ℂ) * mixedCumulant ν (Function.update W i Y) +
        (a' : ℂ) * mixedCumulant ν (Function.update W i Y') := by
  obtain ⟨-, F, hF, M, -, hM⟩ := hLin Ω ν k hk
  have mem : ∀ x : Ω → ℝ, IsBoundedRealRV x → x ∈ F := fun x hx => by
    have : x ∈ (F : Set (Ω → ℝ)) := by
      rw [hF]
      exact hx
    exact this
  let g : Fin k → F := fun j => ⟨W j, mem _ (hW j)⟩
  let y : F := ⟨Y, mem _ hY⟩
  let y' : F := ⟨Y', mem _ hY'⟩
  have key : ∀ z : F, mixedCumulant ν (Function.update W i (z : Ω → ℝ)) =
      ((M (Function.update g i z) : ℝ) : ℂ) := fun z => by
    rw [← hM]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Function.update_of_ne hj, g]
  have hz : (fun ω => a * Y ω + a' * Y' ω) = ((a • y + a' • y' : F) : Ω → ℝ) := by
    funext ω
    simp [y, y']
  rw [hz, key, show Y = (y : Ω → ℝ) from rfl, show Y' = (y' : Ω → ℝ) from rfl, key, key,
    M.map_update_add, M.map_update_smul, M.map_update_smul]
  simp
def interpolateComponents {Ω : Type*} {k : ℕ} (X X' : Fin k → Ω → ℝ) (m : ℕ) :
    Fin k → Ω → ℝ :=
  fun j ω => if (j : ℕ) < m then X j ω else X j ω + X' j ω
theorem mixedCumulant_add_sub_eq_sum {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν]
    {k : ℕ} (hk : 1 ≤ k) (hLin : RealSymmetricMultilinear.CumulantIsRealSymmetricMultilinear)
    (X X' : Fin k → Ω → ℝ) (hX : ∀ i, IsBoundedRealRV (X i))
    (hX' : ∀ i, IsBoundedRealRV (X' i)) :
    mixedCumulant ν (fun i ω => X i ω + X' i ω) - mixedCumulant ν X =
      ∑ i, mixedCumulant ν (telescopeTuple X X' i) := by
  have hZ : ∀ m j, IsBoundedRealRV (interpolateComponents X X' m j) := fun m j => by
    by_cases hj : (j : ℕ) < m
    · have e : interpolateComponents X X' m j = X j := by
        funext ω
        simp [interpolateComponents, hj]
      rw [e]
      exact hX j
    · obtain ⟨C, hC⟩ := (hX j).bounded
      obtain ⟨C', hC'⟩ := (hX' j).bounded
      have e : interpolateComponents X X' m j = fun ω => X j ω + X' j ω := by
        funext ω
        simp [interpolateComponents, hj]
      rw [e]
      exact ⟨(hX j).measurable.add (hX' j).measurable, C + C', fun ω =>
        (abs_add_le _ _).trans (add_le_add (hC ω) (hC' ω))⟩
  have hstep : ∀ i : Fin k,
      mixedCumulant ν (interpolateComponents X X' (i : ℕ)) -
          mixedCumulant ν (interpolateComponents X X' ((i : ℕ) + 1)) =
        mixedCumulant ν (telescopeTuple X X' i) := fun i => by
    have h := mixedCumulant_update_linear hLin ν hk (hZ ((i : ℕ) + 1)) i (X i) (X' i) 1 1
      (hX i) (hX' i)
    have e0 : Function.update (interpolateComponents X X' ((i : ℕ) + 1)) i
        (fun ω => 1 * X i ω + 1 * X' i ω) = interpolateComponents X X' (i : ℕ) := by
      funext j ω
      by_cases hj : j = i
      · subst hj
        simp [interpolateComponents]
      · have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
        have hiff : (j : ℕ) < (i : ℕ) + 1 ↔ (j : ℕ) < i := by omega
        simp [Function.update_of_ne hj, interpolateComponents, hiff]
    have e1 : Function.update (interpolateComponents X X' ((i : ℕ) + 1)) i (X i) =
        interpolateComponents X X' ((i : ℕ) + 1) := by
      funext j ω
      by_cases hj : j = i
      · subst hj
        simp [interpolateComponents]
      · simp [Function.update_of_ne hj]
    have e2 : Function.update (interpolateComponents X X' ((i : ℕ) + 1)) i (X' i) =
        telescopeTuple X X' i := by
      funext j ω
      by_cases hj : j = i
      · subst hj
        simp [telescopeTuple]
      · have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
        have hiff : (j : ℕ) < (i : ℕ) + 1 ↔ j < i := by
          rw [Fin.lt_def]
          omega
        simp [interpolateComponents, telescopeTuple, hiff, hj]
    rw [e0, e1, e2] at h
    rw [h]
    simp
  have h0 : interpolateComponents X X' 0 = fun i ω => X i ω + X' i ω := by
    funext j ω
    simp [interpolateComponents]
  have hkk : interpolateComponents X X' k = X := by
    funext j ω
    simp [interpolateComponents]
  have hsum := Finset.sum_range_sub'
    (fun m => mixedCumulant ν (interpolateComponents X X' m)) k
  rw [← Fin.sum_univ_eq_sum_range
    (fun m => mixedCumulant ν (interpolateComponents X X' m) -
      mixedCumulant ν (interpolateComponents X X' (m + 1))) k] at hsum
  calc mixedCumulant ν (fun i ω => X i ω + X' i ω) - mixedCumulant ν X
      = mixedCumulant ν (interpolateComponents X X' 0) -
          mixedCumulant ν (interpolateComponents X X' k) := by rw [h0, hkk]
    _ = _ := hsum.symm
    _ = _ := Finset.sum_congr rfl fun i _ => hstep i
theorem mixedCumulantProperties_holds (hMoments : MixedCumulantMomentExpansion)
    (hLin : RealSymmetricMultilinear.CumulantIsRealSymmetricMultilinear)
    (hShift : MomentCumulantRelations.Holds) :
    MixedCumulantProperties := by
  intro Ω _ ν _ k X X' hk hX hX'
  refine ⟨hMoments Ω ν k X hk hX, ?_, ?_, ?_, ?_,
    mixedCumulant_add_sub_eq_sum ν hk hLin X X' hX hX'⟩
  · intro i Y Y' a a' hY hY'
    exact mixedCumulant_update_linear hLin ν hk hX i Y Y' a a' hY hY'
  · intro i Y hY hae
    rw [hMoments Ω ν k _ hk (isBoundedRealRV_update hX i hY), hMoments Ω ν k X hk hX]
    refine Finset.sum_congr rfl fun π _ => congrArg _ (Finset.prod_congr rfl fun J _ => ?_)
    refine congrArg _ (integral_congr_ae ?_)
    filter_upwards [hae] with ω hω
    refine Finset.prod_congr rfl fun l _ => ?_
    by_cases hl : l = i
    · subst hl
      simpa using hω
    · simp [Function.update_of_ne hl]
  · intro hk2 i b
    have h := (hShift Ω ν).2.2.1 k X (Pi.single i b) hk2 hX
    rw [← h]
    congr 1
    funext l ω
    by_cases hl : l = i
    · subst hl
      simp
    · simp [Function.update_of_ne hl, Pi.single_eq_of_ne hl]
  · intro hk4 I
    exact norm_mixedCumulant_le ν X hX hk hk4 I (hMoments Ω ν k X hk hX)
end YangMills.Construction.Cumulants.MixedCumulantFacts
