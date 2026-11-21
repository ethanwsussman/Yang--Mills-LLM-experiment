import YangMills.Construction.MeasureTheory.ComplexMeasureFacts
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SetFunctions.CountablyAdditive
variable {X : Type*} [MeasurableSpace X]
abbrev emptySet : MeasurableSets X := ⟨∅, MeasurableSet.empty⟩
theorem apply_empty {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν) : ν emptySet = 0 := by
  have hd : PairwiseDisjointSeq (fun _ : ℕ => (emptySet : MeasurableSets X)) :=
    fun _ _ _ => by simp
  have hu : iUnionSets (fun _ : ℕ => (emptySet : MeasurableSets X)) = emptySet :=
    Subtype.ext (by simp [iUnionSets])
  have hl := h _ hd
  rw [hu] at hl
  have h1 := (hl.comp (tendsto_add_atTop_nat 1)).sub hl
  have h2 : ((fun N : ℕ => ∑ _j ∈ Finset.range N, ν emptySet) ∘ fun a => a + 1) -
      (fun N : ℕ => ∑ _j ∈ Finset.range N, ν emptySet) = fun _ => ν emptySet := by
    funext N
    simp only [Pi.sub_apply, Function.comp, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have h3 : Tendsto (fun _ : ℕ => ν emptySet) atTop (𝓝 (ν emptySet - ν emptySet)) := by
    rw [← h2]
    exact h1
  have h4 := tendsto_nhds_unique h3 tendsto_const_nhds
  simpa using h4.symm
theorem summable_max_zero {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    (φ : ℂ →L[ℝ] ℝ) {A : ℕ → MeasurableSets X} (hA : PairwiseDisjointSeq A) :
    Summable fun j => max (φ (ν (A j))) 0 := by
  classical
  set B : ℕ → MeasurableSets X := fun j => if 0 ≤ φ (ν (A j)) then A j else emptySet with hB
  have hd : PairwiseDisjointSeq B := by
    intro i j hij
    simp only [hB]
    split_ifs
    · exact hA hij
    all_goals simp
  have hl := (φ.continuous.tendsto _).comp (h B hd)
  have hv : ∀ j, φ (ν (B j)) = max (φ (ν (A j))) 0 := by
    intro j
    simp only [hB]
    split_ifs with hj
    · exact (max_eq_left hj).symm
    · rw [apply_empty h, map_zero]
      exact (max_eq_right (not_le.mp hj).le).symm
  have hs : Tendsto (fun N => ∑ j ∈ Finset.range N, max (φ (ν (A j))) 0) atTop
      (𝓝 (φ (ν (iUnionSets B)))) := by
    refine hl.congr fun N => ?_
    simp only [Function.comp, map_sum, hv]
  exact ((hasSum_iff_tendsto_nat_of_nonneg (fun j => le_max_right _ _) _).2 hs).summable
theorem summable_norm {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    {A : ℕ → MeasurableSets X} (hA : PairwiseDisjointSeq A) :
    Summable fun j => ‖ν (A j)‖ := by
  have h1 := summable_max_zero h Complex.reCLM hA
  have h2 := summable_max_zero h (-Complex.reCLM) hA
  have h3 := summable_max_zero h Complex.imCLM hA
  have h4 := summable_max_zero h (-Complex.imCLM) hA
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
    (((h1.add h2).add h3).add h4)
  have hz := Complex.norm_le_abs_re_add_abs_im (ν (A j))
  simp only [Complex.reCLM_apply, Complex.imCLM_apply, neg_apply]
  rcases le_total 0 (ν (A j)).re with hr | hr <;> rcases le_total 0 (ν (A j)).im with hi | hi <;>
    simp only [abs_of_nonneg, abs_of_nonpos, hr, hi] at hz <;>
    simp only [max_eq_left, max_eq_right, hr, hi, Left.nonneg_neg_iff, Left.neg_nonpos_iff] <;>
    linarith
theorem hasSum_iUnion {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    {A : ℕ → MeasurableSets X} (hA : PairwiseDisjointSeq A) :
    HasSum (fun j => ν (A j)) (ν (iUnionSets A)) := by
  have hs := (summable_norm h hA).of_norm.hasSum
  rwa [tendsto_nhds_unique hs.tendsto_sum_nat (h A hA)] at hs
open Classical in
def toComplexMeasure (ν : MeasurableSets X → ℂ) (h : IsCountablyAdditive ν) : ComplexMeasure X where
  measureOf' s := if hs : MeasurableSet s then ν ⟨s, hs⟩ else 0
  empty' := by
    rw [dif_pos MeasurableSet.empty]
    exact apply_empty h
  not_measurable' s hs := dif_neg hs
  m_iUnion' f hf hd := by
    have hu : MeasurableSet (⋃ i, f i) := MeasurableSet.iUnion hf
    rw [dif_pos hu]
    have hv : (fun i => if hs : MeasurableSet (f i) then ν ⟨f i, hs⟩ else 0) =
        fun i => ν ⟨f i, hf i⟩ := funext fun i => dif_pos (hf i)
    rw [hv]
    exact hasSum_iUnion h (A := fun i => ⟨f i, hf i⟩) hd
theorem toComplexMeasure_apply {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    (A : MeasurableSets X) : toComplexMeasure ν h (A : Set X) = ν A :=
  dif_pos A.2
theorem isFiniteMeasure_vectorVariation (V : ComplexMeasure X) : IsFiniteMeasure V.variation := by
  have : IsFiniteMeasure (ComplexMeasure.re V).totalVariation := by
    unfold SignedMeasure.totalVariation
    infer_instance
  have : IsFiniteMeasure (ComplexMeasure.im V).totalVariation := by
    unfold SignedMeasure.totalVariation
    infer_instance
  refine isFiniteMeasure_of_le
    ((ComplexMeasure.re V).totalVariation + (ComplexMeasure.im V).totalVariation)
    (VectorMeasure.variation_le_of_forall_enorm_le fun E _ => ?_)
  rw [Measure.add_apply]
  refine le_trans ?_ (add_le_add ((ComplexMeasure.re V).enorm_le_totalVariation E)
    ((ComplexMeasure.im V).enorm_le_totalVariation E))
  have h1 : ComplexMeasure.re V E = (V E).re := rfl
  have h2 : ComplexMeasure.im V E = (V E).im := rfl
  rw [h1, h2, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (Complex.norm_le_abs_re_add_abs_im _)
theorem coe_iUnionSets (A : ℕ → MeasurableSets X) :
    (iUnionSets A : Set X) = ⋃ j, (A j : Set X) := rfl
def cons (r : MeasurableSets X) (E : ℕ → MeasurableSets X) : ℕ → MeasurableSets X
  | 0 => r
  | j + 1 => E j
theorem tsum_enorm_le_variation (ν : MeasurableSets X → ℂ) {E : ℕ → MeasurableSets X}
    (hd : PairwiseDisjointSeq E) {A : MeasurableSets X} (hs : ∀ j, (E j : Set X) ⊆ A) :
    ∑' j, ‖ν (E j)‖ₑ ≤ variation ν A := by
  set rest : MeasurableSets X :=
    ⟨(A : Set X) \ (iUnionSets E : Set X), A.2.diff (iUnionSets E).2⟩ with hrest
  have hrd : ∀ j, Disjoint (rest : Set X) (E j : Set X) := by
    intro j
    refine Set.disjoint_left.2 fun x hx hxj => hx.2 ?_
    rw [coe_iUnionSets]
    exact Set.mem_iUnion.2 ⟨j, hxj⟩
  have hdB : PairwiseDisjointSeq (cons rest E) := by
    intro i j hij
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ j => exact hrd j
    | succ i =>
      cases j with
      | zero => exact (hrd i).symm
      | succ j => exact hd fun h => hij (by rw [h])
  have huB : iUnionSets (cons rest E) = A := by
    apply Subtype.ext
    ext x
    rw [coe_iUnionSets]
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
      cases j with
      | zero => exact hj.1
      | succ j => exact hs j hj
    · intro hx
      by_cases hu : x ∈ (iUnionSets E : Set X)
      · rw [coe_iUnionSets] at hu
        obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hu
        exact Set.mem_iUnion.2 ⟨j + 1, hj⟩
      · exact Set.mem_iUnion.2 ⟨0, hx, hu⟩
  have hsum : ∑' j, ‖ν (E j)‖ₑ ≤ ∑' j, ‖ν (cons rest E j)‖ₑ := by
    exact ENNReal.tsum_comp_le_tsum_of_injective (f := Nat.succ) Nat.succ_injective
      fun j => ‖ν (cons rest E j)‖ₑ
  exact hsum.trans
    (le_iSup_of_le (cons rest E) (le_iSup_of_le hdB (le_iSup_of_le huB le_rfl)))
theorem sum_enorm_le_variation {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    {A : MeasurableSets X} (P : Finset (Set X)) (hsub : ∀ t ∈ P, t ⊆ A)
    (hdis : (P : Set (Set X)).PairwiseDisjoint id) (hm : ∀ t ∈ P, MeasurableSet t) :
    ∑ p ∈ P, ‖toComplexMeasure ν h p‖ₑ ≤ variation ν A := by
  classical
  let e := P.equivFin
  set E : ℕ → MeasurableSets X := fun j =>
    if hj : j < P.card then ⟨(e.symm ⟨j, hj⟩).1, hm _ (e.symm ⟨j, hj⟩).2⟩ else emptySet with hE
  have hd : PairwiseDisjointSeq E := by
    intro i j hij
    simp only [hE]
    split_ifs with hi hj
    · refine hdis (e.symm _).2 (e.symm _).2 fun heq => hij ?_
      have := e.symm.injective (Subtype.ext heq)
      simpa using this
    all_goals simp
  have hs : ∀ j, (E j : Set X) ⊆ A := by
    intro j
    simp only [hE]
    split_ifs with hj
    · exact hsub _ (e.symm _).2
    · simp
  calc ∑ p ∈ P, ‖toComplexMeasure ν h p‖ₑ = ∑ p : P, ‖toComplexMeasure ν h p‖ₑ :=
        (Finset.sum_coe_sort P _).symm
    _ = ∑ i : Fin P.card, ‖toComplexMeasure ν h (e.symm i)‖ₑ :=
        (Equiv.sum_comp e.symm fun p : P => ‖toComplexMeasure ν h p‖ₑ).symm
    _ = ∑ j ∈ Finset.range P.card, ‖ν (E j)‖ₑ := by
        rw [Finset.sum_range]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hEi : E i = ⟨(e.symm i).1, hm _ (e.symm i).2⟩ := dif_pos i.2
        rw [hEi]
        exact congrArg (‖·‖ₑ) (toComplexMeasure_apply h ⟨(e.symm i).1, hm _ (e.symm i).2⟩)
    _ ≤ ∑' j, ‖ν (E j)‖ₑ := ENNReal.sum_le_tsum _
    _ ≤ variation ν A := tsum_enorm_le_variation ν hd hs
theorem variation_eq {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν) (A : MeasurableSets X) :
    variation ν A = (toComplexMeasure ν h).variation (A : Set X) := by
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hd => iSup_le fun hu => ?_
    have hA : (A : Set X) = ⋃ j, (B j : Set X) := by rw [← hu, coe_iUnionSets]
    rw [hA, measure_iUnion (f := fun j => (B j : Set X)) hd fun j => (B j).2]
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [← toComplexMeasure_apply h]
    exact VectorMeasure.enorm_measure_le_variation _ _
  · refine le_of_forall_lt fun a ha => ?_
    obtain ⟨P, h1, h2, h3, h4⟩ := VectorMeasure.exists_lt_sum_of_lt_variation _ A.2 ha
    exact h4.trans_le (sum_enorm_le_variation h P h1 h2 h3)
theorem enorm_le_variation {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    (A : MeasurableSets X) : ‖ν A‖ₑ ≤ variation ν A := by
  rw [variation_eq h, ← toComplexMeasure_apply h]
  exact VectorMeasure.enorm_measure_le_variation _ _
theorem variation_ne_top {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    (A : MeasurableSets X) : variation ν A ≠ ∞ := by
  have := isFiniteMeasure_vectorVariation (toComplexMeasure ν h)
  rw [variation_eq h]
  exact measure_ne_top _ _
theorem norm_le_variation_toReal {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    (A : MeasurableSets X) : ‖ν A‖ ≤ (variation ν A).toReal := by
  have := ENNReal.toReal_mono (variation_ne_top h A) (enorm_le_variation h A)
  simpa using this
theorem toMeasure_eq (M : Measure X) {m : MeasurableSets X → ℝ≥0∞}
    (hm : ∀ A : MeasurableSets X, m A = M (A : Set X)) : toMeasure m = M := by
  have h0 : m ⟨∅, MeasurableSet.empty⟩ = 0 := by
    rw [hm]
    simp
  have h1 : ∀ A : ℕ → MeasurableSets X, PairwiseDisjointSeq A →
      m (iUnionSets A) = ∑' j, m (A j) := by
    intro A hA
    simp only [hm]
    exact measure_iUnion (f := fun j => (A j : Set X)) hA fun j => (A j).2
  unfold toMeasure
  rw [dif_pos ⟨h0, h1⟩]
  refine Measure.ext fun s hs => ?_
  exact (Measure.ofMeasurable_apply s hs).trans (hm ⟨s, hs⟩)
theorem isFiniteMeasureValues_of_eq (M : Measure X) [IsFiniteMeasure M]
    {m : MeasurableSets X → ℝ≥0∞} (hm : ∀ A : MeasurableSets X, m A = M (A : Set X)) :
    IsFiniteMeasureValues m := by
  refine ⟨?_, fun A => ?_⟩
  · rw [toMeasure_eq M hm]
    infer_instance
  · rw [toMeasure_eq M hm]
    exact (hm A).symm
theorem toMeasure_variation {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν) :
    toMeasure (variation ν) = (toComplexMeasure ν h).variation :=
  toMeasure_eq _ (variation_eq h)
theorem isCountablyAdditive_add {ν ν' : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    (h' : IsCountablyAdditive ν') : IsCountablyAdditive (ν + ν') := by
  intro A hA
  simpa [Finset.sum_add_distrib] using (h A hA).add (h' A hA)
theorem isCountablyAdditive_smul {ν : MeasurableSets X → ℂ} (c : ℂ) (h : IsCountablyAdditive ν) :
    IsCountablyAdditive (c • ν) := by
  intro A hA
  simpa [Finset.mul_sum] using (h A hA).const_mul c
theorem isCountablyAdditive_reFn {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν) :
    IsCountablyAdditive (reFn ν) := by
  intro A hA
  refine (((Complex.continuous_ofReal.comp Complex.continuous_re).tendsto _).comp
    (h A hA)).congr fun N => ?_
  simp [reFn]
theorem isCountablyAdditive_imFn {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν) :
    IsCountablyAdditive (imFn ν) := by
  intro A hA
  refine (((Complex.continuous_ofReal.comp Complex.continuous_im).tendsto _).comp
    (h A hA)).congr fun N => ?_
  simp [imFn]
theorem variation_mono {ν ν' : MeasurableSets X → ℂ} (hle : ∀ A, ‖ν A‖ₑ ≤ ‖ν' A‖ₑ)
    (A : MeasurableSets X) : variation ν A ≤ variation ν' A :=
  iSup_mono fun B => iSup_mono fun _ => iSup_mono fun _ =>
    ENNReal.tsum_le_tsum fun j => hle (B j)
theorem enorm_ofReal_re_le (z : ℂ) : ‖((z.re : ℝ) : ℂ)‖ₑ ≤ ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  exact ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm z)
theorem enorm_ofReal_im_le (z : ℂ) : ‖((z.im : ℝ) : ℂ)‖ₑ ≤ ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  exact ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm z)
theorem isCountablyAdditive_ofFiniteMeasure (M : Measure X) [IsFiniteMeasure M] :
    IsCountablyAdditive fun A : MeasurableSets X => (((M (A : Set X)).toReal : ℝ) : ℂ) := by
  intro A hA
  have hm : ∀ j, MeasurableSet (A j : Set X) := fun j => (A j).2
  have hl := (M.toSignedMeasure.hasSum_of_disjoint_iUnion hm hA).tendsto_sum_nat
  have hv : ∀ j, M.toSignedMeasure (A j : Set X) = (M (A j : Set X)).toReal :=
    fun j => Measure.toSignedMeasure_apply_measurable (A j).2
  have hU : M.toSignedMeasure (⋃ j, (A j : Set X)) = (M (iUnionSets A : Set X)).toReal :=
    Measure.toSignedMeasure_apply_measurable (iUnionSets A).2
  rw [hU] at hl
  simp only [hv] at hl
  refine ((Complex.continuous_ofReal.tendsto _).comp hl).congr fun N => ?_
  simp
theorem isCountablyAdditive_variation {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν) :
    IsCountablyAdditive fun A => (((variation ν A).toReal : ℝ) : ℂ) := by
  have := isFiniteMeasure_vectorVariation (toComplexMeasure ν h)
  have e : (fun A => (((variation ν A).toReal : ℝ) : ℂ)) =
      fun A : MeasurableSets X => (((toComplexMeasure ν h).variation (A : Set X)).toReal : ℂ) :=
    funext fun A => by rw [variation_eq h]
  rw [e]
  exact isCountablyAdditive_ofFiniteMeasure _
theorem isCountablyAdditive_posPart {μ : MeasurableSets X → ℂ} (h : IsCountablyAdditive μ) :
    IsCountablyAdditive (posPart μ) := by
  have e : posPart μ =
      (1 / 2 : ℂ) • ((fun A => (((variation μ A).toReal : ℝ) : ℂ)) + μ) := rfl
  rw [e]
  exact isCountablyAdditive_smul _
    (isCountablyAdditive_add (isCountablyAdditive_variation h) h)
theorem isCountablyAdditive_negPart {μ : MeasurableSets X → ℂ} (h : IsCountablyAdditive μ) :
    IsCountablyAdditive (negPart μ) := by
  have e : negPart μ = (1 / 2 : ℂ) •
      ((fun A => (((variation μ A).toReal : ℝ) : ℂ)) + (-1 : ℂ) • μ) := by
    funext A
    simp [negPart, sub_eq_add_neg]
  rw [e]
  exact isCountablyAdditive_smul _ (isCountablyAdditive_add (isCountablyAdditive_variation h)
    (isCountablyAdditive_smul _ h))
theorem isNonneg_posPart {μ : MeasurableSets X → ℂ} (h : IsCountablyAdditive μ)
    (hr : ∀ A, (μ A).im = 0) : IsNonneg (posPart μ) := by
  intro A
  have h1 := norm_le_variation_toReal h A
  have h2 := Complex.abs_re_le_norm (μ A)
  have h3 := neg_abs_le (μ A).re
  simp only [posPart, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, hr A]
  norm_num
  linarith
theorem isNonneg_negPart {μ : MeasurableSets X → ℂ} (h : IsCountablyAdditive μ)
    (hr : ∀ A, (μ A).im = 0) : IsNonneg (negPart μ) := by
  intro A
  have h1 := norm_le_variation_toReal h A
  have h2 := Complex.abs_re_le_norm (μ A)
  have h3 := le_abs_self (μ A).re
  simp only [negPart, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, hr A]
  norm_num
  linarith
theorem enorm_eq_ofReal_re {ν : MeasurableSets X → ℂ} (hp : IsNonneg ν) (A : MeasurableSets X) :
    ‖ν A‖ₑ = ENNReal.ofReal (ν A).re := by
  have hz : ν A = ((ν A).re : ℂ) := Complex.ext (by simp) (by simp [(hp A).1])
  have hn : ‖ν A‖ = (ν A).re := by
    conv_lhs => rw [hz]
    rw [Complex.norm_real, Real.norm_of_nonneg (hp A).2]
  rw [← ofReal_norm, hn]
theorem variation_eq_of_nonneg {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    (hp : IsNonneg ν) (A : MeasurableSets X) :
    variation ν A = ENNReal.ofReal (ν A).re := by
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hd => iSup_le fun hu => ?_
    have hre : HasSum (fun j => (ν (B j)).re) (ν (iUnionSets B)).re :=
      Complex.reCLM.hasSum (hasSum_iUnion h hd)
    refine le_of_eq ?_
    calc ∑' j, ‖ν (B j)‖ₑ = ∑' j, ENNReal.ofReal (ν (B j)).re :=
          tsum_congr fun j => enorm_eq_ofReal_re hp _
      _ = ENNReal.ofReal (∑' j, (ν (B j)).re) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun j => (hp _).2) hre.summable).symm
      _ = ENNReal.ofReal (ν A).re := by rw [hre.tsum_eq, hu]
  · rw [← enorm_eq_ofReal_re hp]
    exact enorm_le_variation h A
theorem nonnegToMeasure_eq {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    (hp : IsNonneg ν) : nonnegToMeasure ν = (toComplexMeasure ν h).variation :=
  toMeasure_eq _ fun A => by
    rw [← variation_eq h, variation_eq_of_nonneg h hp]
theorem isFiniteMeasure_nonnegToMeasure {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    (hp : IsNonneg ν) : IsFiniteMeasure (nonnegToMeasure ν) := by
  rw [nonnegToMeasure_eq h hp]
  exact isFiniteMeasure_vectorVariation _
theorem nonnegToMeasure_real {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    (hp : IsNonneg ν) (A : MeasurableSets X) :
    (nonnegToMeasure ν).real (A : Set X) = (ν A).re := by
  rw [nonnegToMeasure_eq h hp, Measure.real, ← variation_eq h,
    variation_eq_of_nonneg h hp, ENNReal.toReal_ofReal (hp A).2]
theorem isFiniteNonnegMeasure_of_nonneg {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    (hp : IsNonneg ν) : IsFiniteNonnegMeasure ν := by
  have := isFiniteMeasure_vectorVariation (toComplexMeasure ν h)
  exact ⟨h, hp, isFiniteMeasureValues_of_eq (toComplexMeasure ν h).variation fun A => by
    rw [← variation_eq h, variation_eq_of_nonneg h hp]⟩
theorem reFn_im (ν : MeasurableSets X → ℂ) (A : MeasurableSets X) : (reFn ν A).im = 0 := by
  simp [reFn]
theorem imFn_im (ν : MeasurableSets X → ℂ) (A : MeasurableSets X) : (imFn ν A).im = 0 := by
  simp [imFn]
def rePosMeasure (ν : MeasurableSets X → ℂ) : Measure X :=
  nonnegToMeasure (posPart (reFn ν))
def reNegMeasure (ν : MeasurableSets X → ℂ) : Measure X :=
  nonnegToMeasure (negPart (reFn ν))
def imPosMeasure (ν : MeasurableSets X → ℂ) : Measure X :=
  nonnegToMeasure (posPart (imFn ν))
def imNegMeasure (ν : MeasurableSets X → ℂ) : Measure X :=
  nonnegToMeasure (negPart (imFn ν))
theorem integralWith_eq (ν : MeasurableSets X → ℂ) (F : X → ℂ) :
    integralWith ν F = ∫ x, F x ∂(rePosMeasure ν) - ∫ x, F x ∂(reNegMeasure ν)
      + Complex.I * ∫ x, F x ∂(imPosMeasure ν) - Complex.I * ∫ x, F x ∂(imNegMeasure ν) :=
  rfl
theorem isFiniteMeasure_parts {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν) :
    IsFiniteMeasure (rePosMeasure ν) ∧ IsFiniteMeasure (reNegMeasure ν) ∧
      IsFiniteMeasure (imPosMeasure ν) ∧ IsFiniteMeasure (imNegMeasure ν) :=
  ⟨isFiniteMeasure_nonnegToMeasure (isCountablyAdditive_posPart (isCountablyAdditive_reFn h))
      (isNonneg_posPart (isCountablyAdditive_reFn h) (reFn_im ν)),
    isFiniteMeasure_nonnegToMeasure (isCountablyAdditive_negPart (isCountablyAdditive_reFn h))
      (isNonneg_negPart (isCountablyAdditive_reFn h) (reFn_im ν)),
    isFiniteMeasure_nonnegToMeasure
      (isCountablyAdditive_posPart (isCountablyAdditive_imFn h))
      (isNonneg_posPart (isCountablyAdditive_imFn h) (imFn_im ν)),
    isFiniteMeasure_nonnegToMeasure
      (isCountablyAdditive_negPart (isCountablyAdditive_imFn h))
      (isNonneg_negPart (isCountablyAdditive_imFn h) (imFn_im ν))⟩
theorem posPart_sub_negPart (μ : MeasurableSets X → ℂ) (A : MeasurableSets X) :
    posPart μ A - negPart μ A = μ A := by
  simp only [posPart, negPart]
  ring
theorem apply_eq_parts {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    (A : MeasurableSets X) :
    ν A = (((rePosMeasure ν).real (A : Set X) - (reNegMeasure ν).real (A : Set X) : ℝ) : ℂ) +
      Complex.I *
        (((imPosMeasure ν).real (A : Set X) - (imNegMeasure ν).real (A : Set X) : ℝ) : ℂ) := by
  have hr := isCountablyAdditive_reFn h
  have hi := isCountablyAdditive_imFn h
  have e1 : (rePosMeasure ν).real (A : Set X) -
      (reNegMeasure ν).real (A : Set X) = (ν A).re := by
    rw [rePosMeasure, reNegMeasure,
      nonnegToMeasure_real (isCountablyAdditive_posPart hr)
        (isNonneg_posPart hr (reFn_im ν)),
      nonnegToMeasure_real (isCountablyAdditive_negPart hr)
        (isNonneg_negPart hr (reFn_im ν)),
      ← Complex.sub_re, posPart_sub_negPart]
    simp [reFn]
  have e2 : (imPosMeasure ν).real (A : Set X) -
      (imNegMeasure ν).real (A : Set X) = (ν A).im := by
    rw [imPosMeasure, imNegMeasure,
      nonnegToMeasure_real (isCountablyAdditive_posPart hi)
        (isNonneg_posPart hi (imFn_im ν)),
      nonnegToMeasure_real (isCountablyAdditive_negPart hi)
        (isNonneg_negPart hi (imFn_im ν)),
      ← Complex.sub_re, posPart_sub_negPart]
    simp [imFn]
  rw [e1, e2, mul_comm, Complex.re_add_im]
theorem integrable_of_isBoundedMeasurable (M : Measure X) [IsFiniteMeasure M] {F : X → ℂ}
    (hF : IsBoundedMeasurable F) : Integrable F M := by
  obtain ⟨hm, C, hC⟩ := hF
  exact Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hC)
theorem integral_simpleFunc_eq_sum (M : Measure X) [IsFiniteMeasure M] (s : SimpleFunc X ℂ) :
    ∫ x, s x ∂M = ∑ c ∈ s.range, ((M.real (s ⁻¹' {c}) : ℝ) : ℂ) * c := by
  rw [← SimpleFunc.integral_eq_integral s (SimpleFunc.integrable_of_isFiniteMeasure s),
    SimpleFunc.integral_eq]
  exact Finset.sum_congr rfl fun c _ => Complex.real_smul
theorem integralWith_simpleFunc {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    (s : SimpleFunc X ℂ) :
    integralWith ν s = ∑ c ∈ s.range, c * ν ⟨s ⁻¹' {c}, s.measurableSet_fiber c⟩ := by
  obtain ⟨i1, i2, i3, i4⟩ := isFiniteMeasure_parts h
  rw [integralWith_eq, integral_simpleFunc_eq_sum, integral_simpleFunc_eq_sum,
    integral_simpleFunc_eq_sum, integral_simpleFunc_eq_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e := apply_eq_parts h ⟨s ⁻¹' {c}, s.measurableSet_fiber c⟩
  simp only at e
  rw [e]
  push_cast
  ring
theorem norm_integralWith_simpleFunc_le {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    (s : SimpleFunc X ℂ) :
    ‖integralWith ν s‖ ≤ ∫ x, ‖s x‖ ∂((toComplexMeasure ν h).variation) := by
  have := isFiniteMeasure_vectorVariation (toComplexMeasure ν h)
  have hI : ∫ x, ‖s x‖ ∂((toComplexMeasure ν h).variation) =
      ∑ c ∈ s.range, (toComplexMeasure ν h).variation.real (s ⁻¹' {c}) * ‖c‖ := by
    have e := SimpleFunc.map_integral (μ := (toComplexMeasure ν h).variation) s (fun z => ‖z‖)
      (SimpleFunc.integrable_of_isFiniteMeasure s) (by simp)
    rw [SimpleFunc.integral_eq_integral (s.map fun z => ‖z‖)
      (SimpleFunc.integrable_of_isFiniteMeasure _)] at e
    simpa [smul_eq_mul] using e
  rw [hI, integralWith_simpleFunc h]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [norm_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg c)
  have e := norm_le_variation_toReal h ⟨s ⁻¹' {c}, s.measurableSet_fiber c⟩
  rwa [variation_eq h] at e
theorem exists_simpleFunc_approx {F : X → ℂ} (hF : IsBoundedMeasurable F) :
    ∃ (s : ℕ → SimpleFunc X ℂ) (C : ℝ), (∀ n x, ‖s n x‖ ≤ C) ∧
      ∀ x, Tendsto (fun n => s n x) atTop (𝓝 (F x)) := by
  obtain ⟨hm, C, hC⟩ := hF
  have hs : StronglyMeasurable F := hm.stronglyMeasurable
  exact ⟨hs.approxBounded (max C 0), max C 0,
    fun n x => hs.norm_approxBounded_le (le_max_right _ _) n x,
    fun x => hs.tendsto_approxBounded_of_norm_le ((hC x).trans (le_max_left _ _))⟩
theorem tendsto_integral_of_bounded_of_finite {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (M : Measure X) [IsFiniteMeasure M] {F : X → E} {Fs : ℕ → X → E}
    (hm : ∀ᶠ j in atTop, AEStronglyMeasurable (Fs j) M) (C : ℝ)
    (hb : ∀ᶠ j in atTop, ∀ x, ‖Fs j x‖ ≤ C)
    (hl : ∀ x, Tendsto (fun j => Fs j x) atTop (𝓝 (F x))) :
    Tendsto (fun j => ∫ x, Fs j x ∂M) atTop (𝓝 (∫ x, F x ∂M)) :=
  tendsto_integral_filter_of_dominated_convergence (fun _ => C) hm
    (hb.mono fun _ hj => Eventually.of_forall hj) (integrable_const C) (Eventually.of_forall hl)
theorem tendsto_integralWith_of_bounded {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    {F : X → ℂ} {Fs : ℕ → X → ℂ} (hm : ∀ᶠ j in atTop, Measurable (Fs j)) (C : ℝ)
    (hb : ∀ᶠ j in atTop, ∀ x, ‖Fs j x‖ ≤ C)
    (hl : ∀ x, Tendsto (fun j => Fs j x) atTop (𝓝 (F x))) :
    Tendsto (fun j => integralWith ν (Fs j)) atTop (𝓝 (integralWith ν F)) := by
  obtain ⟨i1, i2, i3, i4⟩ := isFiniteMeasure_parts h
  have hm' : ∀ M : Measure X, ∀ᶠ j in atTop, AEStronglyMeasurable (Fs j) M :=
    fun M => hm.mono fun _ hj => hj.aestronglyMeasurable
  simp only [integralWith_eq]
  exact (((tendsto_integral_of_bounded_of_finite _ (hm' _) C hb hl).sub
    (tendsto_integral_of_bounded_of_finite _ (hm' _) C hb hl)).add
      ((tendsto_integral_of_bounded_of_finite _ (hm' _) C hb hl).const_mul _)).sub
        ((tendsto_integral_of_bounded_of_finite _ (hm' _) C hb hl).const_mul _)
theorem tendsto_integralWith_simpleFunc {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    {F : X → ℂ} {s : ℕ → SimpleFunc X ℂ} {C : ℝ} (hb : ∀ n x, ‖s n x‖ ≤ C)
    (hl : ∀ x, Tendsto (fun n => s n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => integralWith ν (s n)) atTop (𝓝 (integralWith ν F)) :=
  tendsto_integralWith_of_bounded h (Fs := fun n => s n)
    (Eventually.of_forall fun n => (s n).measurable) C (Eventually.of_forall hb) hl
theorem norm_integralWith_le {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν) {F : X → ℂ}
    (hF : IsBoundedMeasurable F) :
    ‖integralWith ν F‖ ≤ ∫ x, ‖F x‖ ∂(toMeasure (variation ν)) := by
  obtain ⟨s, C, hb, hl⟩ := exists_simpleFunc_approx hF
  have := isFiniteMeasure_vectorVariation (toComplexMeasure ν h)
  rw [toMeasure_variation h]
  have t1 := tendsto_integralWith_simpleFunc h hb hl
  have t2 : Tendsto (fun n => ∫ x, ‖s n x‖ ∂((toComplexMeasure ν h).variation)) atTop
      (𝓝 (∫ x, ‖F x‖ ∂((toComplexMeasure ν h).variation))) :=
    tendsto_integral_of_bounded_of_finite _
      (Eventually.of_forall fun n => (s n).measurable.norm.aestronglyMeasurable) C
      (Eventually.of_forall fun n x => by simpa using hb n x) fun x => (hl x).norm
  exact le_of_tendsto_of_tendsto' t1.norm t2 fun n => norm_integralWith_simpleFunc_le h (s n)
theorem integral_norm_le_iSup_mul {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    {F : X → ℂ} (hF : IsBoundedMeasurable F) :
    ∫ x, ‖F x‖ ∂(toMeasure (variation ν)) ≤
      (⨆ x, ‖F x‖) * (variation ν ⟨Set.univ, MeasurableSet.univ⟩).toReal := by
  have := isFiniteMeasure_vectorVariation (toComplexMeasure ν h)
  rw [toMeasure_variation h, variation_eq h]
  have hint := (integrable_of_isBoundedMeasurable (toComplexMeasure ν h).variation hF).norm
  obtain ⟨hm, C, hC⟩ := hF
  have hbdd : BddAbove (Set.range fun x => ‖F x‖) := ⟨C, by
    rintro _ ⟨x, rfl⟩
    exact hC x⟩
  calc ∫ x, ‖F x‖ ∂((toComplexMeasure ν h).variation)
      ≤ ∫ _, (⨆ x, ‖F x‖) ∂((toComplexMeasure ν h).variation) :=
        integral_mono hint (integrable_const _) fun x => le_ciSup hbdd x
    _ = _ := by
        rw [integral_const, smul_eq_mul, mul_comm]
        rfl
theorem integralWith_add {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν) {F G : X → ℂ}
    (hF : IsBoundedMeasurable F) (hG : IsBoundedMeasurable G) :
    integralWith ν (F + G) = integralWith ν F + integralWith ν G := by
  obtain ⟨i1, i2, i3, i4⟩ := isFiniteMeasure_parts h
  have e : ∀ (M : Measure X) [IsFiniteMeasure M],
      ∫ x, (F + G) x ∂M = ∫ x, F x ∂M + ∫ x, G x ∂M :=
    fun M _ => MeasureTheory.integral_add (integrable_of_isBoundedMeasurable M hF)
      (integrable_of_isBoundedMeasurable M hG)
  simp only [integralWith_eq, e]
  ring
theorem integralWith_smul (ν : MeasurableSets X → ℂ) (c : ℂ) (F : X → ℂ) :
    integralWith ν (c • F) = c * integralWith ν F := by
  simp only [integralWith_eq, Pi.smul_apply, smul_eq_mul, MeasureTheory.integral_const_mul]
  ring
theorem integralWith_indicator_one {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    (A : MeasurableSets X) :
    integralWith ν ((A : Set X).indicator fun _ => 1) = ν A := by
  obtain ⟨i1, i2, i3, i4⟩ := isFiniteMeasure_parts h
  rw [integralWith_eq, MeasureTheory.integral_indicator_const _ A.2,
    MeasureTheory.integral_indicator_const _ A.2, MeasureTheory.integral_indicator_const _ A.2,
    MeasureTheory.integral_indicator_const _ A.2]
  conv_rhs => rw [apply_eq_parts h A]
  simp only [Complex.real_smul, mul_one]
  push_cast
  ring
theorem integralWith_add_measure {ν ν' : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    (h' : IsCountablyAdditive ν') {F : X → ℂ} (hF : IsBoundedMeasurable F) :
    integralWith (ν + ν') F = integralWith ν F + integralWith ν' F := by
  obtain ⟨s, C, hb, hl⟩ := exists_simpleFunc_approx hF
  have hs := isCountablyAdditive_add h h'
  have e : ∀ n, integralWith ν (s n) + integralWith ν' (s n) = integralWith (ν + ν') (s n) := by
    intro n
    rw [integralWith_simpleFunc hs, integralWith_simpleFunc h, integralWith_simpleFunc h',
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by simp [mul_add]
  exact tendsto_nhds_unique (tendsto_integralWith_simpleFunc hs hb hl)
    (((tendsto_integralWith_simpleFunc h hb hl).add
      (tendsto_integralWith_simpleFunc h' hb hl)).congr e)
theorem integralWith_smul_measure {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν) (c : ℂ)
    {F : X → ℂ} (hF : IsBoundedMeasurable F) :
    integralWith (c • ν) F = c * integralWith ν F := by
  obtain ⟨s, C, hb, hl⟩ := exists_simpleFunc_approx hF
  have hs := isCountablyAdditive_smul c h
  have e : ∀ n, c * integralWith ν (s n) = integralWith (c • ν) (s n) := by
    intro n
    rw [integralWith_simpleFunc hs, integralWith_simpleFunc h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  exact tendsto_nhds_unique (tendsto_integralWith_simpleFunc hs hb hl)
    (((tendsto_integralWith_simpleFunc h hb hl).const_mul c).congr e)
theorem variation_add_le (ν ν' : MeasurableSets X → ℂ) (A : MeasurableSets X) :
    variation (ν + ν') A ≤ variation ν A + variation ν' A := by
  refine iSup_le fun B => iSup_le fun hd => iSup_le fun hu => ?_
  calc ∑' j, ‖(ν + ν') (B j)‖ₑ ≤ ∑' j, (‖ν (B j)‖ₑ + ‖ν' (B j)‖ₑ) :=
        ENNReal.tsum_le_tsum fun j => enorm_add_le _ _
    _ = ∑' j, ‖ν (B j)‖ₑ + ∑' j, ‖ν' (B j)‖ₑ := ENNReal.tsum_add
    _ ≤ variation ν A + variation ν' A :=
        add_le_add (le_iSup_of_le B (le_iSup_of_le hd (le_iSup_of_le hu le_rfl)))
          (le_iSup_of_le B (le_iSup_of_le hd (le_iSup_of_le hu le_rfl)))
theorem variation_smul (ν : MeasurableSets X → ℂ) (c : ℂ) (A : MeasurableSets X) :
    variation (c • ν) A = ‖c‖ₑ * variation ν A := by
  simp only [variation, ENNReal.mul_iSup, ← ENNReal.tsum_mul_left, Pi.smul_apply, smul_eq_mul,
    enorm_mul]
theorem integralWith_eq_integral_of_nonneg {ν : MeasurableSets X → ℂ} (h : IsCountablyAdditive ν)
    (hp : IsNonneg ν) (F : X → ℂ) :
    integralWith ν F = ∫ x, F x ∂(nonnegToMeasure ν) := by
  have hz : ∀ A, ((ν A).re : ℂ) = ν A :=
    fun A => Complex.ext (by simp) (by simp [(hp A).1])
  have hre : reFn ν = ν := funext hz
  have him : imFn ν = 0 :=
    funext fun A => by simp [imFn, (hp A).1]
  have hpos : posPart ν = ν := by
    funext A
    simp only [posPart, variation_eq_of_nonneg h hp, ENNReal.toReal_ofReal (hp A).2, hz]
    ring
  have hneg : negPart ν = 0 := by
    funext A
    simp only [negPart, variation_eq_of_nonneg h hp, ENNReal.toReal_ofReal (hp A).2, hz]
    simp
  have htv : ∀ A : MeasurableSets X, variation (0 : MeasurableSets X → ℂ) A = 0 := by
    intro A
    simp [variation]
  have h0 : posPart (0 : MeasurableSets X → ℂ) = 0 := by
    funext A
    simp [posPart, htv]
  have h1 : negPart (0 : MeasurableSets X → ℂ) = 0 := by
    funext A
    simp [negPart, htv]
  have hm0 : nonnegToMeasure (0 : MeasurableSets X → ℂ) = 0 :=
    toMeasure_eq 0 fun A => by simp
  simp only [integralWith, hre, him, hpos, hneg, h0, h1, hm0]
  simp
theorem ofReal_posPart_re_le {μ : MeasurableSets X → ℂ} (h : IsCountablyAdditive μ)
    (hr : ∀ A, (μ A).im = 0) (A : MeasurableSets X) :
    ENNReal.ofReal (posPart μ A).re ≤ variation μ A := by
  refine ENNReal.ofReal_le_of_le_toReal ?_
  have h1 := norm_le_variation_toReal h A
  have h2 := Complex.abs_re_le_norm (μ A)
  have h3 := le_abs_self (μ A).re
  simp only [posPart, Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, hr A]
  norm_num
  linarith
theorem ofReal_negPart_re_le {μ : MeasurableSets X → ℂ} (h : IsCountablyAdditive μ)
    (hr : ∀ A, (μ A).im = 0) (A : MeasurableSets X) :
    ENNReal.ofReal (negPart μ A).re ≤ variation μ A := by
  refine ENNReal.ofReal_le_of_le_toReal ?_
  have h1 := norm_le_variation_toReal h A
  have h2 := Complex.abs_re_le_norm (μ A)
  have h3 := neg_abs_le (μ A).re
  simp only [negPart, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, hr A]
  norm_num
  linarith
theorem complexMeasureFacts : ComplexMeasureFacts := by
  intro X _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ν h
    have := isFiniteMeasure_vectorVariation (toComplexMeasure ν h)
    exact ⟨isFiniteMeasureValues_of_eq _ (variation_eq h), enorm_le_variation h,
      isCountablyAdditive_reFn h, isCountablyAdditive_imFn h,
      variation_mono fun A => enorm_ofReal_re_le _, variation_mono fun A => enorm_ofReal_im_le _⟩
  · intro μ h hr
    exact ⟨isFiniteNonnegMeasure_of_nonneg (isCountablyAdditive_posPart h)
        (isNonneg_posPart h hr),
      isFiniteNonnegMeasure_of_nonneg (isCountablyAdditive_negPart h)
        (isNonneg_negPart h hr),
      ofReal_posPart_re_le h hr, ofReal_negPart_re_le h hr,
      fun A => (posPart_sub_negPart μ A).symm⟩
  · intro ν h hp
    exact ⟨isFiniteNonnegMeasure_of_nonneg h hp, variation_eq_of_nonneg h hp,
      fun F _ => integralWith_eq_integral_of_nonneg h hp F⟩
  · intro ν h
    exact ⟨fun F G hF hG => integralWith_add h hF hG,
      fun c F _ => integralWith_smul ν c F, integralWith_indicator_one h,
      fun F hF => ⟨norm_integralWith_le h hF, integral_norm_le_iSup_mul h hF⟩⟩
  · intro ν ν' c h h'
    exact ⟨isCountablyAdditive_add h h', isCountablyAdditive_smul c h, variation_add_le ν ν',
      variation_smul ν c, fun F hF =>
        ⟨integralWith_add_measure h h' hF, integralWith_smul_measure h c hF⟩⟩
  · intro ν F Fs h _ hFs hC hl
    obtain ⟨C, hC⟩ := hC
    exact tendsto_integralWith_of_bounded h
      ((eventually_ge_atTop 1).mono fun j hj => (hFs j hj).1) C
      ((eventually_ge_atTop 1).mono fun j hj => hC j hj) hl
end YangMills.Construction.SetFunctions.CountablyAdditive
