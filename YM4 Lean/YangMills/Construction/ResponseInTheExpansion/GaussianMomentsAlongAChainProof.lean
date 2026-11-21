import YangMills.Construction.PassageToTheLimit.WhatPassesToTheLimitProof
import YangMills.Construction.ResponseInTheExpansion.GaussianMomentsAlongAChain
import YangMills.Construction.ResponseInTheExpansion.PairingsOfASum
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
namespace YangMills.Construction.ResponseInTheExpansion
section Bounded
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
private def BoundedOn (μ : Measure Ω) (B : Set Ω) (f : Ω → ℝ) : Prop :=
  AEStronglyMeasurable (B.indicator f) μ ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ᵐ ω ∂μ, ω ∈ B → |f ω| ≤ c
private theorem BoundedOn.integrable [IsFiniteMeasure μ] {B : Set Ω} {f : Ω → ℝ} (h : BoundedOn μ B f) :
    Integrable (B.indicator f) μ := by
  obtain ⟨hm, c, hc, hb⟩ := h
  refine Integrable.of_bound hm c ?_
  filter_upwards [hb] with ω hω
  by_cases hB : ω ∈ B
  · rw [Set.indicator_of_mem hB, Real.norm_eq_abs]; exact hω hB
  · rw [Set.indicator_of_notMem hB]; simpa using hc
private theorem BoundedOn.add {B : Set Ω} {f g : Ω → ℝ} (hf : BoundedOn μ B f) (hg : BoundedOn μ B g) :
    BoundedOn μ B (fun ω => f ω + g ω) := by
  obtain ⟨hm, c, hc, hb⟩ := hf
  obtain ⟨hm', c', hc', hb'⟩ := hg
  refine ⟨?_, c + c', by positivity, ?_⟩
  · have : B.indicator (fun ω => f ω + g ω) = B.indicator f + B.indicator g := by
      ext ω; by_cases hB : ω ∈ B <;> simp [hB]
    rw [this]; exact hm.add hm'
  · filter_upwards [hb, hb'] with ω h1 h2 hB
    exact (abs_add_le _ _).trans (add_le_add (h1 hB) (h2 hB))
private theorem BoundedOn.mul {B : Set Ω} {f g : Ω → ℝ} (hf : BoundedOn μ B f) (hg : BoundedOn μ B g) :
    BoundedOn μ B (fun ω => f ω * g ω) := by
  obtain ⟨hm, c, hc, hb⟩ := hf
  obtain ⟨hm', c', hc', hb'⟩ := hg
  refine ⟨?_, c * c', by positivity, ?_⟩
  · have : B.indicator (fun ω => f ω * g ω) = B.indicator f * B.indicator g := by
      ext ω; by_cases hB : ω ∈ B <;> simp [hB]
    rw [this]; exact hm.mul hm'
  · filter_upwards [hb, hb'] with ω h1 h2 hB
    rw [abs_mul]
    exact mul_le_mul (h1 hB) (h2 hB) (abs_nonneg _) hc
private theorem BoundedOn.const {B : Set Ω} (hB : MeasurableSet B) (c : ℝ) : BoundedOn μ B (fun _ => c) := by
  refine ⟨aestronglyMeasurable_const.indicator hB, |c|, abs_nonneg _, ?_⟩
  exact Filter.Eventually.of_forall fun _ _ => le_rfl
private theorem BoundedOn.abs {B : Set Ω} {f : Ω → ℝ} (hf : BoundedOn μ B f) :
    BoundedOn μ B (fun ω => |f ω|) := by
  obtain ⟨hm, c, hc, hb⟩ := hf
  refine ⟨?_, c, hc, ?_⟩
  · have : B.indicator (fun ω => |f ω|) = fun ω => |B.indicator f ω| := by
      ext ω; by_cases hB : ω ∈ B <;> simp [hB]
    rw [this]
    exact hm.norm
  · filter_upwards [hb] with ω h hB
    rw [abs_abs]; exact h hB
private theorem BoundedOn.prod {κ : Type} {B : Set Ω} (hB : MeasurableSet B) (S : Finset κ) {f : κ → Ω → ℝ}
    (hf : ∀ i ∈ S, BoundedOn μ B (f i)) : BoundedOn μ B (fun ω => ∏ i ∈ S, f i ω) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using BoundedOn.const hB 1
  | insert a S ha ih =>
    have h1 := hf a (mem_insert_self _ _)
    have h2 := ih fun i hi => hf i (mem_insert_of_mem hi)
    have := h1.mul h2
    simpa only [prod_insert ha] using this
private theorem BoundedOn.sum {κ : Type} {B : Set Ω} (hB : MeasurableSet B) (S : Finset κ) {f : κ → Ω → ℝ}
    (hf : ∀ i ∈ S, BoundedOn μ B (f i)) : BoundedOn μ B (fun ω => ∑ i ∈ S, f i ω) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using BoundedOn.const hB 0
  | insert a S ha ih =>
    have h1 := hf a (mem_insert_self _ _)
    have h2 := ih fun i hi => hf i (mem_insert_of_mem hi)
    have := h1.add h2
    simpa only [sum_insert ha] using this
private theorem BoundedOn.pow {B : Set Ω} (hB : MeasurableSet B) {f : Ω → ℝ} (hf : BoundedOn μ B f) (n : ℕ) :
    BoundedOn μ B (fun ω => f ω ^ n) := by
  have := BoundedOn.prod (μ := μ) hB (Finset.univ : Finset (Fin n)) (f := fun _ => f) (fun _ _ => hf)
  simpa using this
private theorem BoundedOn.mono {B B' : Set Ω} (hB : MeasurableSet B') (hs : B' ⊆ B) {f : Ω → ℝ}
    (hf : BoundedOn μ B f) : BoundedOn μ B' f := by
  obtain ⟨hm, c, hc, hb⟩ := hf
  refine ⟨?_, c, hc, ?_⟩
  · have : B'.indicator f = B'.indicator (B.indicator f) := by
      rw [Set.indicator_indicator, Set.inter_eq_left.2 hs]
    rw [this]
    exact hm.indicator hB
  · filter_upwards [hb] with ω h hB'
    exact h (hs hB')
private theorem indicatorIntegral_mono [IsFiniteMeasure μ] {B : Set Ω} {f g : Ω → ℝ} (hf : BoundedOn μ B f)
    (hg : BoundedOn μ B g) (h : ∀ᵐ ω ∂μ, ω ∈ B → f ω ≤ g ω) :
    ∫ ω, B.indicator f ω ∂μ ≤ ∫ ω, B.indicator g ω ∂μ := by
  refine integral_mono_ae hf.integrable hg.integrable ?_
  filter_upwards [h] with ω hω
  by_cases hB : ω ∈ B
  · simpa [hB] using hω hB
  · simp [hB]
private theorem indicatorIntegral_add [IsFiniteMeasure μ] {B : Set Ω} {f g : Ω → ℝ} (hf : BoundedOn μ B f)
    (hg : BoundedOn μ B g) :
    ∫ ω, B.indicator (fun ω => f ω + g ω) ω ∂μ = ∫ ω, B.indicator f ω ∂μ + ∫ ω, B.indicator g ω ∂μ := by
  rw [← integral_add hf.integrable hg.integrable]
  congr 1
  ext ω
  by_cases hB : ω ∈ B <;> simp [hB]
private theorem indicatorIntegral_sum [IsFiniteMeasure μ] {κ : Type} {B : Set Ω} (S : Finset κ)
    {f : κ → Ω → ℝ} (hf : ∀ i ∈ S, BoundedOn μ B (f i)) :
    ∫ ω, B.indicator (fun ω => ∑ i ∈ S, f i ω) ω ∂μ = ∑ i ∈ S, ∫ ω, B.indicator (f i) ω ∂μ := by
  rw [← integral_finsetSum S fun i hi => (hf i hi).integrable]
  congr 1
  ext ω
  by_cases hB : ω ∈ B <;> simp [hB]
private theorem indicatorIntegral_const_mul {B : Set Ω} (c : ℝ) (f : Ω → ℝ) :
    ∫ ω, B.indicator (fun ω => c * f ω) ω ∂μ = c * ∫ ω, B.indicator f ω ∂μ := by
  rw [← integral_const_mul]
  congr 1
  ext ω
  by_cases hB : ω ∈ B <;> simp [hB]
private theorem indicatorIntegral_one_le [IsProbabilityMeasure μ] {B : Set Ω} (hB : MeasurableSet B) :
    ∫ ω, B.indicator (fun _ => (1 : ℝ)) ω ∂μ ≤ 1 := by
  rw [integral_indicator_const (1 : ℝ) hB]
  simpa using (measureReal_le_one (μ := μ) (s := B))
private theorem indicatorIntegral_nonneg {B : Set Ω} {f : Ω → ℝ} (h : ∀ ω, ω ∈ B → 0 ≤ f ω) :
    0 ≤ ∫ ω, B.indicator f ω ∂μ := by
  refine integral_nonneg fun ω => ?_
  by_cases hB : ω ∈ B
  · simpa [hB] using h ω hB
  · simp [hB]
private theorem prod_le_one_add_sum_pow {κ : Type} (I : Finset κ) (a : κ → ℝ) (m : ℕ)
    (ha : ∀ i ∈ I, 0 ≤ a i) (hm : I.card ≤ m) : ∏ i ∈ I, a i ≤ 1 + ∑ i ∈ I, (1 + a i ^ m) := by
  classical
  have hpos : ∀ i ∈ I, 0 ≤ 1 + a i ^ m := fun i hi => by have := pow_nonneg (ha i hi) m; linarith
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp
  obtain ⟨i₀, hi₀, hmax⟩ := I.exists_max_image a hI
  have h1 : ∏ i ∈ I, a i ≤ a i₀ ^ I.card := by
    calc ∏ i ∈ I, a i ≤ ∏ _i ∈ I, a i₀ := prod_le_prod ha hmax
      _ = a i₀ ^ I.card := by simp
  have h2 : a i₀ ^ I.card ≤ 1 + a i₀ ^ m := by
    rcases le_total (a i₀) 1 with h | h
    · have := pow_le_one₀ (n := I.card) (ha _ hi₀) h
      have := pow_nonneg (ha _ hi₀) m
      linarith
    · have := pow_le_pow_right₀ h hm
      linarith
  have h3 : 1 + a i₀ ^ m ≤ ∑ i ∈ I, (1 + a i ^ m) := single_le_sum hpos hi₀
  linarith
private theorem indicatorIntegral_prod_le_of_moments [IsProbabilityMeasure μ] {κ : Type} {B : Set Ω}
    (hB : MeasurableSet B) (I : Finset κ) (f : κ → Ω → ℝ) (l : κ → ℝ) (m : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hm : I.card ≤ m) (hf : ∀ i ∈ I, BoundedOn μ B (f i))
    (hf0 : ∀ i ∈ I, ∀ ω, ω ∈ B → 0 ≤ f i ω) (hl : ∀ i ∈ I, 0 < l i)
    (hmom : ∀ i ∈ I, ∫ ω, B.indicator (fun ω => f i ω ^ m) ω ∂μ ≤ c * l i ^ m) :
    ∫ ω, B.indicator (fun ω => ∏ i ∈ I, f i ω) ω ∂μ ≤ ((I.card : ℝ) + 1) * (1 + c) * ∏ i ∈ I, l i := by
  classical
  have hL : 0 < ∏ i ∈ I, l i := prod_pos hl
  have hpt : ∀ ω, ω ∈ B → ∏ i ∈ I, f i ω ≤ (∏ i ∈ I, l i) *
      (1 + ∑ i ∈ I, (1 + (l i ^ m)⁻¹ * f i ω ^ m)) := by
    intro ω hω
    have h := prod_le_one_add_sum_pow I (fun i => f i ω / l i) m
      (fun i hi => div_nonneg (hf0 i hi ω hω) (hl i hi).le) hm
    have e1 : ∏ i ∈ I, f i ω = (∏ i ∈ I, l i) * ∏ i ∈ I, (f i ω / l i) := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun i hi => ?_
      have := (hl i hi).ne'
      field_simp
    rw [e1]
    refine mul_le_mul_of_nonneg_left ?_ hL.le
    refine h.trans (le_of_eq ?_)
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [div_pow]
    have := pow_ne_zero m (hl i hi).ne'
    field_simp
  have hpows : ∀ i ∈ I, BoundedOn μ B (fun ω => 1 + (l i ^ m)⁻¹ * f i ω ^ m) := fun i hi =>
    (BoundedOn.const hB 1).add ((BoundedOn.const hB _).mul ((hf i hi).pow hB m))
  have hR : BoundedOn μ B (fun ω => (∏ i ∈ I, l i) * (1 + ∑ i ∈ I, (1 + (l i ^ m)⁻¹ * f i ω ^ m))) :=
    (BoundedOn.const hB _).mul ((BoundedOn.const hB 1).add (BoundedOn.sum hB I hpows))
  have h1 := indicatorIntegral_mono (BoundedOn.prod hB I hf) hR (Filter.Eventually.of_forall hpt)
  refine h1.trans ?_
  rw [indicatorIntegral_const_mul, indicatorIntegral_add (BoundedOn.const hB 1) (BoundedOn.sum hB I hpows),
    indicatorIntegral_sum I hpows, mul_comm]
  have hterm : ∀ i ∈ I, ∫ ω, B.indicator (fun ω => 1 + (l i ^ m)⁻¹ * f i ω ^ m) ω ∂μ ≤ 1 + c := by
    intro i hi
    have hp : 0 < l i ^ m := pow_pos (hl i hi) m
    rw [indicatorIntegral_add (BoundedOn.const hB 1) ((BoundedOn.const hB _).mul ((hf i hi).pow hB m)),
      indicatorIntegral_const_mul]
    have a1 := indicatorIntegral_one_le (μ := μ) hB
    have a2 : (l i ^ m)⁻¹ * ∫ ω, B.indicator (fun ω => f i ω ^ m) ω ∂μ ≤ c := by
      rw [inv_mul_le_iff₀ hp]
      linarith [hmom i hi, mul_comm c (l i ^ m)]
    linarith
  have hsum : ∑ i ∈ I, ∫ ω, B.indicator (fun ω => 1 + (l i ^ m)⁻¹ * f i ω ^ m) ω ∂μ ≤
      (I.card : ℝ) * (1 + c) := by
    calc _ ≤ ∑ _i ∈ I, (1 + c) := sum_le_sum hterm
      _ = _ := by simp; ring
  have a1 := indicatorIntegral_one_le (μ := μ) hB
  refine mul_le_mul_of_nonneg_right ?_ hL.le
  nlinarith
end Bounded
section Chain
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {q : ℕ} {K X Y ε : ℝ} {M : ℕ} {A : ℕ → Set Ω}
  {Xs : ℕ → ℝ} {Gam Gamc : ℕ → Fin q → Fin q → ℝ} {ζ : ℕ → Fin q → Ω → ℝ} {top : Fin q → Ω → ℝ}
  {s : ℕ → Ω → ℝ}
private theorem tailSum_succ {j : ℕ} (hj : j < M) (i : Fin q) (ω : Ω) :
    tailSum M ζ top j i ω = ζ j i ω + tailSum M ζ top (j + 1) i ω := by
  unfold tailSum
  rw [sum_eq_sum_Ico_succ_bot hj]
  ring
private theorem event_subset_of_le (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) {j u : ℕ}
    (hju : j ≤ u) : A j ⊆ A u := by
  induction u, hju using Nat.le_induction with
  | base => exact subset_rfl
  | succ u _ ih => exact ih.trans (h.event_mono u)
private theorem boundedOn_var (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) {j u : ℕ} (hju : j ≤ u)
    (hu : u < M) (i : Fin q) : BoundedOn μ (A j) (ζ u i) := by
  have hK : 0 ≤ K := by linarith [h.one_le_K]
  have : BoundedOn μ (A u) (ζ u i) := ⟨h.var_aesm u hu i, K * (1 / 2 : ℝ) ^ u, by positivity, h.var_le u hu i⟩
  exact this.mono (h.event_measurable j) (event_subset_of_le h hju)
private theorem boundedOn_top (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) {j : ℕ} (hj : j ≤ M)
    (i : Fin q) : BoundedOn μ (A j) (top i) := by
  have hK : 0 ≤ K := by linarith [h.one_le_K]
  have : BoundedOn μ (A M) (top i) := ⟨h.top_aesm i, K * (1 / 2 : ℝ) ^ M, by positivity, h.top_le i⟩
  exact this.mono (h.event_measurable j) (event_subset_of_le h hj)
private theorem boundedOn_tailSum (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) {j : ℕ} (hj : j ≤ M)
    (i : Fin q) : BoundedOn μ (A j) (tailSum M ζ top j i) := by
  unfold tailSum
  exact (BoundedOn.sum (h.event_measurable j) (Ico j M) fun u hu =>
    boundedOn_var h (mem_Ico.1 hu).1 (mem_Ico.1 hu).2 i).add (boundedOn_top h hj i)
private theorem boundedOn_size (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) {j : ℕ} (hj : j ≤ M) :
    BoundedOn μ (A j) (s j) := by
  have hK : 0 ≤ K := by linarith [h.one_le_K]
  refine ⟨h.size_aesm j hj, K, hK, Filter.Eventually.of_forall fun ω _ => ?_⟩
  rw [abs_of_nonneg (h.size_nonneg j ω)]
  exact h.size_le j ω
private theorem X_pow_le_one (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) (n : ℕ) : X ^ n ≤ 1 :=
  pow_le_one₀ h.X_pos.le h.X_le_one
private theorem X_pow_anti (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) {a b : ℕ} (hab : a ≤ b) :
    X ^ b ≤ X ^ a := pow_le_pow_of_le_one h.X_pos.le h.X_le_one hab
private theorem error_le_quarter_pow (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) :
    ε ≤ (1 / 4 : ℝ) ^ M := by
  have h1 := h.small_error
  have h2 := X_pow_le_one h (4 * q + 4)
  have h4 : (0 : ℝ) < 4 ^ M := by positivity
  have h3 : ε * 4 ^ M ≤ ε * ((M : ℝ) + 1) * 4 ^ M := by
    have : ε * 1 ≤ ε * ((M : ℝ) + 1) := mul_le_mul_of_nonneg_left (by
      have : (0 : ℝ) ≤ M := by positivity
      linarith) h.ε_nonneg
    nlinarith
  have h5 : ε * 4 ^ M ≤ 1 := by linarith
  rw [one_div_pow]
  exact (le_div_iff₀ h4).2 h5
private theorem abs_stepCov_le (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) {u : ℕ} (hu : u < M)
    (i i' : Fin q) : |Gamc u i i'| ≤ (2 * K * (1 / 2 : ℝ) ^ u) ^ 2 := by
  have h1 := h.stepCov_near u hu i i'
  have h2 := h.cov_le u hu i i'
  have h3 : |Gamc u i i'| ≤ |Gam u i i'| + ε := by
    have := abs_sub_abs_le_abs_sub (Gamc u i i') (Gam u i i')
    linarith
  have h4 : ε ≤ (1 / 4 : ℝ) ^ u :=
    (error_le_quarter_pow h).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hu.le)
  have h5 : (2 * K * (1 / 2 : ℝ) ^ u) ^ 2 = 4 * K ^ 2 * (1 / 4 : ℝ) ^ u := by
    rw [mul_pow, mul_pow, ← pow_mul, mul_comm u 2, pow_mul]
    norm_num
  rw [h5]
  have hK := h.one_le_K
  have hp : (0 : ℝ) < (1 / 4 : ℝ) ^ u := by positivity
  have : K + 1 ≤ 4 * K ^ 2 := by nlinarith
  nlinarith
private def levelMomentConst (q : ℕ) (K : ℝ) : ℝ :=
  (4 * K) ^ (2 * q + 2) * ((2 * q + 2).factorial : ℝ) + K * (1 + K) + K ^ (2 * q + 2)
private theorem indicatorIntegral_const_le [IsProbabilityMeasure μ] {B : Set Ω} (hB : MeasurableSet B) {c : ℝ}
    (hc : 0 ≤ c) : ∫ ω, B.indicator (fun _ => c) ω ∂μ ≤ c := by
  have h1 := indicatorIntegral_const_mul (μ := μ) (B := B) c (fun _ => (1 : ℝ))
  simp only [mul_one] at h1
  rw [h1]
  have := indicatorIntegral_one_le (μ := μ) hB
  nlinarith
private theorem moment_var_le (PS : matchingSumPropertiesStatement)
    (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) {u : ℕ} (hu : u < M) (i : Fin q) :
    ∫ ω, (A u).indicator (fun ω => |ζ u i ω| ^ (2 * q + 2)) ω ∂μ ≤
      levelMomentConst q K * (1 / 2 : ℝ) ^ u * X ^ (2 * q + 2) + ε := by
  haveI := h.isProbability
  have hK1 := h.one_le_K
  have hX := h.X_pos
  set Q := 2 * q + 2 with hQ
  have hs := h.step_moment u hu Q (by omega) le_rfl (fun _ => i) ∅
  simp only [prod_empty, mul_one, prod_const, card_univ, Fintype.card_fin, abs_one, one_mul] at hs
  have habs : (fun ω => |ζ u i ω| ^ Q) = fun ω => ζ u i ω ^ Q := by
    ext ω
    have : Even Q := ⟨q + 1, by omega⟩
    exact this.pow_abs _
  rw [habs]
  set I₁ := ∫ ω, (A u).indicator (fun ω => ζ u i ω ^ Q) ω ∂μ
  set I₂ := ∫ ω, (A (u + 1)).indicator (fun _ => (1 : ℝ)) ω ∂μ
  set I₃ := ∫ ω, (A (u + 1)).indicator
    (fun ω => K * (1 / 2 : ℝ) ^ u * (X ^ (Q + 1) + X ^ Q * s (u + 1) ω) + ε) ω ∂μ
  set W := Xs u ^ Q * wickPairingSum (fun a b : Fin Q => Gamc u i i) with hW
  have hB := h.event_measurable (u + 1)
  have hI2 : |I₂| ≤ 1 := by
    rw [abs_of_nonneg (indicatorIntegral_nonneg fun _ _ => zero_le_one)]
    exact indicatorIntegral_one_le hB
  have hp2 : (0 : ℝ) < (1 / 2 : ℝ) ^ u := by positivity
  have hXQ : 0 < X ^ Q := pow_pos hX Q
  have hb0 : 0 ≤ 2 * K * (1 / 2 : ℝ) ^ u := by positivity
  have hP : |wickPairingSum (fun a b : Fin Q => Gamc u i i)| ≤
      (Q.factorial : ℝ) * (2 * K * (1 / 2 : ℝ) ^ u) ^ Q := by
    rw [PS.1 Q]
    have := (PS.2.2 (Fin Q)).2.2.1 Finset.univ (fun _ _ => Gamc u i i) _ hb0
      (fun _ _ => abs_stepCov_le h hu i i)
    simpa using this
  have hXs : |Xs u ^ Q| ≤ (2 * X) ^ Q := by
    rw [abs_of_nonneg (pow_nonneg (h.scale_nonneg u hu) Q)]
    exact pow_le_pow_left₀ (h.scale_nonneg u hu) (h.scale_le u hu) Q
  have hpow : ((1 / 2 : ℝ) ^ u) ^ Q ≤ (1 / 2 : ℝ) ^ u := by
    apply pow_le_of_le_one hp2.le (pow_le_one₀ (by norm_num) (by norm_num))
    omega
  have hWle : |W| ≤ (4 * K) ^ Q * (Q.factorial : ℝ) * (1 / 2 : ℝ) ^ u * X ^ Q := by
    rw [hW, abs_mul]
    calc |Xs u ^ Q| * |wickPairingSum (fun a b : Fin Q => Gamc u i i)|
        ≤ (2 * X) ^ Q * ((Q.factorial : ℝ) * (2 * K * (1 / 2 : ℝ) ^ u) ^ Q) :=
          mul_le_mul hXs hP (abs_nonneg _) (by positivity)
      _ = (4 * K) ^ Q * (Q.factorial : ℝ) * ((1 / 2 : ℝ) ^ u) ^ Q * X ^ Q := by
          rw [mul_pow 2 X, mul_pow (2 * K), mul_pow 2 K, show (4 * K) = 2 * 2 * K by ring, mul_pow (2 * 2),
            mul_pow 2 2]
          ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hXQ.le
          apply mul_le_mul_of_nonneg_left hpow
          positivity
  have hI3 : I₃ ≤ K * (1 + K) * (1 / 2 : ℝ) ^ u * X ^ Q + ε := by
    have hfun : BoundedOn μ (A (u + 1))
        (fun ω => K * (1 / 2 : ℝ) ^ u * (X ^ (Q + 1) + X ^ Q * s (u + 1) ω) + ε) :=
      ((BoundedOn.const hB _).mul ((BoundedOn.const hB _).add ((BoundedOn.const hB _).mul
        (boundedOn_size h hu)))).add (BoundedOn.const hB ε)
    have hc : 0 ≤ K * (1 + K) * (1 / 2 : ℝ) ^ u * X ^ Q + ε := by
      have := h.ε_nonneg
      positivity
    refine (indicatorIntegral_mono hfun (BoundedOn.const hB _) ?_).trans (indicatorIntegral_const_le hB hc)
    refine Filter.Eventually.of_forall fun ω _ => ?_
    have hsk := h.size_le (u + 1) ω
    have hXQ1 : X ^ (Q + 1) ≤ X ^ Q := X_pow_anti h (by omega)
    have : X ^ (Q + 1) + X ^ Q * s (u + 1) ω ≤ (1 + K) * X ^ Q := by nlinarith
    have hm : K * (1 / 2 : ℝ) ^ u * (X ^ (Q + 1) + X ^ Q * s (u + 1) ω) ≤
        K * (1 / 2 : ℝ) ^ u * ((1 + K) * X ^ Q) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hWI : |W * I₂| ≤ |W| := by
    rw [abs_mul]
    have := abs_nonneg W
    nlinarith
  have hfin : I₁ ≤ |W| + I₃ := by
    have h1 := abs_sub_abs_le_abs_sub I₁ (W * I₂)
    have h2 := le_abs_self I₁
    linarith
  have hc₀ : (4 * K) ^ Q * (Q.factorial : ℝ) + K * (1 + K) ≤ levelMomentConst q K := by
    unfold levelMomentConst
    have : 0 ≤ K ^ (2 * q + 2) := by positivity
    linarith
  calc I₁ ≤ |W| + I₃ := hfin
    _ ≤ (4 * K) ^ Q * (Q.factorial : ℝ) * (1 / 2 : ℝ) ^ u * X ^ Q +
          (K * (1 + K) * (1 / 2 : ℝ) ^ u * X ^ Q + ε) := add_le_add hWle hI3
    _ = ((4 * K) ^ Q * (Q.factorial : ℝ) + K * (1 + K)) * (1 / 2 : ℝ) ^ u * X ^ Q + ε := by ring
    _ ≤ _ := by
        have : ((4 * K) ^ Q * (Q.factorial : ℝ) + K * (1 + K)) * ((1 / 2 : ℝ) ^ u * X ^ Q) ≤
            levelMomentConst q K * ((1 / 2 : ℝ) ^ u * X ^ Q) :=
          mul_le_mul_of_nonneg_right hc₀ (by positivity)
        nlinarith
private theorem sum_pow_le_weighted (R : Finset ℕ) (y : ℕ → ℝ) (hy : ∀ u ∈ R, 0 ≤ y u) (τ : ℝ) (hτ : 0 < τ)
    (n : ℕ) :
    (∑ u ∈ R, y u) ^ (n + 1) ≤ (∑ u ∈ R, τ ^ u) ^ n * ∑ u ∈ R, ((τ ^ u)⁻¹) ^ n * y u ^ (n + 1) := by
  rcases R.eq_empty_or_nonempty with rfl | hR
  · simp
  have hT : 0 < ∑ u ∈ R, τ ^ u := sum_pos (fun u _ => pow_pos hτ u) hR
  set T := ∑ u ∈ R, τ ^ u with hTdef
  have hmean := Real.pow_arith_mean_le_arith_mean_pow R (fun u => τ ^ u / T) (fun u => T * y u / τ ^ u)
    (fun u _ => by positivity) (by rw [← sum_div, ← hTdef]; exact div_self hT.ne')
    (fun u hu => by have := hy u hu; positivity) (n + 1)
  have e1 : ∑ u ∈ R, τ ^ u / T * (T * y u / τ ^ u) = ∑ u ∈ R, y u := by
    refine sum_congr rfl fun u _ => ?_
    have := pow_ne_zero u hτ.ne'
    field_simp
  rw [e1] at hmean
  refine hmean.trans (le_of_eq ?_)
  rw [mul_sum]
  refine sum_congr rfl fun u _ => ?_
  have h1 := pow_ne_zero u hτ.ne'
  have h2 := hT.ne'
  rw [div_pow, mul_pow, inv_pow, pow_succ (τ ^ u), pow_succ T]
  field_simp
private def geomRatio (Q : ℕ) : ℝ := (1 / 2 : ℝ) ^ (((2 * Q : ℕ) : ℝ)⁻¹)
private theorem geomRatio_pos (Q : ℕ) : 0 < geomRatio Q := Real.rpow_pos_of_pos (by norm_num) _
private theorem geomRatio_pow (Q : ℕ) (hQ : Q ≠ 0) : geomRatio Q ^ (2 * Q) = 1 / 2 :=
  Real.rpow_inv_natCast_pow (by norm_num) (by omega)
private theorem geomRatio_lt_one (Q : ℕ) (hQ : Q ≠ 0) : geomRatio Q < 1 := by
  apply Real.rpow_lt_one (by norm_num) (by norm_num)
  have : (0 : ℝ) < ((2 * Q : ℕ) : ℝ) := by
    have : 0 < 2 * Q := by omega
    exact_mod_cast this
  positivity
private def geomSumBound (Q : ℕ) : ℝ := (1 - geomRatio Q)⁻¹
private theorem sum_geomRatio_pow_le (Q : ℕ) (hQ : Q ≠ 0) (R : Finset ℕ) :
    ∑ u ∈ R, geomRatio Q ^ u ≤ geomSumBound Q := by
  have h1 := geomRatio_lt_one Q hQ
  have h0 := geomRatio_pos Q
  have := Summable.sum_le_tsum R (fun u _ => (pow_pos h0 u).le) (summable_geometric_of_lt_one h0.le h1)
  rwa [tsum_geometric_of_lt_one h0.le h1] at this
private theorem geomSumBound_nonneg (Q : ℕ) (hQ : Q ≠ 0) : 0 ≤ geomSumBound Q := by
  have h1 := geomRatio_lt_one Q hQ
  unfold geomSumBound
  exact inv_nonneg.2 (by linarith)
private def tailMomentConst (q : ℕ) (K : ℝ) : ℝ :=
  1 + geomSumBound (2 * q + 2) ^ (2 * q + 1) * (levelMomentConst q K * geomSumBound (2 * q + 2) + 1)
private theorem levelMomentConst_nonneg (q : ℕ) (hK : 1 ≤ K) : 0 ≤ levelMomentConst q K := by
  unfold levelMomentConst
  have : 0 ≤ K := by linarith
  positivity
private theorem one_le_tailMomentConst (q : ℕ) (hK : 1 ≤ K) : 1 ≤ tailMomentConst q K := by
  unfold tailMomentConst
  have h1 := geomSumBound_nonneg (2 * q + 2) (by omega)
  have h2 := levelMomentConst_nonneg q hK
  have : 0 ≤ geomSumBound (2 * q + 2) ^ (2 * q + 1) *
      (levelMomentConst q K * geomSumBound (2 * q + 2) + 1) := by positivity
  linarith
private theorem indicatorIntegral_mono_set [IsFiniteMeasure μ] {B B' : Set Ω} (hB : MeasurableSet B)
    (hB' : MeasurableSet B') (hs : B ⊆ B') {f : Ω → ℝ} (hf : BoundedOn μ B' f) (h0 : ∀ ω, 0 ≤ f ω) :
    ∫ ω, B.indicator f ω ∂μ ≤ ∫ ω, B'.indicator f ω ∂μ := by
  refine integral_mono (hf.mono hB hs).integrable hf.integrable fun ω => ?_
  exact Set.indicator_le_indicator_of_subset hs h0 ω
private theorem moment_tailSum_le (PS : matchingSumPropertiesStatement)
    (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) {j : ℕ} (hj : j ≤ M) (i : Fin q) :
    ∫ ω, (A j).indicator (fun ω => |tailSum M ζ top j i ω| ^ (2 * q + 2)) ω ∂μ ≤
      tailMomentConst q K * X ^ (2 * q + 2) := by
  have hprob := h.isProbability
  have hK1 := h.one_le_K
  have hX := h.X_pos
  have hε := h.ε_nonneg
  set Q := 2 * q + 2 with hQ
  have hQ0 : Q ≠ 0 := by omega
  set τ := geomRatio Q with hτdef
  have hτ : 0 < τ := geomRatio_pos Q
  have hτ1 : τ < 1 := geomRatio_lt_one Q hQ0
  set Θ := geomSumBound Q with hΘ
  have hΘ0 : 0 ≤ Θ := geomSumBound_nonneg Q hQ0
  have hB := h.event_measurable j
  set y : ℕ → Ω → ℝ := fun u ω => if u < M then |ζ u i ω| else |top i ω| with hy
  set R := Ico j (M + 1) with hR
  have hy0 : ∀ u ω, 0 ≤ y u ω := by
    intro u ω; simp only [hy]; split_ifs <;> exact abs_nonneg _
  have hyBd : ∀ u ∈ R, BoundedOn μ (A j) (y u) := by
    intro u hu
    obtain ⟨h1, h2⟩ := mem_Ico.1 hu
    by_cases hu' : u < M
    · simpa [hy, hu'] using (boundedOn_var h h1 hu' i).abs
    · simpa [hy, hu'] using (boundedOn_top h hj i).abs
  have hGle : ∀ ω, |tailSum M ζ top j i ω| ≤ ∑ u ∈ R, y u ω := by
    intro ω
    rw [hR, sum_Ico_succ_top hj]
    have e : ∑ u ∈ Ico j M, y u ω = ∑ u ∈ Ico j M, |ζ u i ω| :=
      sum_congr rfl fun u hu => by simp [hy, (mem_Ico.1 hu).2]
    have e2 : y M ω = |top i ω| := by simp [hy]
    rw [e, e2]
    unfold tailSum
    exact (abs_add_le _ _).trans (add_le_add (abs_sum_le_sum_abs _ _) le_rfl)
  have hmom : ∀ u ∈ R, ∫ ω, (A j).indicator (fun ω => y u ω ^ Q) ω ∂μ ≤
      levelMomentConst q K * (1 / 2 : ℝ) ^ u * X ^ Q + ε := by
    intro u hu
    obtain ⟨h1, h2⟩ := mem_Ico.1 hu
    by_cases hu' : u < M
    · have e : (fun ω => y u ω ^ Q) = fun ω => |ζ u i ω| ^ Q := by
        ext ω; simp [hy, hu']
      rw [e]
      refine (indicatorIntegral_mono_set hB (h.event_measurable u) (event_subset_of_le h h1)
        (((boundedOn_var h le_rfl hu' i).abs).pow (h.event_measurable u) Q)
        (fun ω => by positivity)).trans (moment_var_le PS h hu' i)
    · have huM : u = M := by omega
      subst huM
      have e : (fun ω => y u ω ^ Q) = fun ω => |top i ω| ^ Q := by
        ext ω; simp [hy]
      rw [e]
      have hp2 : (1 / 2 : ℝ) ^ u ≤ X ^ Q :=
        h.small_depth.trans (X_pow_anti h (by omega))
      have hp0 : (0 : ℝ) < (1 / 2 : ℝ) ^ u := by positivity
      have hcst : (K * (1 / 2 : ℝ) ^ u) ^ Q ≤ K ^ Q * (1 / 2 : ℝ) ^ u * X ^ Q := by
        rw [mul_pow, mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : Q = 1 + (Q - 1) := by omega
        rw [this, pow_add, pow_one]
        apply mul_le_mul_of_nonneg_left _ hp0.le
        have h3 : ((1 / 2 : ℝ) ^ u) ^ (Q - 1) ≤ (1 / 2 : ℝ) ^ u :=
          pow_le_of_le_one hp0.le (pow_le_one₀ (by norm_num) (by norm_num)) (by omega)
        have h4 : X ^ Q ≤ X ^ (1 + (Q - 1)) := by rw [← this]
        exact h3.trans (hp2.trans h4)
      have hfun := ((boundedOn_top h hj i).abs).pow hB Q
      refine (indicatorIntegral_mono hfun (BoundedOn.const hB ((K * (1 / 2 : ℝ) ^ u) ^ Q)) ?_).trans ?_
      · filter_upwards [h.top_le i] with ω hω hωj
        exact pow_le_pow_left₀ (abs_nonneg _) (hω (event_subset_of_le h hj hωj)) Q
      · refine (indicatorIntegral_const_le hB (by positivity)).trans ?_
        have hc : K ^ Q ≤ levelMomentConst q K := by
          unfold levelMomentConst
          have a1 : 0 ≤ (4 * K) ^ (2 * q + 2) * ((2 * q + 2).factorial : ℝ) := by positivity
          have a2 : 0 ≤ K * (1 + K) := by positivity
          linarith
        have : K ^ Q * (1 / 2 : ℝ) ^ u * X ^ Q ≤ levelMomentConst q K * (1 / 2 : ℝ) ^ u * X ^ Q := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hc hp0.le
        linarith
  have hW1 : ∀ u, ((τ ^ u)⁻¹) ^ (2 * q + 1) * (1 / 2 : ℝ) ^ u ≤ τ ^ u := by
    intro u
    have hτ2 : τ ^ (2 * Q) = 1 / 2 := geomRatio_pow Q hQ0
    have hw : τ ^ u ≠ 0 := pow_ne_zero u hτ.ne'
    have e2 : (1 / 2 : ℝ) ^ u = (τ ^ u) ^ (2 * Q) := by
      rw [← hτ2, ← pow_mul, ← pow_mul, mul_comm]
    have : ((τ ^ u)⁻¹) ^ (2 * q + 1) * (1 / 2 : ℝ) ^ u = (τ ^ u) ^ (2 * q + 2) * τ ^ u := by
      rw [e2]
      calc ((τ ^ u)⁻¹) ^ (2 * q + 1) * (τ ^ u) ^ (2 * Q)
          = ((τ ^ u)⁻¹) ^ (2 * q + 1) * ((τ ^ u) ^ (2 * q + 1) * (τ ^ u) ^ (2 * q + 3)) := by
            rw [← pow_add]; congr 2; omega
        _ = (τ ^ u) ^ (2 * q + 3) := by
            rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hw, one_pow, one_mul]
        _ = _ := pow_succ _ _
    rw [this]
    have h1 : (τ ^ u) ^ (2 * q + 2) ≤ 1 := pow_le_one₀ (pow_pos hτ u).le (pow_le_one₀ hτ.le hτ1.le)
    nlinarith [pow_pos hτ u]
  have hW2 : ∀ u, ((τ ^ u)⁻¹) ^ (2 * q + 1) ≤ 2 ^ u := by
    intro u
    have h2 : (τ⁻¹) ^ (2 * Q) = 2 := by
      rw [inv_pow, geomRatio_pow Q hQ0]; norm_num
    have h1 : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1.le
    have h3 : (τ⁻¹) ^ (2 * q + 1) ≤ 2 := by
      rw [← h2]; exact pow_le_pow_right₀ h1 (by omega)
    calc ((τ ^ u)⁻¹) ^ (2 * q + 1) = ((τ⁻¹) ^ (2 * q + 1)) ^ u := by
          rw [← inv_pow, ← pow_mul, ← pow_mul, mul_comm]
      _ ≤ 2 ^ u := pow_le_pow_left₀ (by positivity) h3 u
  set F : Ω → ℝ := fun ω => Θ ^ (2 * q + 1) * ∑ u ∈ R, ((τ ^ u)⁻¹) ^ (2 * q + 1) * y u ω ^ Q with hF
  have hFBd : BoundedOn μ (A j) F :=
    (BoundedOn.const hB _).mul (BoundedOn.sum hB R fun u hu =>
      (BoundedOn.const hB _).mul ((hyBd u hu).pow hB Q))
  have hpt : ∀ ω, |tailSum M ζ top j i ω| ^ Q ≤ F ω := by
    intro ω
    have h1 := sum_pow_le_weighted R (fun u => y u ω) (fun u _ => hy0 u ω) τ hτ (2 * q + 1)
    have h2 : |tailSum M ζ top j i ω| ^ Q ≤ (∑ u ∈ R, y u ω) ^ Q :=
      pow_le_pow_left₀ (abs_nonneg _) (hGle ω) Q
    refine h2.trans (h1.trans ?_)
    apply mul_le_mul_of_nonneg_right
    · exact pow_le_pow_left₀ (sum_nonneg fun u _ => (pow_pos hτ u).le) (sum_geomRatio_pow_le Q hQ0 R) _
    · exact sum_nonneg fun u _ => mul_nonneg (by positivity) (pow_nonneg (hy0 u ω) Q)
  refine (indicatorIntegral_mono (((boundedOn_tailSum h hj i).abs).pow hB Q) hFBd
    (Filter.Eventually.of_forall fun ω _ => hpt ω)).trans ?_
  rw [hF]
  rw [indicatorIntegral_const_mul, indicatorIntegral_sum R fun u hu =>
    (BoundedOn.const hB _).mul ((hyBd u hu).pow hB Q)]
  have hsum : ∑ u ∈ R, ∫ ω, (A j).indicator (fun ω => ((τ ^ u)⁻¹) ^ (2 * q + 1) * y u ω ^ Q) ω ∂μ ≤
      (levelMomentConst q K * Θ + 1) * X ^ Q := by
    have hterm : ∀ u ∈ R, ∫ ω, (A j).indicator (fun ω => ((τ ^ u)⁻¹) ^ (2 * q + 1) * y u ω ^ Q) ω ∂μ ≤
        levelMomentConst q K * X ^ Q * τ ^ u + 2 ^ M * ε := by
      intro u hu
      rw [indicatorIntegral_const_mul]
      have hw0 : 0 ≤ ((τ ^ u)⁻¹) ^ (2 * q + 1) := by positivity
      have h2u : ((τ ^ u)⁻¹) ^ (2 * q + 1) ≤ 2 ^ M :=
        (hW2 u).trans (pow_le_pow_right₀ (by norm_num) (by have := (mem_Ico.1 hu).2; omega))
      have hc0 := levelMomentConst_nonneg q hK1
      calc _ ≤ ((τ ^ u)⁻¹) ^ (2 * q + 1) * (levelMomentConst q K * (1 / 2 : ℝ) ^ u * X ^ Q + ε) :=
            mul_le_mul_of_nonneg_left (hmom u hu) hw0
        _ = levelMomentConst q K * X ^ Q * (((τ ^ u)⁻¹) ^ (2 * q + 1) * (1 / 2 : ℝ) ^ u) +
              ((τ ^ u)⁻¹) ^ (2 * q + 1) * ε := by ring
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hW1 u) (by positivity))
              (mul_le_mul_of_nonneg_right h2u hε)
    refine (sum_le_sum hterm).trans ?_
    rw [sum_add_distrib, ← mul_sum]
    have hs1 := sum_geomRatio_pow_le Q hQ0 R
    have hcard : (R.card : ℝ) ≤ (M : ℝ) + 1 := by
      have : R.card ≤ M + 1 := by rw [hR, Nat.card_Ico]; omega
      exact_mod_cast this
    have h2M : (2 : ℝ) ^ M ≤ 4 ^ M := pow_le_pow_left₀ (by norm_num) (by norm_num) M
    have hsmall : ∑ _u ∈ R, (2 : ℝ) ^ M * ε ≤ X ^ Q := by
      rw [sum_const, nsmul_eq_mul]
      have : (R.card : ℝ) * (2 ^ M * ε) ≤ ε * ((M : ℝ) + 1) * 4 ^ M := by
        have a1 : (R.card : ℝ) * (2 ^ M * ε) ≤ ((M : ℝ) + 1) * (4 ^ M * ε) :=
          mul_le_mul hcard (mul_le_mul_of_nonneg_right h2M hε) (by positivity) (by positivity)
        linarith
      exact this.trans (h.small_error.trans (X_pow_anti h (by omega)))
    have : levelMomentConst q K * X ^ Q * ∑ u ∈ R, τ ^ u ≤ levelMomentConst q K * X ^ Q * Θ :=
      mul_le_mul_of_nonneg_left hs1 (mul_nonneg (levelMomentConst_nonneg q hK1) (by positivity))
    nlinarith
  calc _ ≤ Θ ^ (2 * q + 1) * ((levelMomentConst q K * Θ + 1) * X ^ Q) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ tailMomentConst q K * X ^ Q := by
        unfold tailMomentConst
        have : 0 ≤ X ^ Q := by positivity
        nlinarith
private def productConst (q : ℕ) (K : ℝ) : ℝ := ((q : ℝ) + 2) * (1 + tailMomentConst q K)
private theorem indicatorIntegral_prod_abs_le (PS : matchingSumPropertiesStatement)
    (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) {j : ℕ} (hj : j ≤ M) (S : Finset (Fin q)) :
    ∫ ω, (A j).indicator (fun ω => ∏ i ∈ S, |tailSum M ζ top j i ω|) ω ∂μ ≤ productConst q K * X ^ S.card := by
  have hprob := h.isProbability
  have hc1 := one_le_tailMomentConst q h.one_le_K
  have hcard : S.card ≤ q := by simpa using card_le_univ S
  have hH := indicatorIntegral_prod_le_of_moments (h.event_measurable j) S
    (fun i ω => |tailSum M ζ top j i ω|) (fun _ => X) (2 * q + 2) (tailMomentConst q K)
    (by linarith) (by omega) (fun i _ => (boundedOn_tailSum h hj i).abs) (fun _ _ _ _ => abs_nonneg _)
    (fun _ _ => h.X_pos) (fun i _ => moment_tailSum_le PS h hj i)
  refine hH.trans ?_
  simp only [prod_const]
  apply mul_le_mul_of_nonneg_right _ (pow_pos h.X_pos _).le
  unfold productConst
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  have : (S.card : ℝ) ≤ q := by exact_mod_cast hcard
  linarith
private theorem indicatorIntegral_size_mul_prod_abs_le (PS : matchingSumPropertiesStatement)
    (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) {j : ℕ} (hj : j ≤ M) (S : Finset (Fin q)) :
    ∫ ω, (A j).indicator (fun ω => s j ω * ∏ i ∈ S, |tailSum M ζ top j i ω|) ω ∂μ ≤
      productConst q K * (K * X * Y) * X ^ S.card := by
  have hprob := h.isProbability
  have hc1 := one_le_tailMomentConst q h.one_le_K
  have hK1 := h.one_le_K
  have hX := h.X_pos
  have hY := h.one_le_Y
  have hcard : S.card ≤ q := by simpa using card_le_univ S
  have hl : 0 < K * X * Y := by
    have : 0 < K := by linarith
    have : 0 < Y := by linarith
    positivity
  have hH := indicatorIntegral_prod_le_of_moments (κ := Option (Fin q)) (h.event_measurable j) S.insertNone
    (fun o ω => o.elim (s j ω) fun i => |tailSum M ζ top j i ω|)
    (fun o => o.elim (K * X * Y) fun _ => X) (2 * q + 2) (tailMomentConst q K) (by linarith)
    (by rw [card_insertNone]; omega)
    (by
      intro o _
      cases o with
      | none => exact boundedOn_size h hj
      | some i => exact (boundedOn_tailSum h hj i).abs)
    (by
      intro o _ ω _
      cases o with
      | none => exact h.size_nonneg j ω
      | some i => exact abs_nonneg _)
    (by
      intro o _
      cases o with
      | none => exact hl
      | some i => exact hX)
    (by
      intro o _
      cases o with
      | none =>
        refine (h.size_moment j hj).trans ?_
        have : 0 ≤ (K * X * Y) ^ (2 * q + 2) := by positivity
        simp only [Option.elim]
        nlinarith
      | some i => exact moment_tailSum_le PS h hj i)
  simp only [prod_insertNone, Option.elim, prod_const, card_insertNone] at hH
  refine hH.trans ?_
  rw [mul_assoc (productConst q K)]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  unfold productConst
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  have : (S.card : ℝ) ≤ q := by exact_mod_cast hcard
  push_cast
  linarith
private theorem step_error_le (PS : matchingSumPropertiesStatement)
    (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) {j : ℕ} (hj : j < M) (r : ℕ) (S : Finset (Fin q)) :
    ∫ ω, (A (j + 1)).indicator (fun ω => |∏ i ∈ S, tailSum M ζ top (j + 1) i ω| *
        (K * (1 / 2 : ℝ) ^ j * (X ^ (r + 1) + X ^ r * s (j + 1) ω) + ε)) ω ∂μ ≤
      (K + K ^ 2) * productConst q K * (1 / 2 : ℝ) ^ j * X ^ (r + S.card + 1) * Y + productConst q K * ε := by
  have hprob := h.isProbability
  have hK1 := h.one_le_K
  have hX := h.X_pos
  have hY := h.one_le_Y
  have hε := h.ε_nonneg
  have hB := h.event_measurable (j + 1)
  have hj' : j + 1 ≤ M := hj
  have hP : BoundedOn μ (A (j + 1)) (fun ω => ∏ i ∈ S, |tailSum M ζ top (j + 1) i ω|) :=
    BoundedOn.prod hB S fun i _ => (boundedOn_tailSum h hj' i).abs
  have hsP : BoundedOn μ (A (j + 1)) (fun ω => s (j + 1) ω * ∏ i ∈ S, |tailSum M ζ top (j + 1) i ω|) :=
    (boundedOn_size h hj').mul hP
  have hexp : ∀ ω, |∏ i ∈ S, tailSum M ζ top (j + 1) i ω| *
        (K * (1 / 2 : ℝ) ^ j * (X ^ (r + 1) + X ^ r * s (j + 1) ω) + ε) =
      (K * (1 / 2 : ℝ) ^ j * X ^ (r + 1) + ε) * (∏ i ∈ S, |tailSum M ζ top (j + 1) i ω|) +
        K * (1 / 2 : ℝ) ^ j * X ^ r * (s (j + 1) ω * ∏ i ∈ S, |tailSum M ζ top (j + 1) i ω|) := by
    intro ω
    rw [abs_prod]
    ring
  simp_rw [hexp]
  rw [indicatorIntegral_add ((BoundedOn.const hB _).mul hP) ((BoundedOn.const hB _).mul hsP),
    indicatorIntegral_const_mul, indicatorIntegral_const_mul]
  have h1 := indicatorIntegral_prod_abs_le PS h hj' S
  have h2 := indicatorIntegral_size_mul_prod_abs_le PS h hj' S
  have hcP : 0 ≤ productConst q K := by
    unfold productConst
    have := one_le_tailMomentConst q hK1
    positivity
  have hc1 : 0 ≤ K * (1 / 2 : ℝ) ^ j * X ^ (r + 1) + ε := by positivity
  have hc2 : 0 ≤ K * (1 / 2 : ℝ) ^ j * X ^ r := by positivity
  have hXS : X ^ S.card ≤ 1 := X_pow_le_one h _
  have e1 : X ^ (r + S.card + 1) = X ^ (r + 1) * X ^ S.card := by ring
  have e2 : X ^ (r + S.card + 1) = X ^ r * X * X ^ S.card := by ring
  calc _ ≤ (K * (1 / 2 : ℝ) ^ j * X ^ (r + 1) + ε) * (productConst q K * X ^ S.card) +
        K * (1 / 2 : ℝ) ^ j * X ^ r * (productConst q K * (K * X * Y) * X ^ S.card) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hc1) (mul_le_mul_of_nonneg_left h2 hc2)
    _ = K * productConst q K * (1 / 2 : ℝ) ^ j * X ^ (r + S.card + 1) +
          K ^ 2 * productConst q K * (1 / 2 : ℝ) ^ j * X ^ (r + S.card + 1) * Y +
        productConst q K * ε * X ^ S.card := by
        rw [show K * productConst q K * (1 / 2 : ℝ) ^ j * X ^ (r + S.card + 1) =
            K * productConst q K * (1 / 2 : ℝ) ^ j * (X ^ (r + 1) * X ^ S.card) by rw [e1],
          show K ^ 2 * productConst q K * (1 / 2 : ℝ) ^ j * X ^ (r + S.card + 1) * Y =
            K ^ 2 * productConst q K * (1 / 2 : ℝ) ^ j * (X ^ r * X * X ^ S.card) * Y by rw [e2]]
        ring
    _ ≤ _ := by
        have a0 : 0 ≤ K * productConst q K * (1 / 2 : ℝ) ^ j * X ^ (r + S.card + 1) := by positivity
        have a1 : K * productConst q K * (1 / 2 : ℝ) ^ j * X ^ (r + S.card + 1) ≤
            K * productConst q K * (1 / 2 : ℝ) ^ j * X ^ (r + S.card + 1) * Y := le_mul_of_one_le_right a0 hY
        have a2 : productConst q K * ε * X ^ S.card ≤ productConst q K * ε :=
          mul_le_of_le_one_right (by positivity) hXS
        linarith
private def tailMoment (μ : Measure Ω) (M : ℕ) (A : ℕ → Set Ω) (ζ : ℕ → Fin q → Ω → ℝ)
    (top : Fin q → Ω → ℝ) (J : Finset (Fin q)) (j : ℕ) : ℝ :=
  ∫ ω, (A j).indicator (fun ω => ∏ i ∈ J, tailSum M ζ top j i ω) ω ∂μ
private def tailCov (M : ℕ) (Xs : ℕ → ℝ) (Gam : ℕ → Fin q → Fin q → ℝ) (j : ℕ) (i i' : Fin q) : ℝ :=
  ∑ u ∈ Ico j M, Xs u ^ 2 * Gam u i i'
omit [MeasurableSpace Ω] in
private theorem sum_Ico_half_pow_le (j M : ℕ) : ∑ u ∈ Ico j M, (1 / 2 : ℝ) ^ u ≤ 2 := by
  have h1 : ∑ u ∈ Ico j M, (1 / 2 : ℝ) ^ u ≤ ∑ u ∈ range M, (1 / 2 : ℝ) ^ u := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro u hu
      exact mem_range.2 (mem_Ico.1 hu).2
    · intro u _ _
      positivity
  exact h1.trans (sum_geometric_two_le M)
private theorem abs_tailSum_le (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) {j : ℕ} (hj : j ≤ M) :
    ∀ᵐ ω ∂μ, ω ∈ A j → ∀ i, |tailSum M ζ top j i ω| ≤ 3 * K := by
  have hK1 := h.one_le_K
  have H1 : ∀ᵐ ω ∂μ, ∀ (u : ℕ) (i : Fin q), u < M → ω ∈ A u → |ζ u i ω| ≤ K * (1 / 2 : ℝ) ^ u := by
    rw [ae_all_iff]
    intro u
    rw [ae_all_iff]
    intro i
    by_cases hu : u < M
    · filter_upwards [h.var_le u hu i] with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun _ h' => absurd h' hu
  have H2 : ∀ᵐ ω ∂μ, ∀ i : Fin q, ω ∈ A M → |top i ω| ≤ K * (1 / 2 : ℝ) ^ M := by
    rw [ae_all_iff]
    exact h.top_le
  filter_upwards [H1, H2] with ω h1 h2 hω i
  unfold tailSum
  have hs : ∑ u ∈ Ico j M, |ζ u i ω| ≤ ∑ u ∈ Ico j M, K * (1 / 2 : ℝ) ^ u := by
    refine sum_le_sum fun u hu => ?_
    obtain ⟨a, b⟩ := mem_Ico.1 hu
    exact h1 u i b (event_subset_of_le h a hω)
  rw [← mul_sum] at hs
  have hs2 : K * ∑ u ∈ Ico j M, (1 / 2 : ℝ) ^ u ≤ K * 2 :=
    mul_le_mul_of_nonneg_left (sum_Ico_half_pow_le j M) (by linarith)
  have ht := h2 i (event_subset_of_le h hj hω)
  have hp : (1 / 2 : ℝ) ^ M ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ht2 : K * (1 / 2 : ℝ) ^ M ≤ K := mul_le_of_le_one_right (by linarith) hp
  calc |∑ u ∈ Ico j M, ζ u i ω + top i ω| ≤ ∑ u ∈ Ico j M, |ζ u i ω| + |top i ω| :=
        (abs_add_le _ _).trans (add_le_add (abs_sum_le_sum_abs _ _) le_rfl)
    _ ≤ 3 * K := by linarith
private theorem abs_tailCov_le (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) (j : ℕ) (i i' : Fin q) :
    |tailCov M Xs Gam j i i'| ≤ (3 * K * X) ^ 2 := by
  have hK1 := h.one_le_K
  have hX := h.X_pos
  unfold tailCov
  have hterm : ∀ u ∈ Ico j M, |Xs u ^ 2 * Gam u i i'| ≤ 4 * K * X ^ 2 * (1 / 2 : ℝ) ^ u := by
    intro u hu
    have hu' := (mem_Ico.1 hu).2
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    have h1 : Xs u ^ 2 ≤ (2 * X) ^ 2 := pow_le_pow_left₀ (h.scale_nonneg u hu') (h.scale_le u hu') 2
    have h2 : |Gam u i i'| ≤ K * (1 / 2 : ℝ) ^ u := by
      refine (h.cov_le u hu' i i').trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) u
    calc Xs u ^ 2 * |Gam u i i'| ≤ (2 * X) ^ 2 * (K * (1 / 2 : ℝ) ^ u) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hs := (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
  rw [← mul_sum] at hs
  have h3 : 4 * K * X ^ 2 * ∑ u ∈ Ico j M, (1 / 2 : ℝ) ^ u ≤ 4 * K * X ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left (sum_Ico_half_pow_le j M) (by positivity)
  have h4 : 4 * K * X ^ 2 * 2 ≤ (3 * K * X) ^ 2 := by
    have : 8 * K ≤ 9 * K ^ 2 := by nlinarith
    have h5 : 0 ≤ X ^ 2 := by positivity
    nlinarith
  linarith
omit [MeasurableSpace Ω] in
private theorem prod_orderEmbOfFin_eq {I : Finset (Fin q)} (F : Fin q → ℝ) :
    ∏ a : Fin I.card, F (I.orderEmbOfFin rfl a) = ∏ i ∈ I, F i := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.LimitPassage.prod_comp_orderEmbOfFin <;> assumption
private theorem tailMoment_split (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) {j : ℕ} (hj : j < M)
    (J : Finset (Fin q)) :
    tailMoment μ M A ζ top J j = ∑ I ∈ J.powerset, ∫ ω, (A j).indicator (fun ω =>
      (∏ i ∈ I, ζ j i ω) * ∏ i ∈ J \ I, tailSum M ζ top (j + 1) i ω) ω ∂μ := by
  have hprob := h.isProbability
  have hB := h.event_measurable j
  have hj' : j + 1 ≤ M := hj
  have hpt : (fun ω => ∏ i ∈ J, tailSum M ζ top j i ω) = fun ω => ∑ I ∈ J.powerset,
      (∏ i ∈ I, ζ j i ω) * ∏ i ∈ J \ I, tailSum M ζ top (j + 1) i ω := by
    funext ω
    rw [prod_congr rfl fun i _ => tailSum_succ hj i ω]
    exact Finset.prod_add _ _ _
  unfold tailMoment
  rw [hpt]
  refine indicatorIntegral_sum _ fun I _ => ?_
  exact (BoundedOn.prod hB I fun i _ => boundedOn_var h le_rfl hj i).mul
    (BoundedOn.prod hB _ fun i _ => (boundedOn_tailSum h hj' i).mono hB (h.event_mono j))
private theorem tailMoment_event_shift (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) {j : ℕ}
    (hj : j < M) (J : Finset (Fin q)) :
    |∫ ω, (A j).indicator (fun ω => ∏ i ∈ J, tailSum M ζ top (j + 1) i ω) ω ∂μ -
        tailMoment μ M A ζ top J (j + 1)| ≤ (3 * K) ^ q * ε := by
  have hprob := h.isProbability
  have hK1 := h.one_le_K
  have hj' : j + 1 ≤ M := hj
  set f : Ω → ℝ := fun ω => ∏ i ∈ J, tailSum M ζ top (j + 1) i ω with hf
  have hB := h.event_measurable j
  have hB' := h.event_measurable (j + 1)
  set D := A (j + 1) \ A j with hD
  have hDm : MeasurableSet D := hB'.diff hB
  have hfB : BoundedOn μ (A (j + 1)) f := BoundedOn.prod hB' J fun i _ => boundedOn_tailSum h hj' i
  have hsplit : (A (j + 1)).indicator f = fun ω => (A j).indicator f ω + D.indicator f ω := by
    funext ω
    by_cases h1 : ω ∈ A j
    · have h2 := h.event_mono j h1
      have h3 : ω ∉ D := fun hd => hd.2 h1
      simp [h1, h2, h3]
    · by_cases h2 : ω ∈ A (j + 1)
      · have h3 : ω ∈ D := ⟨h2, h1⟩
        simp [h1, h2, h3]
      · have h3 : ω ∉ D := fun hd => h2 hd.1
        simp [h1, h2, h3]
  have hfj := (hfB.mono hB (h.event_mono j)).integrable
  have hfD := (hfB.mono hDm Set.diff_subset).integrable
  have heq : tailMoment μ M A ζ top J (j + 1) = ∫ ω, (A j).indicator f ω ∂μ + ∫ ω, D.indicator f ω ∂μ := by
    unfold tailMoment
    rw [← hf, hsplit]
    exact integral_add hfj hfD
  rw [heq]
  have hc : 0 ≤ (3 * K) ^ q := by
    have : 0 ≤ K := by linarith
    positivity
  have hle : ∀ᵐ ω ∂μ, ω ∈ D → |f ω| ≤ (3 * K) ^ q := by
    filter_upwards [abs_tailSum_le h hj'] with ω hω hd
    rw [hf, abs_prod]
    have h3 : 1 ≤ 3 * K := by linarith
    calc ∏ i ∈ J, |tailSum M ζ top (j + 1) i ω| ≤ ∏ _i ∈ J, (3 * K) :=
          prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => hω hd.1 i
      _ = (3 * K) ^ J.card := by simp
      _ ≤ (3 * K) ^ q := pow_le_pow_right₀ h3 (by simpa using card_le_univ J)
  have hDle : μ.real D ≤ ε := by
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans h.measure_compl_le
    intro ω hd h0
    exact hd.2 (event_subset_of_le h (Nat.zero_le j) h0)
  have habs : |∫ ω, D.indicator f ω ∂μ| ≤ (3 * K) ^ q * ε := by
    have h1 : |∫ ω, D.indicator f ω ∂μ| ≤ ∫ ω, |D.indicator f ω| ∂μ := abs_integral_le_integral_abs
    have h2 : ∫ ω, |D.indicator f ω| ∂μ ≤ ∫ ω, D.indicator (fun _ => (3 * K) ^ q) ω ∂μ := by
      refine integral_mono_ae hfD.abs ((integrable_const _).indicator hDm) ?_
      filter_upwards [hle] with ω hω
      by_cases hd : ω ∈ D
      · simpa [hd] using hω hd
      · simp [hd]
    rw [integral_indicator_const _ hDm] at h2
    simp only [smul_eq_mul] at h2
    have h3 : μ.real D * (3 * K) ^ q ≤ ε * (3 * K) ^ q := mul_le_mul_of_nonneg_right hDle hc
    linarith
  have : ∫ ω, (A j).indicator f ω ∂μ - (∫ ω, (A j).indicator f ω ∂μ + ∫ ω, D.indicator f ω ∂μ) =
      -∫ ω, D.indicator f ω ∂μ := by ring
  rw [this, abs_neg]
  exact habs
private theorem matchingSum_perturb (PS : matchingSumPropertiesStatement) (S : Finset (Fin q))
    (A₀ D : Fin q → Fin q → ℝ) (b δ : ℝ) (hb : 1 ≤ b) (hδ0 : 0 ≤ δ) (hδ : δ ≤ b ^ 2)
    (hA : ∀ i j, |A₀ i j| ≤ b ^ 2) (hD : ∀ i j, |D i j| ≤ δ) :
    |matchingSum S (fun i j => D i j + A₀ i j) - matchingSum S A₀| ≤
      2 ^ q * ((q.factorial : ℝ) ^ 2 * δ * b ^ (2 * q)) := by
  classical
  obtain ⟨hemp, hadd, hbd, hbd1, hsc⟩ := PS.2.2 (Fin q)
  have hb0 : 0 ≤ b := by linarith
  have hq : ∀ T : Finset (Fin q), T.card ≤ q := fun T => by simpa using card_le_univ T
  rw [hadd S D A₀, ← add_sum_erase _ _ (empty_mem_powerset S), hemp, sdiff_empty, one_mul, add_sub_cancel_left]
  have hterm : ∀ I ∈ S.powerset.erase ∅, |matchingSum I D * matchingSum (S \ I) A₀| ≤
      (q.factorial : ℝ) ^ 2 * δ * b ^ (2 * q) := by
    intro I hI
    obtain ⟨hne, hIS⟩ := mem_erase.1 hI
    have hIne : I.Nonempty := nonempty_iff_ne_empty.2 hne
    have h1 := hbd1 I D b δ hb0 hIne hδ hD
    have h2 := hbd (S \ I) A₀ b hb0 hA
    have f1 : ((I.card).factorial : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_le (hq I)
    have f2 : (((S \ I).card).factorial : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_le (hq _)
    rw [abs_mul]
    calc |matchingSum I D| * |matchingSum (S \ I) A₀|
        ≤ ((I.card).factorial * δ * b ^ (I.card - 2)) * (((S \ I).card).factorial * b ^ (S \ I).card) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = ((I.card).factorial * ((S \ I).card).factorial : ℝ) * δ * b ^ (I.card - 2 + (S \ I).card) := by
          rw [pow_add]; ring
      _ ≤ (q.factorial * q.factorial : ℝ) * δ * b ^ (2 * q) := by
          have p1 : b ^ (I.card - 2 + (S \ I).card) ≤ b ^ (2 * q) :=
            pow_le_pow_right₀ hb (by have := hq I; have := hq (S \ I); omega)
          have p2 : ((I.card).factorial * ((S \ I).card).factorial : ℝ) ≤ q.factorial * q.factorial :=
            mul_le_mul f1 f2 (by positivity) (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_right p2 hδ0) p1 (by positivity) (by positivity)
      _ = _ := by ring
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hc : (S.powerset.erase ∅).card ≤ 2 ^ q := by
    calc (S.powerset.erase ∅).card ≤ S.powerset.card := card_le_card (erase_subset _ _)
      _ = 2 ^ S.card := card_powerset S
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (hq S)
  exact_mod_cast hc
private def stepCovConst (q : ℕ) (K : ℝ) : ℝ := 2 ^ q * (q.factorial : ℝ) * (4 * K ^ 2) * (2 * K) ^ q
private def perturbConst (q : ℕ) (K : ℝ) : ℝ := 2 ^ q * ((q.factorial : ℝ) ^ 2 * (2 * K) ^ (2 * q))
private def driftConst (q : ℕ) (K : ℝ) : ℝ := 2 ^ q * perturbConst q K * ((q.factorial : ℝ) * (3 * K) ^ q)
private theorem split_term_le (PS : matchingSumPropertiesStatement)
    (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) {j : ℕ} (hj : j < M) (J I : Finset (Fin q))
    (hIJ : I ⊆ J) (hI : I.Nonempty) (B' : ℝ) (hB' : 0 ≤ B')
    (hIH : |tailMoment μ M A ζ top (J \ I) (j + 1) - matchingSum (J \ I) (tailCov M Xs Gam (j + 1))| ≤
      B' * X ^ ((J \ I).card + 1) * Y) :
    |∫ ω, (A j).indicator (fun ω => (∏ i ∈ I, ζ j i ω) * ∏ i ∈ J \ I, tailSum M ζ top (j + 1) i ω) ω ∂μ -
        matchingSum I (fun a b => Xs j ^ 2 * Gam j a b) * matchingSum (J \ I) (tailCov M Xs Gam (j + 1))| ≤
      ((K + K ^ 2) * productConst q K + stepCovConst q K * B') * (1 / 2 : ℝ) ^ j * X ^ (J.card + 1) * Y +
        (productConst q K + driftConst q K) * ε := by
  classical
  obtain ⟨hemp, hadd, hbd, hbd1, hsc⟩ := PS.2.2 (Fin q)
  have hprob := h.isProbability
  have hK1 := h.one_le_K
  have hK0 : 0 ≤ K := by linarith
  have hX := h.X_pos
  have hX1 := h.X_le_one
  have hY := h.one_le_Y
  have hε := h.ε_nonneg
  have hq : ∀ T : Finset (Fin q), T.card ≤ q := fun T => by simpa using card_le_univ T
  have hr1 : 1 ≤ I.card := card_pos.2 hI
  have hstep := h.step_moment j hj I.card hr1 (by have := hq I; omega) (fun a => I.orderEmbOfFin rfl a) (J \ I)
  have hprod : ∀ ω, ∏ a, ζ j (I.orderEmbOfFin rfl a) ω = ∏ i ∈ I, ζ j i ω :=
    fun ω => prod_orderEmbOfFin_eq (fun i => ζ j i ω)
  beta_reduce at hstep
  simp_rw [hprod] at hstep
  rw [PS.2.1 q I (Gamc j)] at hstep
  have herr := hstep.trans (step_error_le PS h hj I.card (J \ I))
  have hrS0 : I.card + (J \ I).card = J.card := by
    rw [card_sdiff_of_subset hIJ]
    have := card_le_card hIJ
    omega
  rw [hrS0] at herr
  set r := I.card with hr
  set S := J \ I with hS
  have hrS : r + S.card = J.card := hrS0
  set T := ∫ ω, (A j).indicator (fun ω => (∏ i ∈ I, ζ j i ω) * ∏ i ∈ S, tailSum M ζ top (j + 1) i ω) ω ∂μ
  set E := ∫ ω, (A (j + 1)).indicator (fun ω => ∏ i ∈ S, tailSum M ζ top (j + 1) i ω) ω ∂μ with hE
  have hEE : tailMoment μ M A ζ top S (j + 1) = E := rfl
  rw [hEE] at hIH
  set W := matchingSum S (tailCov M Xs Gam (j + 1)) with hW
  set c := Xs j ^ r * matchingSum I (Gamc j) with hc
  have hd : matchingSum I (fun a b => Xs j ^ 2 * Gam j a b) = Xs j ^ r * matchingSum I (Gam j) :=
    hsc I (Gam j) (Xs j)
  rw [hd]
  set d := Xs j ^ r * matchingSum I (Gam j) with hd'
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  have hXsr : |Xs j ^ r| ≤ 2 ^ q * X ^ r := by
    rw [abs_of_nonneg (pow_nonneg (h.scale_nonneg j hj) r)]
    calc Xs j ^ r ≤ (2 * X) ^ r := pow_le_pow_left₀ (h.scale_nonneg j hj) (h.scale_le j hj) r
      _ = 2 ^ r * X ^ r := mul_pow _ _ _
      _ ≤ 2 ^ q * X ^ r := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact pow_le_pow_right₀ (by norm_num) (hq I)
  have h2K : 1 ≤ 2 * K := by linarith
  have hPc : |matchingSum I (Gamc j)| ≤ (q.factorial : ℝ) * (4 * K ^ 2) * (2 * K) ^ q * (1 / 2 : ℝ) ^ j := by
    have hδ : ∀ a b, |Gamc j a b| ≤ 4 * K ^ 2 * (1 / 2 : ℝ) ^ j := by
      intro a b
      refine (abs_stepCov_le h hj a b).trans ?_
      rw [mul_pow, mul_pow]
      have : ((1 / 2 : ℝ) ^ j) ^ 2 ≤ (1 / 2 : ℝ) ^ j :=
        pow_le_of_le_one hp.le (pow_le_one₀ (by norm_num) (by norm_num)) (by norm_num)
      have h4 : (0 : ℝ) ≤ 2 ^ 2 * K ^ 2 := by positivity
      calc 2 ^ 2 * K ^ 2 * ((1 / 2 : ℝ) ^ j) ^ 2 ≤ 2 ^ 2 * K ^ 2 * (1 / 2 : ℝ) ^ j :=
            mul_le_mul_of_nonneg_left this h4
        _ = _ := by ring
    have hle : 4 * K ^ 2 * (1 / 2 : ℝ) ^ j ≤ (2 * K) ^ 2 := by
      have : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h4 : 0 ≤ 4 * K ^ 2 := by positivity
      nlinarith
    have hb := hbd1 I (Gamc j) (2 * K) _ (by linarith) hI hle hδ
    refine hb.trans ?_
    have f1 : ((I.card).factorial : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_le (hq I)
    have p1 : (2 * K) ^ (I.card - 2) ≤ (2 * K) ^ q := pow_le_pow_right₀ h2K (by have := hq I; omega)
    calc ((I.card).factorial : ℝ) * (4 * K ^ 2 * (1 / 2 : ℝ) ^ j) * (2 * K) ^ (I.card - 2)
        ≤ (q.factorial : ℝ) * (4 * K ^ 2 * (1 / 2 : ℝ) ^ j) * (2 * K) ^ q :=
          mul_le_mul (mul_le_mul_of_nonneg_right f1 (by positivity)) p1 (by positivity) (by positivity)
      _ = _ := by ring
  have hcabs : |c| ≤ stepCovConst q K * (1 / 2 : ℝ) ^ j * X ^ r := by
    rw [hc, abs_mul]
    calc |Xs j ^ r| * |matchingSum I (Gamc j)|
        ≤ (2 ^ q * X ^ r) * ((q.factorial : ℝ) * (4 * K ^ 2) * (2 * K) ^ q * (1 / 2 : ℝ) ^ j) :=
          mul_le_mul hXsr hPc (abs_nonneg _) (by positivity)
      _ = _ := by unfold stepCovConst; ring
  have hcd : |c - d| ≤ 2 ^ q * (perturbConst q K * ε) := by
    have hε1 : ε ≤ (2 * K) ^ 2 := by
      have h1 : ε ≤ 1 := (error_le_quarter_pow h).trans (pow_le_one₀ (by norm_num) (by norm_num))
      nlinarith
    have hG : ∀ a b, |Gam j a b| ≤ (2 * K) ^ 2 := by
      intro a b
      refine (h.cov_le j hj a b).trans ?_
      have : (1 / 4 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have hn := matchingSum_perturb PS I (Gam j) (fun a b => Gamc j a b - Gam j a b) (2 * K) ε h2K hε hε1 hG
      (h.stepCov_near j hj)
    have he : (fun a b => Gamc j a b - Gam j a b + Gam j a b) = Gamc j := by
      funext a b; ring
    rw [he] at hn
    have hXr : |Xs j ^ r| ≤ 2 ^ q := by
      refine hXsr.trans ?_
      exact mul_le_of_le_one_right (by positivity) (X_pow_le_one h r)
    have : c - d = Xs j ^ r * (matchingSum I (Gamc j) - matchingSum I (Gam j)) := by rw [hc, hd']; ring
    rw [this, abs_mul]
    refine mul_le_mul hXr ?_ (abs_nonneg _) (by positivity)
    refine hn.trans (le_of_eq ?_)
    unfold perturbConst
    ring
  have hWabs : |W| ≤ (q.factorial : ℝ) * (3 * K) ^ q := by
    have hb := hbd S (tailCov M Xs Gam (j + 1)) (3 * K * X) (by positivity) (abs_tailCov_le h (j + 1))
    refine hb.trans ?_
    have f1 : ((S.card).factorial : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_le (hq S)
    have h3 : 1 ≤ 3 * K := by linarith
    have p1 : (3 * K * X) ^ S.card ≤ (3 * K) ^ q := by
      rw [mul_pow]
      calc (3 * K) ^ S.card * X ^ S.card ≤ (3 * K) ^ S.card * 1 :=
            mul_le_mul_of_nonneg_left (X_pow_le_one h _) (by positivity)
        _ = (3 * K) ^ S.card := mul_one _
        _ ≤ (3 * K) ^ q := pow_le_pow_right₀ h3 (hq S)
    exact mul_le_mul f1 p1 (by positivity) (by positivity)
  have e : T - d * W = (T - c * E) + c * (E - W) + (c - d) * W := by ring
  rw [e]
  have t2 : |c * (E - W)| ≤ stepCovConst q K * B' * (1 / 2 : ℝ) ^ j * X ^ (J.card + 1) * Y := by
    rw [abs_mul]
    have hcG : 0 ≤ stepCovConst q K := by unfold stepCovConst; positivity
    calc |c| * |E - W| ≤ (stepCovConst q K * (1 / 2 : ℝ) ^ j * X ^ r) * (B' * X ^ (S.card + 1) * Y) :=
          mul_le_mul hcabs hIH (abs_nonneg _) (by positivity)
      _ = _ := by rw [← hrS]; ring
  have t3 : |(c - d) * W| ≤ driftConst q K * ε := by
    rw [abs_mul]
    calc |c - d| * |W| ≤ (2 ^ q * (perturbConst q K * ε)) * ((q.factorial : ℝ) * (3 * K) ^ q) :=
          mul_le_mul hcd hWabs (abs_nonneg _) (by unfold perturbConst; positivity)
      _ = _ := by unfold driftConst; ring
  have t0 := abs_add_three (T - c * E) (c * (E - W)) ((c - d) * W)
  calc _ ≤ |T - c * E| + |c * (E - W)| + |(c - d) * W| := t0
    _ ≤ ((K + K ^ 2) * productConst q K * (1 / 2 : ℝ) ^ j * X ^ (J.card + 1) * Y + productConst q K * ε) +
          stepCovConst q K * B' * (1 / 2 : ℝ) ^ j * X ^ (J.card + 1) * Y + driftConst q K * ε :=
        add_le_add (add_le_add herr t2) t3
    _ = _ := by ring
private theorem tailCov_succ {j : ℕ} (hj : j < M) :
    tailCov M Xs Gam j = fun i i' => Xs j ^ 2 * Gam j i i' + tailCov M Xs Gam (j + 1) i i' := by
  funext i i'
  unfold tailCov
  rw [sum_eq_sum_Ico_succ_bot hj]
private theorem wickDefect_step (PS : matchingSumPropertiesStatement)
    (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) {j : ℕ} (hj : j < M) (J : Finset (Fin q))
    (B' : ℝ) (hB' : 0 ≤ B')
    (hIH : ∀ S : Finset (Fin q), S.card < J.card →
      |tailMoment μ M A ζ top S (j + 1) - matchingSum S (tailCov M Xs Gam (j + 1))| ≤
        B' * X ^ (S.card + 1) * Y) :
    |tailMoment μ M A ζ top J j - matchingSum J (tailCov M Xs Gam j)| ≤
      |tailMoment μ M A ζ top J (j + 1) - matchingSum J (tailCov M Xs Gam (j + 1))| +
        2 ^ q * ((K + K ^ 2) * productConst q K + stepCovConst q K * B') * (1 / 2 : ℝ) ^ j *
          X ^ (J.card + 1) * Y +
        ((3 * K) ^ q + 2 ^ q * (productConst q K + driftConst q K)) * ε := by
  classical
  obtain ⟨hemp, hadd, hbd, hbd1, hsc⟩ := PS.2.2 (Fin q)
  have hq : ∀ T : Finset (Fin q), T.card ≤ q := fun T => by simpa using card_le_univ T
  have hε := h.ε_nonneg
  rw [tailMoment_split h hj J, tailCov_succ hj, hadd J _ _, ← add_sum_erase _ _ (empty_mem_powerset J),
    ← add_sum_erase _ _ (empty_mem_powerset J), hemp, sdiff_empty, one_mul]
  simp only [prod_empty, one_mul, sdiff_empty]
  set R := ((K + K ^ 2) * productConst q K + stepCovConst q K * B') * (1 / 2 : ℝ) ^ j * X ^ (J.card + 1) * Y +
    (productConst q K + driftConst q K) * ε with hR
  have hterm : ∀ I ∈ J.powerset.erase ∅,
      |∫ ω, (A j).indicator (fun ω => (∏ i ∈ I, ζ j i ω) * ∏ i ∈ J \ I, tailSum M ζ top (j + 1) i ω) ω ∂μ -
        matchingSum I (fun a b => Xs j ^ 2 * Gam j a b) * matchingSum (J \ I) (tailCov M Xs Gam (j + 1))| ≤
        R := by
    intro I hI
    obtain ⟨hne, hIJ⟩ := mem_erase.1 hI
    have hIJ' := mem_powerset.1 hIJ
    have hIne : I.Nonempty := nonempty_iff_ne_empty.2 hne
    refine split_term_le PS h hj J I hIJ' hIne B' hB' (hIH _ ?_)
    have := card_pos.2 hIne
    rw [card_sdiff_of_subset hIJ']
    have := card_le_card hIJ'
    omega
  have hsum : |∑ I ∈ J.powerset.erase ∅,
        (∫ ω, (A j).indicator (fun ω => (∏ i ∈ I, ζ j i ω) * ∏ i ∈ J \ I, tailSum M ζ top (j + 1) i ω) ω ∂μ -
        matchingSum I (fun a b => Xs j ^ 2 * Gam j a b) * matchingSum (J \ I) (tailCov M Xs Gam (j + 1)))| ≤
        2 ^ q * R := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
    rw [sum_const, nsmul_eq_mul]
    have hc : (J.powerset.erase ∅).card ≤ 2 ^ q := by
      calc (J.powerset.erase ∅).card ≤ J.powerset.card := card_le_card (erase_subset _ _)
        _ = 2 ^ J.card := card_powerset J
        _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (hq J)
    have hc' : ((J.powerset.erase ∅).card : ℝ) ≤ 2 ^ q := by exact_mod_cast hc
    have hR0 : 0 ≤ R := by
      by_cases hJ : (J.powerset.erase ∅).Nonempty
      · obtain ⟨I, hI⟩ := hJ
        exact (abs_nonneg _).trans (hterm I hI)
      · have hK1 := h.one_le_K
        have hK0 : 0 ≤ K := by linarith
        have c1 := one_le_tailMomentConst q hK1
        have hcP : 0 ≤ productConst q K := by unfold productConst; positivity
        have hcG : 0 ≤ stepCovConst q K := by unfold stepCovConst; positivity
        have hcD : 0 ≤ driftConst q K := by unfold driftConst perturbConst; positivity
        have hX := h.X_pos
        have hY : 0 ≤ Y := by linarith [h.one_le_Y]
        rw [hR]
        positivity
    exact mul_le_mul_of_nonneg_right hc' hR0
  have h0 := tailMoment_event_shift h hj J
  set T₀ := ∫ ω, (A j).indicator (fun ω => ∏ i ∈ J, tailSum M ζ top (j + 1) i ω) ω ∂μ
  set E₁ := tailMoment μ M A ζ top J (j + 1)
  set W₁ := matchingSum J (tailCov M Xs Gam (j + 1))
  rw [sum_sub_distrib] at hsum
  set ST := ∑ I ∈ J.powerset.erase ∅, ∫ ω, (A j).indicator (fun ω =>
    (∏ i ∈ I, ζ j i ω) * ∏ i ∈ J \ I, tailSum M ζ top (j + 1) i ω) ω ∂μ
  set SW := ∑ I ∈ J.powerset.erase ∅,
    matchingSum I (fun a b => Xs j ^ 2 * Gam j a b) * matchingSum (J \ I) (tailCov M Xs Gam (j + 1))
  have e : T₀ + ST - (W₁ + SW) = (T₀ - E₁) + (E₁ - W₁) + (ST - SW) := by ring
  rw [e]
  have t0 := abs_add_three (T₀ - E₁) (E₁ - W₁) (ST - SW)
  have eR : 2 ^ q * R = 2 ^ q * ((K + K ^ 2) * productConst q K + stepCovConst q K * B') * (1 / 2 : ℝ) ^ j *
      X ^ (J.card + 1) * Y + 2 ^ q * (productConst q K + driftConst q K) * ε := by rw [hR]; ring
  calc _ ≤ |T₀ - E₁| + |E₁ - W₁| + |ST - SW| := t0
    _ ≤ (3 * K) ^ q * ε + |E₁ - W₁| + 2 ^ q * R := by linarith
    _ = _ := by rw [eR]; ring
private theorem error_mul_le (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) :
    ((M : ℝ) + 1) * ε ≤ X ^ (4 * q + 4) := by
  have h1 := h.small_error
  have hε := h.ε_nonneg
  have h4 : (1 : ℝ) ≤ 4 ^ M := one_le_pow₀ (by norm_num)
  have : ε * ((M : ℝ) + 1) * 1 ≤ ε * ((M : ℝ) + 1) * 4 ^ M :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  linarith
private theorem wickDefect_empty (PS : matchingSumPropertiesStatement)
    (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) (j : ℕ) :
    |tailMoment μ M A ζ top ∅ j - matchingSum ∅ (tailCov M Xs Gam j)| ≤
      1 * X ^ ((∅ : Finset (Fin q)).card + 1) * Y := by
  have hprob := h.isProbability
  obtain ⟨hemp, -⟩ := PS.2.2 (Fin q)
  rw [hemp]
  unfold tailMoment
  simp only [prod_empty]
  rw [integral_indicator_const (1 : ℝ) (h.event_measurable j)]
  simp only [smul_eq_mul, mul_one, card_empty, zero_add, pow_one, one_mul]
  have h1 : μ.real (A j) + μ.real (A j)ᶜ = 1 := by
    simpa using measureReal_add_measureReal_compl (μ := μ) (h.event_measurable j)
  have h2 : μ.real (A j)ᶜ ≤ μ.real (A 0)ᶜ :=
    measureReal_mono (Set.compl_subset_compl.2 (event_subset_of_le h (Nat.zero_le j))) (measure_ne_top _ _)
  have h3 := h.measure_compl_le
  have h0 : 0 ≤ μ.real (A j)ᶜ := measureReal_nonneg
  have h4 := error_mul_le h
  have h5 : ε ≤ ((M : ℝ) + 1) * ε := by
    have : (0 : ℝ) ≤ M := by positivity
    nlinarith
  have h6 : X ^ (4 * q + 4) ≤ X ^ 1 := X_pow_anti h (by omega)
  have hX : 0 < X := h.X_pos
  have hY := h.one_le_Y
  have : μ.real (A j) - 1 = -μ.real (A j)ᶜ := by linarith
  rw [this, abs_neg, abs_of_nonneg h0]
  have h7 : X ≤ X * Y := le_mul_of_one_le_right hX.le hY
  linarith
private theorem wickDefect_top (PS : matchingSumPropertiesStatement)
    (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) (J : Finset (Fin q)) (hJ : J.Nonempty) :
    |tailMoment μ M A ζ top J M - matchingSum J (tailCov M Xs Gam M)| ≤ K ^ q * X ^ (J.card + 1) := by
  obtain ⟨hemp, hadd, hbd, -⟩ := PS.2.2 (Fin q)
  have hprob := h.isProbability
  have hK1 := h.one_le_K
  have hq : J.card ≤ q := by simpa using card_le_univ J
  have hcard : 0 < J.card := card_pos.2 hJ
  have h0 : matchingSum J (tailCov M Xs Gam M) = 0 := by
    have := hbd J (tailCov M Xs Gam M) 0 le_rfl (fun i i' => by simp [tailCov])
    rw [zero_pow hcard.ne', mul_zero] at this
    exact abs_nonpos_iff.1 this
  rw [h0, sub_zero]
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ M := by positivity
  have hc : 0 ≤ K ^ q * (1 / 2 : ℝ) ^ M := by positivity
  have hB := h.event_measurable M
  have hf : BoundedOn μ (A M) (fun ω => ∏ i ∈ J, tailSum M ζ top M i ω) :=
    BoundedOn.prod hB J fun i _ => boundedOn_tailSum h le_rfl i
  have hle : ∀ᵐ ω ∂μ, ω ∈ A M → |∏ i ∈ J, tailSum M ζ top M i ω| ≤ K ^ q * (1 / 2 : ℝ) ^ M := by
    have H2 : ∀ᵐ ω ∂μ, ∀ i : Fin q, ω ∈ A M → |top i ω| ≤ K * (1 / 2 : ℝ) ^ M := by
      rw [ae_all_iff]
      exact h.top_le
    filter_upwards [H2] with ω h2 hω
    rw [abs_prod]
    have hsame : ∀ i, tailSum M ζ top M i ω = top i ω := fun i => by simp [tailSum]
    simp_rw [hsame]
    calc ∏ i ∈ J, |top i ω| ≤ ∏ _i ∈ J, (K * (1 / 2 : ℝ) ^ M) :=
          prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => h2 i hω
      _ = K ^ J.card * ((1 / 2 : ℝ) ^ M) ^ J.card := by simp [mul_pow]
      _ ≤ K ^ q * (1 / 2 : ℝ) ^ M := by
          apply mul_le_mul (pow_le_pow_right₀ hK1 hq) _ (by positivity) (by positivity)
          exact pow_le_of_le_one hp.le (pow_le_one₀ (by norm_num) (by norm_num)) hcard.ne'
  have h1 : |tailMoment μ M A ζ top J M| ≤ K ^ q * (1 / 2 : ℝ) ^ M := by
    unfold tailMoment
    have a1 := abs_integral_le_integral_abs (μ := μ)
      (f := (A M).indicator fun ω => ∏ i ∈ J, tailSum M ζ top M i ω)
    have a2 : ∫ ω, |(A M).indicator (fun ω => ∏ i ∈ J, tailSum M ζ top M i ω) ω| ∂μ ≤
        ∫ ω, (A M).indicator (fun _ => K ^ q * (1 / 2 : ℝ) ^ M) ω ∂μ := by
      refine integral_mono_ae hf.integrable.abs ((integrable_const _).indicator hB) ?_
      filter_upwards [hle] with ω hω
      by_cases hd : ω ∈ A M
      · simpa [hd] using hω hd
      · simp [hd]
    exact a1.trans (a2.trans (indicatorIntegral_const_le hB hc))
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact h.small_depth.trans (X_pow_anti h (by omega))
private theorem wickDefect_bottom (PS : matchingSumPropertiesStatement)
    (h : IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s) :
    |matchingSum Finset.univ (tailCov M Xs Gam 0) -
        X ^ q * wickPairingSum (fun i i' => ∑ u ∈ Finset.range M, Gam u i i')| ≤
      2 ^ q * ((q.factorial : ℝ) ^ 2 * |(2 * K) ^ q|) * X ^ (q + 1) := by
  classical
  obtain ⟨hemp, hadd, hbd, hbd1, hsc⟩ := PS.2.2 (Fin q)
  have hK1 := h.one_le_K
  have hK0 : 0 ≤ K := by linarith
  have hX := h.X_pos
  have hq : ∀ T : Finset (Fin q), T.card ≤ q := fun T => by simpa using card_le_univ T
  set T : Fin q → Fin q → ℝ := fun i i' => ∑ u ∈ Finset.range M, Gam u i i' with hT
  have hsc' := hsc Finset.univ T X
  rw [card_univ, Fintype.card_fin] at hsc'
  rw [PS.1 q T, ← hsc']
  set A₀ : Fin q → Fin q → ℝ := fun i i' => X ^ 2 * T i i' with hA₀
  set D : Fin q → Fin q → ℝ := fun i i' => tailCov M Xs Gam 0 i i' - A₀ i i' with hD
  have hSk : tailCov M Xs Gam 0 = fun i i' => D i i' + A₀ i i' := by
    funext i i'
    simp only [hD]
    ring
  have hhalf : ∀ u : ℕ, (1 / 4 : ℝ) ^ u ≤ (1 / 2 : ℝ) ^ u := fun u =>
    pow_le_pow_left₀ (by norm_num) (by norm_num) u
  have hTle : ∀ i i', |T i i'| ≤ 2 * K := by
    intro i i'
    have a : ∀ u ∈ Finset.range M, |Gam u i i'| ≤ K * (1 / 2 : ℝ) ^ u := fun u hu =>
      (h.cov_le u (mem_range.1 hu) i i').trans (mul_le_mul_of_nonneg_left (hhalf u) hK0)
    have b := (abs_sum_le_sum_abs _ _).trans (sum_le_sum a)
    rw [← mul_sum] at b
    have c : K * ∑ u ∈ Finset.range M, (1 / 2 : ℝ) ^ u ≤ K * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le M) hK0
    simp only [hT]
    linarith
  have hAle : ∀ i i', |A₀ i i'| ≤ (2 * K * X) ^ 2 := by
    intro i i'
    simp only [hA₀]
    rw [abs_mul, abs_of_nonneg (sq_nonneg X)]
    have h5 := hTle i i'
    have h6 : 2 * K ≤ 4 * K ^ 2 := by nlinarith
    have h7 : 0 ≤ X ^ 2 := sq_nonneg X
    calc X ^ 2 * |T i i'| ≤ X ^ 2 * (4 * K ^ 2) := mul_le_mul_of_nonneg_left (h5.trans h6) h7
      _ = _ := by ring
  have hDle : ∀ i i', |D i i'| ≤ (2 * K * X ^ 2) ^ 2 := by
    intro i i'
    have e : D i i' = ∑ u ∈ Finset.range M, (Xs u ^ 2 - X ^ 2) * Gam u i i' := by
      simp only [hD, hA₀, hT, tailCov, Nat.Ico_zero_eq_range, mul_sum]
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun u _ => by ring
    rw [e]
    have a : ∀ u ∈ Finset.range M, |(Xs u ^ 2 - X ^ 2) * Gam u i i'| ≤
        K ^ 2 * X ^ 4 * (1 / 2 : ℝ) ^ u := by
      intro u hu
      have hu' := mem_range.1 hu
      rw [abs_mul]
      have b1 := h.scale_sq_near u hu'
      have b2 := h.cov_le u hu' i i'
      have b3 : ((u : ℝ) + 1) * (1 / 4 : ℝ) ^ u ≤ (1 / 2 : ℝ) ^ u := by
        have c1 : ((u : ℝ) + 1) ≤ 2 ^ u := by
          have := Nat.lt_two_pow_self (n := u)
          exact_mod_cast this
        have c2 : (1 / 4 : ℝ) ^ u = (1 / 2 : ℝ) ^ u * (1 / 2 : ℝ) ^ u := by
          rw [← mul_pow]; norm_num
        have c3 : (2 : ℝ) ^ u * (1 / 2 : ℝ) ^ u = 1 := by
          rw [← mul_pow]; norm_num
        have c4 : (0 : ℝ) < (1 / 2 : ℝ) ^ u := by positivity
        rw [c2]
        calc ((u : ℝ) + 1) * ((1 / 2 : ℝ) ^ u * (1 / 2 : ℝ) ^ u)
            ≤ 2 ^ u * ((1 / 2 : ℝ) ^ u * (1 / 2 : ℝ) ^ u) :=
              mul_le_mul_of_nonneg_right c1 (by positivity)
          _ = (1 / 2 : ℝ) ^ u := by rw [← mul_assoc, c3, one_mul]
      calc |Xs u ^ 2 - X ^ 2| * |Gam u i i'|
          ≤ (K * ((u : ℝ) + 1) * X ^ 4) * (K * (1 / 4 : ℝ) ^ u) :=
            mul_le_mul b1 b2 (abs_nonneg _) (by positivity)
        _ = K ^ 2 * X ^ 4 * (((u : ℝ) + 1) * (1 / 4 : ℝ) ^ u) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left b3 (by positivity)
    have b := (abs_sum_le_sum_abs _ _).trans (sum_le_sum a)
    rw [← mul_sum] at b
    have c : K ^ 2 * X ^ 4 * ∑ u ∈ Finset.range M, (1 / 2 : ℝ) ^ u ≤ K ^ 2 * X ^ 4 * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le M) (by positivity)
    have d : K ^ 2 * X ^ 4 * 2 ≤ (2 * K * X ^ 2) ^ 2 := by
      have : 0 ≤ K ^ 2 * X ^ 4 := by positivity
      nlinarith
    linarith
  rw [hSk, hadd Finset.univ D A₀, ← add_sum_erase _ _ (empty_mem_powerset _), hemp, sdiff_empty, one_mul,
    add_sub_cancel_left]
  have hterm : ∀ I ∈ (Finset.univ : Finset (Fin q)).powerset.erase ∅,
      |matchingSum I D * matchingSum (Finset.univ \ I) A₀| ≤
        (q.factorial : ℝ) ^ 2 * |(2 * K) ^ q| * X ^ (q + 1) := by
    intro I hI
    obtain ⟨hne, -⟩ := mem_erase.1 hI
    have hIne : I.Nonempty := nonempty_iff_ne_empty.2 hne
    have hI1 : 1 ≤ I.card := card_pos.2 hIne
    have b1 := hbd I D (2 * K * X ^ 2) (by positivity) hDle
    have b2 := hbd (Finset.univ \ I) A₀ (2 * K * X) (by positivity) hAle
    have hcard : (Finset.univ \ I : Finset (Fin q)).card = q - I.card := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
    rw [hcard] at b2
    have f1 : ((I.card).factorial : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_le (hq I)
    have f2 : ((q - I.card).factorial : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_le (by omega)
    rw [abs_mul]
    have hqI := hq I
    have h2K : 1 ≤ 2 * K := by linarith
    have eX : (2 * K * X ^ 2) ^ I.card * (2 * K * X) ^ (q - I.card) =
        (2 * K) ^ q * X ^ (q + I.card) := by
      rw [mul_pow, mul_pow, ← pow_mul]
      have p1 : (2 * K) ^ q = (2 * K) ^ I.card * (2 * K) ^ (q - I.card) := by
        rw [← pow_add]; congr 1; omega
      have p2 : X ^ (q + I.card) = X ^ (2 * I.card) * X ^ (q - I.card) := by
        rw [← pow_add]; congr 1; omega
      rw [p1, p2]
      ring
    calc |matchingSum I D| * |matchingSum (Finset.univ \ I) A₀|
        ≤ (((I.card).factorial : ℝ) * (2 * K * X ^ 2) ^ I.card) *
            (((q - I.card).factorial : ℝ) * (2 * K * X) ^ (q - I.card)) :=
          mul_le_mul b1 b2 (abs_nonneg _) (by positivity)
      _ = ((I.card).factorial * (q - I.card).factorial : ℝ) * ((2 * K) ^ q * X ^ (q + I.card)) := by
          rw [← eX]; ring
      _ ≤ (q.factorial * q.factorial : ℝ) * (|(2 * K) ^ q| * X ^ (q + 1)) := by
          apply mul_le_mul (mul_le_mul f1 f2 (by positivity) (by positivity)) _ (by positivity) (by positivity)
          apply mul_le_mul (le_abs_self _) (X_pow_anti h (by omega)) (by positivity) (abs_nonneg _)
      _ = _ := by ring
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_const, nsmul_eq_mul]
  have hc : (((Finset.univ : Finset (Fin q)).powerset.erase ∅).card : ℝ) ≤ 2 ^ q := by
    have : ((Finset.univ : Finset (Fin q)).powerset.erase ∅).card ≤ 2 ^ q := by
      calc _ ≤ (Finset.univ : Finset (Fin q)).powerset.card := card_le_card (erase_subset _ _)
        _ = 2 ^ q := by rw [card_powerset, card_univ, Fintype.card_fin]
    exact_mod_cast this
  calc _ ≤ (2 : ℝ) ^ q * ((q.factorial : ℝ) ^ 2 * |(2 * K) ^ q| * X ^ (q + 1)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring
end Chain
private theorem wickDefect_le (PS : matchingSumPropertiesStatement) (q : ℕ) (K : ℝ) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X Y ε : ℝ) (M : ℕ) (A : ℕ → Set Ω)
      (Xs : ℕ → ℝ) (Gam Gamc : ℕ → Fin q → Fin q → ℝ) (ζ : ℕ → Fin q → Ω → ℝ) (top : Fin q → Ω → ℝ)
      (s : ℕ → Ω → ℝ), IsGaussianChain μ K X Y ε M A Xs Gam Gamc ζ top s →
      ∀ J : Finset (Fin q), J.card ≤ n → ∀ j ≤ M,
        |tailMoment μ M A ζ top J j - matchingSum J (tailCov M Xs Gam j)| ≤ B * X ^ (J.card + 1) * Y := by
  induction n with
  | zero =>
    refine ⟨1, zero_le_one, ?_⟩
    intro Ω _ μ X Y ε M A Xs Gam Gamc ζ top s h J hJ j _
    have : J = ∅ := card_eq_zero.1 (by omega)
    subst this
    exact wickDefect_empty PS h j
  | succ n ih =>
    obtain ⟨B', hB', hih⟩ := ih
    set C₃ := 2 ^ q * ((K + K ^ 2) * productConst q K + stepCovConst q K * B') with hC₃
    set C₄ := (3 * K) ^ q + 2 ^ q * (productConst q K + driftConst q K) with hC₄
    refine ⟨B' + |K ^ q| + 2 * |C₃| + |C₄| + 1, by positivity, ?_⟩
    intro Ω _ μ X Y ε M A Xs Gam Gamc ζ top s h J hJ j hj
    have hX := h.X_pos
    have hY := h.one_le_Y
    have hY0 : 0 ≤ Y := by linarith
    have hε := h.ε_nonneg
    by_cases hJn : J.card ≤ n
    · refine (hih Ω μ X Y ε M A Xs Gam Gamc ζ top s h J hJn j hj).trans ?_
      apply mul_le_mul_of_nonneg_right _ hY0
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have := abs_nonneg (K ^ q)
      have := abs_nonneg C₃
      have := abs_nonneg C₄
      linarith
    have hne : J.Nonempty := card_pos.1 (by omega)
    set P := X ^ (J.card + 1) * Y with hP
    have hP0 : 0 ≤ P := by positivity
    have hdown : ∀ d j, j + d = M → |tailMoment μ M A ζ top J j - matchingSum J (tailCov M Xs Gam j)| ≤
        |tailMoment μ M A ζ top J M - matchingSum J (tailCov M Xs Gam M)| +
          ∑ u ∈ Ico j M, (C₃ * (1 / 2 : ℝ) ^ u * P + C₄ * ε) := by
      intro d
      induction d with
      | zero =>
        intro j hj0
        have : j = M := by omega
        subst this
        simp
      | succ d ihd =>
        intro j hj0
        have hjM : j < M := by omega
        have hs := wickDefect_step PS h hjM J B' hB' (fun S hS =>
          hih Ω μ X Y ε M A Xs Gam Gamc ζ top s h S (by omega) (j + 1) hjM)
        have hi := ihd (j + 1) (by omega)
        rw [sum_eq_sum_Ico_succ_bot hjM]
        have e : 2 ^ q * ((K + K ^ 2) * productConst q K + stepCovConst q K * B') * (1 / 2 : ℝ) ^ j *
            X ^ (J.card + 1) * Y = C₃ * (1 / 2 : ℝ) ^ j * P := by rw [hC₃, hP]; ring
        linarith
    have h1 := hdown (M - j) j (by omega)
    have hT := wickDefect_top PS h J hne
    have hsum : ∑ u ∈ Ico j M, (C₃ * (1 / 2 : ℝ) ^ u * P + C₄ * ε) ≤ (2 * |C₃| + |C₄|) * P := by
      rw [sum_add_distrib, ← sum_mul, ← mul_sum]
      have s1 : C₃ * ∑ u ∈ Ico j M, (1 / 2 : ℝ) ^ u ≤ 2 * |C₃| := by
        have a := sum_Ico_half_pow_le j M
        have a0 : 0 ≤ ∑ u ∈ Ico j M, (1 / 2 : ℝ) ^ u := sum_nonneg fun _ _ => by positivity
        calc C₃ * ∑ u ∈ Ico j M, (1 / 2 : ℝ) ^ u ≤ |C₃| * ∑ u ∈ Ico j M, (1 / 2 : ℝ) ^ u :=
              mul_le_mul_of_nonneg_right (le_abs_self _) a0
          _ ≤ |C₃| * 2 := mul_le_mul_of_nonneg_left a (abs_nonneg _)
          _ = _ := by ring
      have s2 : ∑ _u ∈ Ico j M, C₄ * ε ≤ |C₄| * P := by
        rw [sum_const, nsmul_eq_mul, Nat.card_Ico]
        have a1 := error_mul_le h
        have a2 : X ^ (4 * q + 4) ≤ X ^ (J.card + 1) := by
          have hq : J.card ≤ q := by simpa using card_le_univ J
          exact pow_le_pow_of_le_one hX.le h.X_le_one (by omega)
        have a3 : X ^ (J.card + 1) ≤ P := le_mul_of_one_le_right (by positivity) hY
        have a4 : ((M - j : ℕ) : ℝ) * ε ≤ ((M : ℝ) + 1) * ε := by
          apply mul_le_mul_of_nonneg_right _ hε
          have : ((M - j : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.sub_le M j
          linarith
        have a5 : ((M - j : ℕ) : ℝ) * ε ≤ P := by linarith
        have a6 : 0 ≤ ((M - j : ℕ) : ℝ) * ε := by positivity
        calc ((M - j : ℕ) : ℝ) * (C₄ * ε) = C₄ * (((M - j : ℕ) : ℝ) * ε) := by ring
          _ ≤ |C₄| * (((M - j : ℕ) : ℝ) * ε) := mul_le_mul_of_nonneg_right (le_abs_self _) a6
          _ ≤ |C₄| * P := mul_le_mul_of_nonneg_left a5 (abs_nonneg _)
      have s3 : (C₃ * ∑ u ∈ Ico j M, (1 / 2 : ℝ) ^ u) * P ≤ (2 * |C₃|) * P :=
        mul_le_mul_of_nonneg_right s1 hP0
      linarith
    have hXP : X ^ (J.card + 1) ≤ P := le_mul_of_one_le_right (by positivity) hY
    have hTP : K ^ q * X ^ (J.card + 1) ≤ |K ^ q| * P :=
      mul_le_mul (le_abs_self _) hXP (by positivity) (abs_nonneg _)
    have hfin : |tailMoment μ M A ζ top J j - matchingSum J (tailCov M Xs Gam j)| ≤
        (|K ^ q| + 2 * |C₃| + |C₄|) * P := by
      linarith
    refine hfin.trans ?_
    have e : (B' + |K ^ q| + 2 * |C₃| + |C₄| + 1) * X ^ (J.card + 1) * Y =
        (B' + |K ^ q| + 2 * |C₃| + |C₄| + 1) * P := by rw [hP]; ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hP0
    linarith
theorem gaussianMomentsAlongChain_holds (PS : matchingSumPropertiesStatement) :
    gaussianMomentsAlongChainStatement := by
  intro q K
  obtain ⟨B, hB, hdel⟩ := wickDefect_le PS q K q
  refine ⟨B + 2 ^ q * ((q.factorial : ℝ) ^ 2 * |(2 * K) ^ q|) + 3 * |K|, ?_⟩
  intro Ω _ μ X Y ε M A Xs Gam Gamc ζ top s h
  have hprob := h.isProbability
  have hX := h.X_pos
  have hY := h.one_le_Y
  have hK1 := h.one_le_K
  have hKa : |K| = K := abs_of_nonneg (by linarith)
  have hc0 : 0 ≤ 2 ^ q * ((q.factorial : ℝ) ^ 2 * |(2 * K) ^ q|) := by positivity
  refine ⟨fun i => (boundedOn_tailSum h (Nat.zero_le M) i).1, ?_, ?_, ?_, ?_⟩
  · filter_upwards [abs_tailSum_le h (Nat.zero_le M)] with ω hω h0 i
    refine (hω h0 i).trans ?_
    rw [hKa]
    linarith
  · exact (BoundedOn.prod (h.event_measurable 0) Finset.univ fun i _ =>
      boundedOn_tailSum h (Nat.zero_le M) i).integrable
  · intro i i'
    have a : ∀ u ∈ Finset.range M, |Gam u i i'| ≤ K * (1 / 2 : ℝ) ^ u := fun u hu =>
      (h.cov_le u (mem_range.1 hu) i i').trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by norm_num) (by norm_num) u) (by linarith))
    have b := (abs_sum_le_sum_abs _ _).trans (sum_le_sum a)
    rw [← mul_sum] at b
    have c : K * ∑ u ∈ Finset.range M, (1 / 2 : ℝ) ^ u ≤ K * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le M) (by linarith)
    rw [hKa]
    linarith
  have h1 := hdel Ω μ X Y ε M A Xs Gam Gamc ζ top s h Finset.univ (by simp) 0 (Nat.zero_le M)
  have h2 := wickDefect_bottom PS h
  simp only [card_univ, Fintype.card_fin] at h1
  have e : ∫ ω, (A 0).indicator (fun ω => ∏ i, tailSum M ζ top 0 i ω) ω ∂μ =
      tailMoment μ M A ζ top Finset.univ 0 := rfl
  rw [e]
  have h3 : X ^ (q + 1) ≤ X ^ (q + 1) * Y := le_mul_of_one_le_right (by positivity) hY
  have h4 : 2 ^ q * ((q.factorial : ℝ) ^ 2 * |(2 * K) ^ q|) * X ^ (q + 1) ≤
      2 ^ q * ((q.factorial : ℝ) ^ 2 * |(2 * K) ^ q|) * (X ^ (q + 1) * Y) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have t := abs_sub_le (tailMoment μ M A ζ top Finset.univ 0) (matchingSum Finset.univ (tailCov M Xs Gam 0))
    (X ^ q * wickPairingSum (fun i i' => ∑ u ∈ Finset.range M, Gam u i i'))
  have e2 : (B + 2 ^ q * ((q.factorial : ℝ) ^ 2 * |(2 * K) ^ q|) + 3 * |K|) * X ^ (q + 1) * Y =
      B * X ^ (q + 1) * Y + 2 ^ q * ((q.factorial : ℝ) ^ 2 * |(2 * K) ^ q|) * (X ^ (q + 1) * Y) +
        3 * |K| * (X ^ (q + 1) * Y) := by ring
  rw [e2]
  have h5 : 0 ≤ 3 * |K| * (X ^ (q + 1) * Y) := by positivity
  linarith
end YangMills.Construction.ResponseInTheExpansion
end
