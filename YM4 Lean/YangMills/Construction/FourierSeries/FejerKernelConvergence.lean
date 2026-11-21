import YangMills.Construction.FourierSeries.FejerMeansUniformLimit
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
namespace YangMills.Construction.FourierSeries.FejerKernel
def dirichletKernel (t : ℕ) (s : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(t : ℤ)) (t : ℤ), Complex.exp ((k : ℂ) * (s : ℂ) * Complex.I)
def fejerKernel (n : ℕ) (s : ℝ) : ℂ :=
  ((n : ℂ) + 1)⁻¹ * ∑ t ∈ Finset.range (n + 1), dirichletKernel t s
theorem continuous_dirichletKernel (t : ℕ) : Continuous (dirichletKernel t) := by
  unfold dirichletKernel
  fun_prop
theorem continuous_fejerKernel (n : ℕ) : Continuous (fejerKernel n) := by
  unfold fejerKernel
  exact continuous_const.mul (continuous_finsetSum _ fun t _ => continuous_dirichletKernel t)
theorem symmetricPartialSum_eq_integral_mul_dirichletKernel {f : ℝ → ℂ} (hf : Continuous f)
    (t : ℕ) (u : ℝ) :
    symmetricPartialSum f t u =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ v in (-Real.pi)..Real.pi, f v * dirichletKernel t (u - v) := by
  simp only [symmetricPartialSum, fourierCoeffOnCircle, dirichletKernel, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, ← intervalIntegral.integral_mul_const]
    congr 2
    funext v
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · intro k _
    exact Continuous.intervalIntegrable (by fun_prop) _ _
theorem cesaroMean_eq_integral_mul_fejerKernel {f : ℝ → ℂ} (hf : Continuous f) (n : ℕ) (u : ℝ) :
    cesaroMeanOfPartialSums f n u =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ v in (-Real.pi)..Real.pi, f v * fejerKernel n (u - v) := by
  have hk : ∀ v, f v * fejerKernel n (u - v) =
      ((n : ℂ) + 1)⁻¹ * ∑ t ∈ Finset.range (n + 1), f v * dirichletKernel t (u - v) := by
    intro v
    simp only [fejerKernel, ← Finset.mul_sum]
    ring
  simp only [hk]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
  · simp only [cesaroMeanOfPartialSums, symmetricPartialSum_eq_integral_mul_dirichletKernel hf,
      ← Finset.mul_sum]
    ring
  · intro t _
    exact (hf.mul ((continuous_dirichletKernel t).comp (by fun_prop))).intervalIntegrable _ _
theorem geom_sum_mul_pow_of_mul_eq_one {z y : ℂ} (hzy : z * y = 1) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), z ^ j) * y ^ (n + 1) =
      ∑ j ∈ Finset.range (n + 1), y ^ (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz : z ^ (n + 1) * (y ^ (n + 1) * y) = y := by
      rw [← mul_assoc, ← mul_pow, hzy, one_pow, one_mul]
    rw [Finset.sum_range_succ, add_mul, pow_succ y (n + 1), ← mul_assoc, ih, hz,
      Finset.sum_range_succ' (fun j => y ^ (j + 1)) (n + 1), Finset.sum_mul]
    simp [pow_succ]
theorem sum_zpow_Icc_neg_self (z : ℂ) (t : ℕ) :
    ∑ k ∈ Finset.Icc (-(t : ℤ)) (t : ℤ), z ^ k =
      1 + ∑ j ∈ Finset.range t, (z ^ (j + 1) + z⁻¹ ^ (j + 1)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hset : Finset.Icc (-((t + 1 : ℕ) : ℤ)) ((t + 1 : ℕ) : ℤ) =
        insert (((t + 1 : ℕ) : ℤ)) (insert (-((t + 1 : ℕ) : ℤ))
          (Finset.Icc (-(t : ℤ)) (t : ℤ))) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have h1 : ((t + 1 : ℕ) : ℤ) ∉ insert (-((t + 1 : ℕ) : ℤ))
        (Finset.Icc (-(t : ℤ)) (t : ℤ)) := by
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have h2 : -((t + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(t : ℤ)) (t : ℤ) := by
      simp only [Finset.mem_Icc]
      push_cast
      omega
    rw [hset, Finset.sum_insert h1, Finset.sum_insert h2, ih, Finset.sum_range_succ,
      zpow_neg, zpow_natCast, inv_pow]
    ring
theorem sum_range_sum_zpow_Icc_eq_mul {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), ∑ k ∈ Finset.Icc (-(t : ℤ)) (t : ℤ), z ^ k =
      (∑ j ∈ Finset.range (n + 1), z ^ j) * ∑ j ∈ Finset.range (n + 1), z⁻¹ ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hzy : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
    have hyz : z⁻¹ * z = 1 := inv_mul_cancel₀ hz
    have a1 := geom_sum_mul_pow_of_mul_eq_one hzy n
    have a2 := geom_sum_mul_pow_of_mul_eq_one hyz n
    have a3 : z ^ (n + 1) * z⁻¹ ^ (n + 1) = 1 := by rw [← mul_pow, hzy, one_pow]
    rw [Finset.sum_range_succ, ih, sum_zpow_Icc_neg_self, Finset.sum_add_distrib,
      Finset.sum_range_succ _ (n + 1), Finset.sum_range_succ (fun j => z⁻¹ ^ j) (n + 1), ← a1, ← a2]
    linear_combination -a3
def fejerKernelReal (n : ℕ) (s : ℝ) : ℝ :=
  ((n : ℝ) + 1)⁻¹ * ‖∑ j ∈ Finset.range (n + 1), Complex.exp ((s : ℂ) * Complex.I) ^ j‖ ^ 2
theorem fejerKernelReal_nonneg (n : ℕ) (s : ℝ) : 0 ≤ fejerKernelReal n s := by
  unfold fejerKernelReal
  positivity
theorem fejerKernel_eq_ofReal (n : ℕ) (s : ℝ) : fejerKernel n s = (fejerKernelReal n s : ℂ) := by
  set z := Complex.exp ((s : ℂ) * Complex.I) with hz
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hconj : (starRingEnd ℂ) z = z⁻¹ := by
    rw [hz, ← Complex.exp_conj, ← Complex.exp_neg]
    simp
  have hd : ∀ t : ℕ, dirichletKernel t s = ∑ k ∈ Finset.Icc (-(t : ℤ)) (t : ℤ), z ^ k := by
    intro t
    unfold dirichletKernel
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hz, ← Complex.exp_int_mul]
    congr 1
    ring
  have hsum : (∑ j ∈ Finset.range (n + 1), z⁻¹ ^ j) =
      (starRingEnd ℂ) (∑ j ∈ Finset.range (n + 1), z ^ j) := by
    rw [map_sum]
    simp only [map_pow, hconj]
  simp only [fejerKernel, hd]
  rw [sum_range_sum_zpow_Icc_eq_mul hz0, hsum, Complex.mul_conj']
  simp only [fejerKernelReal, ← hz]
  push_cast
  rfl
theorem continuous_fejerKernelReal (n : ℕ) : Continuous (fejerKernelReal n) := by
  unfold fejerKernelReal
  fun_prop
def expChar (m : ℤ) (u : ℝ) : ℂ := Complex.exp ((m : ℂ) * (u : ℂ) * Complex.I)
theorem continuous_expChar (m : ℤ) : Continuous (expChar m) := by
  unfold expChar
  fun_prop
theorem fourierCoeffOnCircle_expChar (m k : ℤ) :
    fourierCoeffOnCircle (expChar m) k = if k = m then 1 else 0 := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hint : ∀ u : ℝ, expChar m u * Complex.exp (-((k : ℂ) * (u : ℂ) * Complex.I)) =
      Complex.exp ((((m - k : ℤ) : ℂ) * Complex.I) * (u : ℂ)) := by
    intro u
    rw [expChar, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold fourierCoeffOnCircle
  simp only [hint]
  split_ifs with h
  · subst h
    simp only [sub_self, Int.cast_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const]
    simp only [sub_neg_eq_add, Complex.real_smul, mul_one]
    push_cast
    rw [← two_mul]
    exact inv_mul_cancel₀ hpi
  · have hc : (((m - k : ℤ) : ℂ) * Complex.I) ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      exact_mod_cast sub_ne_zero.mpr (Ne.symm h)
    rw [integral_exp_mul_complex hc]
    have hper : Complex.exp ((((m - k : ℤ) : ℂ) * Complex.I) * ((Real.pi : ℝ) : ℂ)) =
        Complex.exp ((((m - k : ℤ) : ℂ) * Complex.I) * ((-Real.pi : ℝ) : ℂ)) := by
      have := Complex.exp_int_mul_two_pi_mul_I (m - k)
      rw [show (((m - k : ℤ) : ℂ) * Complex.I) * ((Real.pi : ℝ) : ℂ) =
        (((m - k : ℤ) : ℂ) * Complex.I) * ((-Real.pi : ℝ) : ℂ) +
          ((m - k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
        Complex.exp_add, this, mul_one]
    rw [hper]
    simp
theorem norm_expChar (m : ℤ) (u : ℝ) : ‖expChar m u‖ = 1 := by
  have : expChar m u = Complex.exp (((m * u : ℝ) : ℂ) * Complex.I) := by
    rw [expChar]
    push_cast
    rfl
  rw [this, Complex.norm_exp_ofReal_mul_I]
def indicatorFreqLe (m : ℤ) (t : ℕ) : ℝ := if m ∈ Finset.Icc (-(t : ℤ)) (t : ℤ) then 1 else 0
theorem symmetricPartialSum_expChar (m : ℤ) (t : ℕ) (u : ℝ) :
    symmetricPartialSum (expChar m) t u = (indicatorFreqLe m t : ℂ) * expChar m u := by
  unfold symmetricPartialSum indicatorFreqLe
  simp only [fourierCoeffOnCircle_expChar, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq']
  split_ifs <;> simp [expChar]
theorem cesaroMean_expChar (m : ℤ) (n : ℕ) (u : ℝ) :
    cesaroMeanOfPartialSums (expChar m) n u =
      ((((n + 1 : ℕ) : ℝ)⁻¹ * ∑ t ∈ Finset.range (n + 1), indicatorFreqLe m t : ℝ) : ℂ) *
        expChar m u := by
  simp only [cesaroMeanOfPartialSums, symmetricPartialSum_expChar, ← Finset.sum_mul]
  push_cast
  ring
theorem tendsto_average_indicatorFreqLe (m : ℤ) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ t ∈ Finset.range (n + 1), indicatorFreqLe m t)
      atTop (𝓝 1) := by
  have h : Tendsto (indicatorFreqLe m) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨m.natAbs, fun t ht => ?_⟩)
    have : m ∈ Finset.Icc (-(t : ℤ)) (t : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    simp [indicatorFreqLe, this]
  exact h.cesaro.comp (tendsto_add_atTop_nat 1)
theorem tendstoUniformly_cesaroMean_expChar (m : ℤ) :
    TendstoUniformly (cesaroMeanOfPartialSums (expChar m)) (expChar m) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.1 (tendsto_average_indicatorFreqLe m) ε hε] with n hn u
  rw [cesaroMean_expChar, dist_eq_norm]
  set c : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ t ∈ Finset.range (n + 1), indicatorFreqLe m t with hc
  have : expChar m u - (c : ℂ) * expChar m u = ((1 - c : ℝ) : ℂ) * expChar m u := by
    push_cast
    ring
  rw [this, norm_mul, norm_expChar, mul_one, Complex.norm_real]
  rw [Real.dist_eq] at hn
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact hn
theorem cesaroMean_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (n : ℕ) (u : ℝ) :
    cesaroMeanOfPartialSums (fun x => f x + g x) n u =
      cesaroMeanOfPartialSums f n u + cesaroMeanOfPartialSums g n u := by
  have hk : Continuous fun v => fejerKernel n (u - v) := (continuous_fejerKernel n).comp (by fun_prop)
  have hs := intervalIntegral.integral_add (μ := volume) (a := -Real.pi) (b := Real.pi)
    (f := fun v => f v * fejerKernel n (u - v)) (g := fun v => g v * fejerKernel n (u - v))
    ((hf.mul hk).intervalIntegrable _ _) ((hg.mul hk).intervalIntegrable _ _)
  rw [cesaroMean_eq_integral_mul_fejerKernel (f := fun x => f x + g x) (hf.add hg),
    cesaroMean_eq_integral_mul_fejerKernel hf,
    cesaroMean_eq_integral_mul_fejerKernel hg, ← mul_add, ← hs]
  simp only [add_mul]
theorem cesaroMean_const_mul {f : ℝ → ℂ} (hf : Continuous f) (c : ℂ) (n : ℕ) (u : ℝ) :
    cesaroMeanOfPartialSums (fun x => c * f x) n u = c * cesaroMeanOfPartialSums f n u := by
  rw [cesaroMean_eq_integral_mul_fejerKernel (f := fun x => c * f x) (continuous_const.mul hf),
    cesaroMean_eq_integral_mul_fejerKernel hf]
  simp only [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring
theorem cesaroMean_sub {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (n : ℕ) (u : ℝ) :
    cesaroMeanOfPartialSums (fun x => f x - g x) n u =
      cesaroMeanOfPartialSums f n u - cesaroMeanOfPartialSums g n u := by
  have h1 := cesaroMean_add (g := fun x => (-1 : ℂ) * g x) hf (continuous_const.mul hg) n u
  rw [cesaroMean_const_mul hg] at h1
  simp only [neg_one_mul, ← sub_eq_add_neg] at h1
  exact h1
theorem integral_fejerKernelReal (n : ℕ) (u : ℝ) :
    ∫ v in (-Real.pi)..Real.pi, fejerKernelReal n (u - v) = 2 * Real.pi := by
  have h1 : cesaroMeanOfPartialSums (expChar 0) n u = 1 := by
    have hs : ∀ t : ℕ, indicatorFreqLe 0 t = 1 := by
      intro t
      simp [indicatorFreqLe]
    have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    rw [cesaroMean_expChar]
    simp only [hs, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [inv_mul_cancel₀ hn]
    simp [expChar]
  rw [cesaroMean_eq_integral_mul_fejerKernel (continuous_expChar 0)] at h1
  have h2 : ∀ v : ℝ, expChar 0 v * fejerKernel n (u - v) = (fejerKernelReal n (u - v) : ℂ) := by
    intro v
    rw [fejerKernel_eq_ofReal]
    simp [expChar]
  simp only [h2] at h1
  rw [intervalIntegral.integral_ofReal] at h1
  have h3 : ((∫ v in (-Real.pi)..Real.pi, fejerKernelReal n (u - v) : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) := by
    field_simp at h1
    exact h1
  exact_mod_cast h3
theorem norm_cesaroMean_le {f : ℝ → ℂ} (hf : Continuous f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M)
    (n : ℕ) (u : ℝ) : ‖cesaroMeanOfPartialSums f n u‖ ≤ M := by
  have hw : Continuous fun v => M * fejerKernelReal n (u - v) :=
    continuous_const.mul ((continuous_fejerKernelReal n).comp (by fun_prop))
  have hb : ‖∫ v in (-Real.pi)..Real.pi, f v * fejerKernel n (u - v)‖ ≤
      ∫ v in (-Real.pi)..Real.pi, M * fejerKernelReal n (u - v) := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith [Real.pi_pos])
      (Eventually.of_forall fun v _ => ?_) (hw.intervalIntegrable _ _)
    rw [norm_mul, fejerKernel_eq_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (fejerKernelReal_nonneg _ _)]
    exact mul_le_mul_of_nonneg_right (hM v) (fejerKernelReal_nonneg _ _)
  rw [intervalIntegral.integral_const_mul, integral_fejerKernelReal] at hb
  have hc : ‖(2 * (Real.pi : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    simp
  rw [cesaroMean_eq_integral_mul_fejerKernel hf, norm_mul, hc]
  calc (2 * Real.pi)⁻¹ * ‖∫ v in (-Real.pi)..Real.pi, f v * fejerKernel n (u - v)‖
      ≤ (2 * Real.pi)⁻¹ * (M * (2 * Real.pi)) := by gcongr
    _ = M := by field_simp
instance fact_two_pi_pos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
theorem continuous_comp_coe (p : C(AddCircle (2 * Real.pi), ℂ)) :
    Continuous fun u : ℝ => p (u : AddCircle (2 * Real.pi)) :=
  p.continuous.comp (AddCircle.continuous_mk' _)
theorem fourier_coe_eq_expChar (m : ℤ) (u : ℝ) :
    fourier m (u : AddCircle (2 * Real.pi)) = expChar m u := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  rw [fourier_coe_apply, expChar]
  congr 1
  push_cast
  field_simp
theorem tendstoUniformly_cesaroMean_of_mem_span (p : C(AddCircle (2 * Real.pi), ℂ))
    (hp : p ∈ Submodule.span ℂ (Set.range (fourier (T := 2 * Real.pi)))) :
    TendstoUniformly (cesaroMeanOfPartialSums fun u : ℝ => p u) (fun u : ℝ => p u) atTop := by
  induction hp using Submodule.span_induction with
  | mem x h =>
    obtain ⟨m, rfl⟩ := h
    have : (fun u : ℝ => fourier m (u : AddCircle (2 * Real.pi))) = expChar m :=
      funext (fourier_coe_eq_expChar m)
    rw [this]
    exact tendstoUniformly_cesaroMean_expChar m
  | zero =>
    have h0 : ∀ n u, cesaroMeanOfPartialSums
        (fun u : ℝ => (0 : C(AddCircle (2 * Real.pi), ℂ)) u) n u = 0 := by
      intro n u
      have := norm_cesaroMean_le (f := fun u : ℝ => (0 : C(AddCircle (2 * Real.pi), ℂ)) u)
        (continuous_comp_coe 0) (M := 0) (by simp) n u
      exact norm_le_zero_iff.1 this
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    exact Eventually.of_forall fun n u => by
      rw [h0 n u]
      simpa using hε
  | add a b _ _ ha hb =>
    rw [Metric.tendstoUniformly_iff] at ha hb ⊢
    intro ε hε
    filter_upwards [ha (ε / 2) (by positivity), hb (ε / 2) (by positivity)] with n h1 h2 u
    have h3 : cesaroMeanOfPartialSums (fun u : ℝ => (a + b) u) n u =
        cesaroMeanOfPartialSums (fun u : ℝ => a u) n u +
          cesaroMeanOfPartialSums (fun u : ℝ => b u) n u :=
      cesaroMean_add (continuous_comp_coe a) (continuous_comp_coe b) n u
    rw [h3]
    have := dist_add_add_le (a u) (b u) (cesaroMeanOfPartialSums (fun u : ℝ => a u) n u)
      (cesaroMeanOfPartialSums (fun u : ℝ => b u) n u)
    have h4 := h1 u
    have h5 := h2 u
    simp only [ContinuousMap.add_apply]
    linarith
  | smul c a _ ha =>
    rw [Metric.tendstoUniformly_iff] at ha ⊢
    intro ε hε
    have hpos : 0 < ε / (‖c‖ + 1) := by positivity
    filter_upwards [ha _ hpos] with n h1 u
    have h3 : cesaroMeanOfPartialSums (fun u : ℝ => (c • a) u) n u =
        c * cesaroMeanOfPartialSums (fun u : ℝ => a u) n u :=
      cesaroMean_const_mul (continuous_comp_coe a) c n u
    rw [h3]
    have h4 := h1 u
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    rw [dist_eq_norm, ← mul_sub, norm_mul, ← dist_eq_norm]
    calc ‖c‖ * dist (a u) (cesaroMeanOfPartialSums (fun u : ℝ => a u) n u)
        ≤ ‖c‖ * (ε / (‖c‖ + 1)) := by gcongr
      _ < (‖c‖ + 1) * (ε / (‖c‖ + 1)) := by
          apply mul_lt_mul_of_pos_right _ hpos
          linarith
      _ = ε := by field_simp
theorem tendstoUniformly_cesaroMean_addCircle (g : C(AddCircle (2 * Real.pi), ℂ)) :
    TendstoUniformly (cesaroMeanOfPartialSums fun u : ℝ => g u) (fun u : ℝ => g u) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hg : g ∈ (Submodule.span ℂ
      (Set.range (fourier (T := 2 * Real.pi)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hg
  obtain ⟨p, hp, hd⟩ := hg (ε / 3) (by positivity)
  filter_upwards [Metric.tendstoUniformly_iff.1 (tendstoUniformly_cesaroMean_of_mem_span p hp)
    (ε / 3) (by positivity)] with n hn u
  have hgp : ∀ x : AddCircle (2 * Real.pi), ‖g x - p x‖ ≤ dist g p := by
    intro x
    rw [dist_eq_norm]
    exact (g - p).norm_coe_le_norm x
  have h1 : dist (g u) (p u) ≤ dist g p := by
    rw [dist_eq_norm]
    exact hgp _
  have h2 : dist (cesaroMeanOfPartialSums (fun u : ℝ => p u) n u)
      (cesaroMeanOfPartialSums (fun u : ℝ => g u) n u) ≤ dist g p := by
    rw [dist_comm, dist_eq_norm,
      ← cesaroMean_sub (continuous_comp_coe g) (continuous_comp_coe p)]
    exact norm_cesaroMean_le ((continuous_comp_coe g).sub (continuous_comp_coe p))
      (fun x => hgp _) n u
  have h3 := hn u
  have h4 := dist_triangle4 (g u) (p u) (cesaroMeanOfPartialSums (fun u : ℝ => p u) n u)
    (cesaroMeanOfPartialSums (fun u : ℝ => g u) n u)
  linarith
theorem tendstoUniformly_cesaroMean_of_periodic {f : ℝ → ℂ} (hf : Continuous f)
    (hp : Function.Periodic f (2 * Real.pi)) :
    TendstoUniformly (cesaroMeanOfPartialSums f) f atTop := by
  have hc : Continuous hp.lift :=
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 (by
      convert hf using 1
      funext u
      exact hp.lift_coe u)
  have hl : (fun u : ℝ => (⟨hp.lift, hc⟩ : C(AddCircle (2 * Real.pi), ℂ)) u) = f :=
    funext fun u => hp.lift_coe u
  have := tendstoUniformly_cesaroMean_addCircle ⟨hp.lift, hc⟩
  rwa [hl] at this
variable {d : ℕ}
theorem apply_update_add_int_mul_two_pi {h : (Fin d → ℝ) → ℂ}
    (hp : IsTwoPiPeriodicInEachCoord h) (a : Fin d) (m : ℤ) (y : Fin d → ℝ) :
    h (Function.update y a (y a + m * (2 * Real.pi))) = h y := by
  have hper : Function.Periodic (fun t => h (Function.update y a t)) (2 * Real.pi) := by
    intro t
    have := hp a (Function.update y a t)
    simpa using this
  have := (hper.int_mul m) (y a)
  simpa using this
theorem apply_add_int_mul_two_pi {h : (Fin d → ℝ) → ℂ} (hp : IsTwoPiPeriodicInEachCoord h)
    (n : Fin d → ℤ) (y : Fin d → ℝ) : h (fun j => y j + n j * (2 * Real.pi)) = h y := by
  have key : ∀ S : Finset (Fin d),
      h (fun j => if j ∈ S then y j + n j * (2 * Real.pi) else y j) = h y := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      refine Eq.trans ?_ ((apply_update_add_int_mul_two_pi hp a (n a) _).trans ih)
      congr 1
      funext j
      by_cases hj : j = a
      · subst hj
        simp [ha]
      · simp [hj]
  simpa using key Finset.univ
def coverTorus (y : Fin d → ℝ) : UnitAddTorus (Fin d) :=
  fun j => ((y j / (2 * Real.pi) : ℝ) : UnitAddCircle)
theorem isOpenQuotientMap_div_two_pi :
    IsOpenQuotientMap (fun t : ℝ => ((t / (2 * Real.pi) : ℝ) : UnitAddCircle)) := by
  have hpi : (2 * Real.pi) ≠ 0 := Real.two_pi_pos.ne'
  refine ⟨?_, ?_, ?_⟩
  · intro x
    induction x using QuotientAddGroup.induction_on with
    | H z =>
      refine ⟨z * (2 * Real.pi), ?_⟩
      simp only [mul_div_assoc, div_self hpi, mul_one]
  · exact (AddCircle.continuous_mk' 1).comp (by fun_prop)
  · have h1 : IsOpenMap (fun t : ℝ => t / (2 * Real.pi)) := by
      simpa [div_eq_mul_inv] using
        (Homeomorph.mulRight₀ (2 * Real.pi)⁻¹ (inv_ne_zero hpi)).isOpenMap
    exact (QuotientAddGroup.isOpenMap_coe).comp h1
theorem isQuotientMap_coverTorus : Topology.IsQuotientMap (coverTorus (d := d)) :=
  (IsOpenQuotientMap.piMap fun _ => isOpenQuotientMap_div_two_pi).isQuotientMap
theorem exists_int_shift_of_coverTorus_eq {y y' : Fin d → ℝ} (h : coverTorus y = coverTorus y') :
    ∃ n : Fin d → ℤ, y' = fun j => y j + n j * (2 * Real.pi) := by
  have hj : ∀ j, ∃ n : ℤ, y' j = y j + n * (2 * Real.pi) := by
    intro j
    have h1 := congrFun h j
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 h1)
    refine ⟨n, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hn
    field_simp at hn
    linarith
  choose n hn using hj
  exact ⟨n, funext hn⟩
theorem mFourier_coverTorus (k : Fin d → ℤ) (y : Fin d → ℝ) :
    UnitAddTorus.mFourier k (coverTorus y) =
      Complex.exp ((∑ j, (k j : ℂ) * (y j : ℂ)) * Complex.I) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  rw [Finset.sum_mul, Complex.exp_sum]
  change (∏ j, (fourier (k j) (coverTorus y j) : ℂ)) = _
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [coverTorus, fourier_coe_apply]
  congr 1
  push_cast
  field_simp
def piCube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ fun _ : Fin d => Set.Icc (-Real.pi) Real.pi
theorem isCompact_piCube : IsCompact (piCube d) :=
  isCompact_univ_pi fun _ => isCompact_Icc
theorem piCube_subset_closure_interior : piCube d ⊆ closure (interior (piCube d)) := by
  have hlt : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  unfold piCube
  rw [interior_pi_set Set.finite_univ, closure_pi_set]
  refine Set.pi_mono fun _ _ => ?_
  simp only [interior_Icc, closure_Ioo hlt.ne]
  exact subset_rfl
theorem eq_zero_of_integral_mul_mFourier_eq_zero {h : (Fin d → ℝ) → ℂ} (hc : Continuous h)
    (hp : IsTwoPiPeriodicInEachCoord h)
    (hz : ∀ k : Fin d → ℤ, ∫ y in piCube d, h y * UnitAddTorus.mFourier k (coverTorus y) = 0)
    (y : Fin d → ℝ) : h y = 0 := by
  have hq := isQuotientMap_coverTorus (d := d)
  have hfac : Function.FactorsThrough h (coverTorus (d := d)) := by
    intro a b hab
    obtain ⟨n, rfl⟩ := exists_int_shift_of_coverTorus_eq hab
    exact (apply_add_int_mul_two_pi hp n a).symm
  obtain ⟨H, hH⟩ : ∃ H : C(UnitAddTorus (Fin d), ℂ), ∀ y, H (coverTorus y) = h y := by
    let F : C(Fin d → ℝ, UnitAddTorus (Fin d)) := ⟨coverTorus, hq.continuous⟩
    have hF : Topology.IsQuotientMap F := hq
    let G : C(Fin d → ℝ, ℂ) := ⟨h, hc⟩
    have hG : Function.FactorsThrough G F := hfac
    exact ⟨hF.lift G hG, fun y => DFunLike.congr_fun (hF.lift_comp G hG) y⟩
  have hint : ∀ p : C(UnitAddTorus (Fin d), ℂ),
      IntegrableOn (fun y => h y * p (coverTorus y)) (piCube d) := fun p =>
    (hc.mul (p.continuous.comp hq.continuous)).continuousOn.integrableOn_compact isCompact_piCube
  have hspan : ∀ q ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin d))),
      ∫ y in piCube d, h y * q (coverTorus y) = 0 := by
    intro q hq'
    induction hq' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact hz k
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [ContinuousMap.add_apply, mul_add]
      rw [integral_add (hint a) (hint b), ha, hb, add_zero]
    | smul c a _ ha =>
      have hm : ∀ y, h y * (c • a) (coverTorus y) = c * (h y * a (coverTorus y)) := by
        intro y
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        ring
      simp only [hm]
      rw [integral_const_mul, ha, mul_zero]
  have hbound : ∀ r : C(UnitAddTorus (Fin d), ℂ),
      ‖∫ y in piCube d, h y * r (coverTorus y)‖ ≤ ‖H‖ * ‖r‖ * volume.real (piCube d) := by
    intro r
    refine norm_setIntegral_le_of_norm_le_const isCompact_piCube.measure_lt_top fun y _ => ?_
    rw [norm_mul, ← hH y]
    exact mul_le_mul (H.norm_coe_le_norm _) (r.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
  have hzero : ∫ y in piCube d, h y * (star H) (coverTorus y) = 0 := by
    by_contra hne
    have ha : 0 < ‖∫ y in piCube d, h y * (star H) (coverTorus y)‖ := norm_pos_iff.2 hne
    have hC : 0 ≤ ‖H‖ * volume.real (piCube d) := by positivity
    have hmem : star H ∈ (Submodule.span ℂ
        (Set.range (UnitAddTorus.mFourier (d := Fin d)))).topologicalClosure := by
      rw [UnitAddTorus.span_mFourier_closure_eq_top]
      trivial
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hmem
    obtain ⟨q, hq', hd⟩ := hmem
      (‖∫ y in piCube d, h y * (star H) (coverTorus y)‖ / (‖H‖ * volume.real (piCube d) + 1))
      (by positivity)
    have hlin : ∫ y in piCube d, h y * (star H - q) (coverTorus y) =
        ∫ y in piCube d, h y * (star H) (coverTorus y) := by
      simp only [ContinuousMap.sub_apply, mul_sub]
      rw [integral_sub (hint _) (hint _), hspan q hq', sub_zero]
    have h1 := hbound (star H - q)
    rw [hlin] at h1
    rw [dist_eq_norm] at hd
    set A := ‖∫ y in piCube d, h y * (star H) (coverTorus y)‖
    set C := ‖H‖ * volume.real (piCube d)
    have h2 : ‖H‖ * ‖star H - q‖ * volume.real (piCube d) = C * ‖star H - q‖ := by
      simp only [C]
      ring
    rw [h2] at h1
    have h3 : C * ‖star H - q‖ ≤ C * (A / (C + 1)) := by gcongr
    have h4 : C * (A / (C + 1)) < A := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hsq : ∀ y, h y * (star H) (coverTorus y) = ((‖h y‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    rw [ContinuousMap.star_apply, hH y, Complex.star_def, Complex.mul_conj']
    push_cast
    rfl
  simp only [hsq] at hzero
  rw [integral_complex_ofReal] at hzero
  have hzero' : ∫ y in piCube d, ‖h y‖ ^ 2 = 0 := by exact_mod_cast hzero
  have hae := (integral_eq_zero_iff_of_nonneg (f := fun y => ‖h y‖ ^ 2) (fun y => sq_nonneg _)
    (((hc.norm.pow 2).continuousOn.integrableOn_compact isCompact_piCube))).1 hzero'
  have hae' : h =ᵐ[volume.restrict (piCube d)] fun _ => (0 : ℂ) := by
    filter_upwards [hae] with y hy
    simpa using hy
  have hon : Set.EqOn h (fun _ => (0 : ℂ)) (piCube d) :=
    Measure.eqOn_of_ae_eq hae' hc.continuousOn continuousOn_const piCube_subset_closure_interior
  have hpos : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  set y' : Fin d → ℝ := fun j => toIcoMod hpos (-Real.pi) (y j) with hy'
  have hy'c : y' ∈ piCube d := by
    intro j _
    have := toIcoMod_mem_Ico hpos (-Real.pi) (y j)
    exact ⟨this.1, by linarith [this.2]⟩
  have hshift : y = fun j => y' j + (toIcoDiv hpos (-Real.pi) (y j) : ℤ) * (2 * Real.pi) := by
    funext j
    have := self_sub_toIcoDiv_zsmul hpos (-Real.pi) (y j)
    simp only [hy', ← this, zsmul_eq_mul]
    ring
  rw [hshift, apply_add_int_mul_two_pi hp (fun j => toIcoDiv hpos (-Real.pi) (y j)) y']
  exact hon hy'c
theorem eq_of_fourierCoeffOnTorus_eq {f g : (Fin d → ℝ) → ℂ} (hf : Continuous f)
    (hg : Continuous g) (pf : IsTwoPiPeriodicInEachCoord f) (pg : IsTwoPiPeriodicInEachCoord g)
    (hfg : ∀ k : Fin d → ℤ, fourierCoeffOnTorus f k = fourierCoeffOnTorus g k) : f = g := by
  have hpi : ((2 * (Real.pi : ℂ)) ^ d)⁻¹ ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hp : IsTwoPiPeriodicInEachCoord fun y => f y - g y := by
    intro j y
    simp only [pf j y, pg j y]
  have hint : ∀ (φ : (Fin d → ℝ) → ℂ), Continuous φ → ∀ k : Fin d → ℤ,
      IntegrableOn (fun y => φ y * UnitAddTorus.mFourier k (coverTorus y)) (piCube d) :=
    fun φ hφ k =>
      (hφ.mul ((UnitAddTorus.mFourier k).continuous.comp
        isQuotientMap_coverTorus.continuous)).continuousOn.integrableOn_compact isCompact_piCube
  have hz : ∀ k : Fin d → ℤ,
      ∫ y in piCube d, (f y - g y) * UnitAddTorus.mFourier k (coverTorus y) = 0 := by
    intro k
    have hk := hfg (-k)
    have hE : ∀ y : Fin d → ℝ, Complex.exp (-((∑ j, ((-k) j : ℂ) * (y j : ℂ)) * Complex.I)) =
        UnitAddTorus.mFourier k (coverTorus y) := by
      intro y
      rw [mFourier_coverTorus]
      congr 1
      simp [Finset.sum_neg_distrib]
    unfold fourierCoeffOnTorus at hk
    simp only [hE] at hk
    have hk' := mul_left_cancel₀ hpi hk
    simp only [sub_mul]
    rw [integral_sub (hint f hf k) (hint g hg k)]
    exact sub_eq_zero.2 hk'
  funext y
  exact sub_eq_zero.1 (eq_zero_of_integral_mul_mFourier_eq_zero (hf.sub hg) hp hz y)
theorem fejerTheoremAndTorusUniqueness_holds : FejerTheoremAndTorusUniqueness :=
  ⟨fun _ hf hp => tendstoUniformly_cesaroMean_of_periodic hf hp,
    fun _ _ _ hf hg pf pg hfg => eq_of_fourierCoeffOnTorus_eq hf hg pf pg hfg⟩
end YangMills.Construction.FourierSeries.FejerKernel
