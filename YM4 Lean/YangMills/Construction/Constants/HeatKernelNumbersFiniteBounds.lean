import YangMills.Construction.Constants.HeatKernelNumbersFinite
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Constants.HeatKernel
theorem heatDecay_pos : 0 < heatDecay := by
  unfold heatDecay
  positivity
theorem symmetryConstant_pos : 0 < symmetryConstant := by
  unfold symmetryConstant
  positivity
theorem shiftConstant_pos : 0 < shiftConstant := Real.exp_pos 1
theorem lowerDiagonalConstant_pos : 0 < lowerDiagonalConstant := by
  unfold lowerDiagonalConstant
  positivity
theorem factorialPower_pos (n : ℕ) : 0 < factorialPower n := by
  have := symmetryConstant_pos
  unfold factorialPower
  positivity
theorem one_add_pow_mul_exp_neg_le (n : ℕ) {c y : ℝ} (hc : 0 < c) (hy : 0 ≤ y) :
    (1 + y) ^ n * Real.exp (-(c * y)) ≤ (n.factorial : ℝ) * Real.exp c / c ^ n := by
  have h := Real.pow_div_factorial_le_exp (x := c * (1 + y)) (by positivity) n
  have hFact : (0 : ℝ) < n.factorial := by positivity
  rw [div_le_iff₀ hFact, mul_pow] at h
  have hSplit : Real.exp (c * (1 + y)) = Real.exp c * Real.exp (c * y) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hSplit] at h
  have hExp : 0 < Real.exp (c * y) := Real.exp_pos _
  have hPow : 0 < c ^ n := by positivity
  rw [le_div_iff₀ hPow, Real.exp_neg]
  calc (1 + y) ^ n * (Real.exp (c * y))⁻¹ * c ^ n
      = c ^ n * (1 + y) ^ n * (Real.exp (c * y))⁻¹ := by ring
    _ ≤ Real.exp c * Real.exp (c * y) * (n.factorial : ℝ) * (Real.exp (c * y))⁻¹ :=
        mul_le_mul_of_nonneg_right h (inv_pos.2 hExp).le
    _ = (n.factorial : ℝ) * Real.exp c := by
        field_simp
theorem one_add_pow_mul_exp_neg_sq_le (n : ℕ) {c y : ℝ} (hc : 0 < c) (hy : 0 ≤ y) :
    (1 + y) ^ n * Real.exp (-(c * y ^ 2)) ≤
      Real.exp c * ((n.factorial : ℝ) * Real.exp c / c ^ n) := by
  have hGauss : Real.exp (-(c * y ^ 2)) ≤ Real.exp c * Real.exp (-(c * y)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg hc.le (sq_nonneg (y - 1 / 2))]
  have hPow : 0 ≤ (1 + y) ^ n := by positivity
  calc (1 + y) ^ n * Real.exp (-(c * y ^ 2))
      ≤ (1 + y) ^ n * (Real.exp c * Real.exp (-(c * y))) := mul_le_mul_of_nonneg_left hGauss hPow
    _ = Real.exp c * ((1 + y) ^ n * Real.exp (-(c * y))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (one_add_pow_mul_exp_neg_le n hc hy) (Real.exp_pos c).le
theorem halfLineSup_ne_top {f : ℝ → ℝ} {C : ℝ} (h : ∀ y, 0 ≤ y → f y ≤ C) :
    halfLineSup f ≠ ⊤ := by
  unfold halfLineSup
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (iSup₂_le fun y hy => ENNReal.ofReal_le_ofReal (h y hy))
theorem halfLineSup_pos {f : ℝ → ℝ} {y : ℝ} (hy : 0 ≤ y) (h : 0 < f y) :
    0 < halfLineSup f := by
  unfold halfLineSup
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 h) (le_iSup₂_of_le y hy le_rfl)
theorem weightedFactorialPower_ne_top (n : ℕ) : weightedFactorialPower n ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (halfLineSup_ne_top fun _ hy => one_add_pow_mul_exp_neg_sq_le n heatDecay_pos hy)
theorem weightedFactorialPower_pos (n : ℕ) : 0 < weightedFactorialPower n := by
  have h1 : 0 < ENNReal.ofReal (factorialPower n) := ENNReal.ofReal_pos.2 (factorialPower_pos n)
  have h2 : 0 < halfLineSup fun y => (1 + y) ^ n * Real.exp (-(heatDecay * y ^ 2)) :=
    halfLineSup_pos le_rfl (by positivity)
  exact ENNReal.mul_pos h1.ne' h2.ne'
theorem gaussianMoment_ne_top (b : ℕ) : gaussianMoment b ≠ ⊤ := by
  have hc : 0 < 1 / 2 * heatDecay := by
    have := heatDecay_pos
    positivity
  refine halfLineSup_ne_top fun y hy => le_trans ?_ (one_add_pow_mul_exp_neg_sq_le b hc hy)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy (by linarith) b) (Real.exp_pos _).le
theorem gaussianMoment_pos (b : ℕ) : 0 < gaussianMoment b :=
  halfLineSup_pos zero_le_one (by positivity)
theorem gaussianMoment_zero : gaussianMoment 0 = 1 := by
  have hh := heatDecay_pos
  apply le_antisymm
  · unfold gaussianMoment halfLineSup
    refine iSup₂_le fun y _ => ENNReal.ofReal_le_one.2 ?_
    beta_reduce
    rw [pow_zero, one_mul]
    apply Real.exp_le_one_iff.2
    have : 0 ≤ 1 / 2 * heatDecay * y ^ 2 := by positivity
    linarith
  · unfold gaussianMoment halfLineSup
    refine le_iSup₂_of_le 0 le_rfl ?_
    simp
theorem binomialMoment_ne_top (n b : ℕ) : binomialMoment n b ≠ ⊤ := by
  unfold binomialMoment
  refine (ENNReal.sum_lt_top.2 fun κ _ => ?_).ne
  exact (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (weightedFactorialPower_ne_top _)) (gaussianMoment_ne_top _)).lt_top
theorem binomialMoment_pos (n b : ℕ) : 0 < binomialMoment n b := by
  have h : (n.choose 0 : ENNReal) * weightedFactorialPower (n - 0) * gaussianMoment (b - 0) ≤
      binomialMoment n b := by
    unfold binomialMoment
    exact Finset.single_le_sum
      (f := fun κ => (n.choose κ : ENNReal) * weightedFactorialPower (n - κ) * gaussianMoment (b - κ))
      (fun _ _ => zero_le) (Finset.mem_range.2 (Nat.succ_pos n))
  refine lt_of_lt_of_le ?_ h
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  exact ENNReal.mul_pos (weightedFactorialPower_pos n).ne' (gaussianMoment_pos b).ne'
theorem derivativeMoment_ne_top (n b : ℕ) : derivativeMoment n b ≠ ⊤ := by
  unfold derivativeMoment
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top (binomialMoment_ne_top n b),
      binomialMoment_ne_top n (b + 1)⟩,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (binomialMoment_ne_top n (b + 4))⟩)
theorem derivativeMoment_pos (n b : ℕ) : 0 < derivativeMoment n b := by
  unfold derivativeMoment
  have h1 : 0 < ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2) * symmetryConstant) := by
    have := symmetryConstant_pos
    exact ENNReal.ofReal_pos.2 (by positivity)
  have h2 : 0 < 2 * binomialMoment n b := ENNReal.mul_pos (by simp) (binomialMoment_pos n b).ne'
  have h3 : 0 < 2 * binomialMoment n b + binomialMoment n (b + 1) +
      ENNReal.ofReal (2 ^ (n + 1) * Real.pi ^ 2) * binomialMoment n (b + 4) :=
    lt_of_lt_of_le h2 (le_self_add.trans le_self_add)
  exact ENNReal.mul_pos h1.ne' h3.ne'
theorem kernelDerivativeBound_ne_top (n : ℕ) : kernelDerivativeBound n ≠ ⊤ := by
  unfold kernelDerivativeBound
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt ?_)
  refine (Finset.sup_lt_iff bot_lt_top).2 fun b _ => ?_
  exact max_lt (derivativeMoment_ne_top 0 b).lt_top (derivativeMoment_ne_top n b).lt_top
theorem kernelDerivativeBound_pos (n : ℕ) : 0 < kernelDerivativeBound n := by
  unfold kernelDerivativeBound
  have h1 : 0 < ENNReal.ofReal (2 ^ n / (2 * Real.pi)) := ENNReal.ofReal_pos.2 (by positivity)
  have h2 : derivativeMoment 0 0 ≤
      ({0, 1, 2} : Finset ℕ).sup fun b => max (derivativeMoment 0 b) (derivativeMoment n b) :=
    le_trans (le_max_left _ (derivativeMoment n 0))
      (Finset.le_sup (f := fun b => max (derivativeMoment 0 b) (derivativeMoment n b)) (by simp))
  exact ENNReal.mul_pos h1.ne' (lt_of_lt_of_le (derivativeMoment_pos 0 0) h2).ne'
theorem two_mul_add_three_pow_div_factorial_le (n l : ℕ) :
    (2 * (l : ℝ) + 3) ^ n / (l.factorial : ℝ) ≤
      3 ^ n * ((n.factorial : ℝ) * Real.exp 1 / 1 ^ n) * Real.exp (Real.exp 1) := by
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hFact : (0 : ℝ) < l.factorial := by positivity
  have h1 : (2 * (l : ℝ) + 3) ^ n ≤ 3 ^ n * (1 + (l : ℝ)) ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) n
  have h2 := one_add_pow_mul_exp_neg_le n (c := 1) (y := l) one_pos hl
  set K : ℝ := (n.factorial : ℝ) * Real.exp 1 / 1 ^ n with hK
  have hExp : 0 < Real.exp (l : ℝ) := Real.exp_pos _
  have h3 : (1 + (l : ℝ)) ^ n ≤ K * Real.exp (l : ℝ) := by
    rw [one_mul, Real.exp_neg] at h2
    calc (1 + (l : ℝ)) ^ n
        = (1 + (l : ℝ)) ^ n * (Real.exp (l : ℝ))⁻¹ * Real.exp (l : ℝ) := by field_simp
      _ ≤ K * Real.exp (l : ℝ) := mul_le_mul_of_nonneg_right h2 hExp.le
  have h4 : Real.exp (l : ℝ) / (l.factorial : ℝ) ≤ Real.exp (Real.exp 1) := by
    rw [← Real.exp_one_pow]
    exact Real.pow_div_factorial_le_exp _ (Real.exp_pos 1).le l
  calc (2 * (l : ℝ) + 3) ^ n / (l.factorial : ℝ)
      ≤ (3 ^ n * (K * Real.exp (l : ℝ))) / (l.factorial : ℝ) := by
        apply div_le_div_of_nonneg_right _ hFact.le
        exact h1.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
    _ = 3 ^ n * K * (Real.exp (l : ℝ) / (l.factorial : ℝ)) := by ring
    _ ≤ 3 ^ n * K * Real.exp (Real.exp 1) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
theorem halfLineSup_quartic_mul_exp_ne_top :
    (halfLineSup fun y => (y ^ 4 + y ^ 3) * Real.exp (-(y / 8))) ≠ ⊤ := by
  refine halfLineSup_ne_top (C := 2 * ((4 : ℕ).factorial * Real.exp (1 / 8) / (1 / 8) ^ 4))
    fun y hy => ?_
  have h := one_add_pow_mul_exp_neg_le 4 (c := 1 / 8) (by norm_num) hy
  have hEighth : -(y / 8) = -(1 / 8 * y) := by ring
  have hPoly : y ^ 4 + y ^ 3 ≤ 2 * (1 + y) ^ 4 := by
    have : 2 * (1 + y) ^ 4 - (y ^ 4 + y ^ 3) = 2 + 8 * y + 12 * y ^ 2 + 7 * y ^ 3 + y ^ 4 := by
      ring
    have h0 : 0 ≤ 2 + 8 * y + 12 * y ^ 2 + 7 * y ^ 3 + y ^ 4 := by positivity
    linarith
  rw [hEighth]
  calc (y ^ 4 + y ^ 3) * Real.exp (-(1 / 8 * y))
      ≤ 2 * (1 + y) ^ 4 * Real.exp (-(1 / 8 * y)) :=
        mul_le_mul_of_nonneg_right hPoly (Real.exp_pos _).le
    _ = 2 * ((1 + y) ^ 4 * Real.exp (-(1 / 8 * y))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)
theorem halfLineSup_one_add_pow_mul_gaussian_ne_top (n : ℕ) :
    (halfLineSup fun y => (1 + y) ^ n * Real.exp (-(y ^ 2 / 8))) ≠ ⊤ := by
  refine halfLineSup_ne_top
    (C := Real.exp (1 / 8) * ((n.factorial : ℝ) * Real.exp (1 / 8) / (1 / 8) ^ n)) fun y hy => ?_
  have h := one_add_pow_mul_exp_neg_sq_le n (c := 1 / 8) (by norm_num) hy
  have hEighth : -(y ^ 2 / 8) = -(1 / 8 * y ^ 2) := by ring
  rw [hEighth]
  exact h
theorem gaussianComparison_ne_top (n : ℕ) : gaussianComparison n ≠ ⊤ := by
  unfold gaussianComparison
  have h1 : (⨆ l : ℕ, ENNReal.ofReal ((2 * (l : ℝ) + 3) ^ n / (l.factorial : ℝ))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup_le fun l => ENNReal.ofReal_le_ofReal (two_mul_add_three_pow_div_factorial_le n l))
  refine (max_lt (max_lt ?_ ?_) ?_).ne
  · exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h1).lt_top
  · exact (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      halfLineSup_quartic_mul_exp_ne_top) (halfLineSup_one_add_pow_mul_gaussian_ne_top n)).lt_top
  · exact (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.pow_ne_top (kernelDerivativeBound_ne_top n))).lt_top
theorem gaussianComparison_pos (n : ℕ) : 0 < gaussianComparison n := by
  unfold gaussianComparison
  have h1 : 0 < ENNReal.ofReal (4 * shiftConstant) := by
    have := shiftConstant_pos
    exact ENNReal.ofReal_pos.2 (by positivity)
  have h2 : 0 < ⨆ l : ℕ, ENNReal.ofReal ((2 * (l : ℝ) + 3) ^ n / (l.factorial : ℝ)) := by
    refine lt_of_lt_of_le (ENNReal.ofReal_pos.2 ?_)
      (le_iSup (fun l : ℕ => ENNReal.ofReal ((2 * (l : ℝ) + 3) ^ n / (l.factorial : ℝ))) 0)
    positivity
  exact lt_of_lt_of_le (ENNReal.mul_pos h1.ne' h2.ne')
    (le_max_of_le_left (le_max_left _ _))
theorem fieldConstant_ne_top : fieldConstant ≠ ⊤ := by
  unfold fieldConstant
  have h : ((15 : ENNReal) + 10368 + 1024 * 257 ^ 3) ≠ ⊤ := by
    norm_num
  exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top h (gaussianComparison_ne_top 6),
    ENNReal.ofReal_ne_top⟩, ENNReal.ofReal_ne_top⟩
theorem fieldConstant_pos : 0 < fieldConstant := by
  unfold fieldConstant
  have h : 0 < ENNReal.ofReal (1 / 2 * lowerDiagonalConstant) := by
    have := lowerDiagonalConstant_pos
    exact ENNReal.ofReal_pos.2 (by positivity)
  exact lt_of_lt_of_le h le_add_self
theorem finite_and_pos_of_exponential_bounds : finite_and_pos := by
  have hpi := Real.pi_gt_three
  refine ⟨symmetryConstant_pos, heatDecay_pos, shiftConstant_pos, lowerDiagonalConstant_pos,
    factorialPower_pos,
    fun n => ⟨weightedFactorialPower_ne_top n, weightedFactorialPower_pos n⟩,
    fun b => ⟨gaussianMoment_ne_top b, gaussianMoment_pos b⟩,
    fun n b => ⟨binomialMoment_ne_top n b, binomialMoment_pos n b⟩,
    fun n b => ⟨derivativeMoment_ne_top n b, derivativeMoment_pos n b⟩,
    fun n => ⟨kernelDerivativeBound_ne_top n, kernelDerivativeBound_pos n⟩,
    fun n => ⟨gaussianComparison_ne_top n, gaussianComparison_pos n⟩,
    ⟨fieldConstant_ne_top, fieldConstant_pos⟩, ?_, ?_, ?_, gaussianMoment_zero⟩
  · unfold symmetryConstant
    linarith
  · unfold heatDecay
    have h9 : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
    have hp : 0 < Real.pi ^ 2 := by positivity
    rw [← mul_div_assoc, div_le_one hp]
    linarith
  · unfold heatDecay
    have h : Real.pi ^ (-2 : ℤ) = (Real.pi ^ 2)⁻¹ := by
      rw [zpow_neg]
      norm_cast
    rw [h]
    ring
end YangMills.Construction.Constants.HeatKernel
