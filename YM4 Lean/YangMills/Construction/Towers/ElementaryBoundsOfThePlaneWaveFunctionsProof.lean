import YangMills.Construction.Weighted.BoxPoincareProof
import YangMills.Construction.Towers.ElementaryBoundsOfThePlaneWaveFunctions
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.PlaneWaves.PlaneWaveBounds
open YangMills.Construction.PeriodicOperators (toComplexVec)
theorem cosh_sub_one_le_of_abs_le_eighth {y : ℝ} (hy : |y| ≤ 1 / 8) :
    Real.cosh y - 1 ≤ y ^ 2 / 2 * (129 / 128) := by
  have hy2 : y ^ 2 ≤ 1 / 64 := by
    have := sq_le_sq' (neg_le_of_abs_le hy) (le_of_abs_le hy)
    nlinarith
  have h1 := Real.cosh_le_exp_half_sq y
  have hu : |y ^ 2 / 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have h2 := le_of_abs_le (Real.abs_exp_sub_one_sub_id_le hu)
  nlinarith
theorem abs_sinh_le_of_abs_le_eighth {y : ℝ} (hy : |y| ≤ 1 / 8) :
    |Real.sinh y| ≤ 11 / 10 * |y| := by
  have hy2 : y ^ 2 ≤ 1 / 64 := by
    have := sq_le_sq' (neg_le_of_abs_le hy) (le_of_abs_le hy)
    nlinarith
  have h1 := cosh_sub_one_le_of_abs_le_eighth hy
  have h2 := Real.one_le_cosh y
  have h3 := Real.cosh_sq y
  have h4 : Real.sinh y ^ 2 ≤ (11 / 10 * |y|) ^ 2 := by
    have : (11 / 10 * |y|) ^ 2 = 121 / 100 * y ^ 2 := by
      rw [mul_pow, sq_abs]; norm_num
    rw [this]
    nlinarith
  have h5 := sq_le_sq.mp h4
  rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 11 / 10 * |y|)] at h5
theorem two_div_pi_mul_abs_le_abs_sin {t : ℝ} (ht : |t| ≤ Real.pi / 2) :
    2 / Real.pi * |t| ≤ |Real.sin t| := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h] at ht ⊢
    exact (Real.mul_le_sin h ht).trans (le_abs_self _)
  · rw [abs_of_nonpos h] at ht ⊢
    have := Real.mul_le_sin (neg_nonneg.mpr h) ht
    rw [Real.sin_neg] at this
    exact this.trans (neg_le_abs _)
theorem sub_cube_div_six_le_sin {t : ℝ} (ht : 0 ≤ t) : t - t ^ 3 / 6 ≤ Real.sin t := by
  have hmono : Monotone fun x : ℝ => Real.sin x - x + x ^ 3 / 6 := by
    apply monotone_of_deriv_nonneg
    · fun_prop
    · intro x
      have : deriv (fun x : ℝ => Real.sin x - x + x ^ 3 / 6) x = Real.cos x - 1 + x ^ 2 / 2 := by
        have h : HasDerivAt (fun x : ℝ => Real.sin x - x + x ^ 3 / 6)
            (Real.cos x - 1 + (3 * x ^ 2) / 6) x := by
          have := (((Real.hasDerivAt_sin x).fun_sub (hasDerivAt_id' x)).fun_add
            (((hasDerivAt_id' x).fun_pow 3).div_const 6))
          simpa using this
        rw [h.deriv]; ring
      rw [this]
      have := Real.one_sub_sq_div_two_le_cos (x := x)
      linarith
  have := hmono ht
  simp at this
  linarith
def axialSymbol (η : ℝ) (w : ℂ) : ℂ :=
  (η : ℂ)⁻¹ * (Complex.exp (Complex.I * (η : ℂ) * w) - 1)
theorem norm_axialSymbol_ofReal {η : ℝ} (hη : 0 < η) (x : ℝ) :
    ‖axialSymbol η x‖ = 2 * η⁻¹ * |Real.sin (η * x / 2)| := by
  have h : Complex.I * (η : ℂ) * (x : ℂ) = Complex.I * ((η * x : ℝ) : ℂ) := by
    push_cast; ring
  rw [axialSymbol, h, norm_mul, Complex.norm_exp_I_mul_ofReal_sub_one, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg hη.le, Real.norm_eq_abs, abs_mul]
  norm_num
  ring
theorem norm_axialSymbol_neg {η : ℝ} (hη : 0 < η) (x : ℝ) :
    ‖axialSymbol η ((-x : ℝ) : ℂ)‖ = ‖axialSymbol η x‖ := by
  rw [norm_axialSymbol_ofReal hη, norm_axialSymbol_ofReal hη,
    show η * -x / 2 = -(η * x / 2) by ring, Real.sin_neg, abs_neg]
theorem axialSymbol_norm_bounds {η : ℝ} (hη : 0 < η) {x : ℝ}
    (hx : |x| ≤ Real.pi / η) :
    2 / Real.pi * |x| ≤ ‖axialSymbol η x‖ ∧ ‖axialSymbol η x‖ ≤ |x| := by
  have hηx : |η * x| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos hη]
    calc η * |x| ≤ η * (Real.pi / η) := by gcongr
      _ = Real.pi := by field_simp
  have ht : |η * x / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hj := two_div_pi_mul_abs_le_abs_sin ht
  have hne : η ≠ 0 := hη.ne'
  have habs : |η * x / 2| = η * |x| / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hη, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  constructor
  · rw [norm_axialSymbol_ofReal hη]
    rw [habs] at hj
    calc 2 / Real.pi * |x| = 2 * η⁻¹ * (2 / Real.pi * (η * |x| / 2)) := by field_simp
      _ ≤ 2 * η⁻¹ * |Real.sin (η * x / 2)| := by gcongr
  · have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := η * x)
    have e : Complex.I * (η : ℂ) * (x : ℂ) = Complex.I * ((η * x : ℝ) : ℂ) := by
      push_cast; ring
    rw [axialSymbol, e, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hη.le]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hη] at h
    calc η⁻¹ * ‖Complex.exp (Complex.I * ((η * x : ℝ) : ℂ)) - 1‖ ≤ η⁻¹ * (η * |x|) := by gcongr
      _ = |x| := by field_simp
theorem axialSymbol_mul_neg (η : ℝ) (w : ℂ) :
    axialSymbol η w * axialSymbol η (-w) =
      2 * ((η : ℂ)⁻¹) ^ 2 * (1 - Complex.cos ((η : ℂ) * w)) := by
  have h2 := Complex.two_cos ((η : ℂ) * w)
  have e1 : Complex.I * (η : ℂ) * w = (η : ℂ) * w * Complex.I := by ring
  have e2 : Complex.I * (η : ℂ) * -w = -((η : ℂ) * w) * Complex.I := by ring
  have hp : Complex.exp ((η : ℂ) * w * Complex.I) * Complex.exp (-((η : ℂ) * w) * Complex.I) = 1 := by
    rw [← Complex.exp_add]; simp
  simp only [axialSymbol, e1, e2]
  linear_combination ((η : ℂ)⁻¹) ^ 2 * hp + ((η : ℂ)⁻¹) ^ 2 * h2
theorem axialSymbol_mul_neg_re_im (η x θ : ℝ) :
    (axialSymbol η ((x : ℂ) + Complex.I * (θ : ℂ)) *
        axialSymbol η (-((x : ℂ) + Complex.I * (θ : ℂ)))).re =
      2 * (η⁻¹) ^ 2 * (1 - Real.cos (η * x) * Real.cosh (η * θ)) ∧
    (axialSymbol η ((x : ℂ) + Complex.I * (θ : ℂ)) *
        axialSymbol η (-((x : ℂ) + Complex.I * (θ : ℂ)))).im =
      2 * (η⁻¹) ^ 2 * (Real.sin (η * x) * Real.sinh (η * θ)) := by
  have hc : Complex.cos ((η : ℂ) * ((x : ℂ) + Complex.I * (θ : ℂ))) =
      ((Real.cos (η * x) * Real.cosh (η * θ) : ℝ) : ℂ) -
        ((Real.sin (η * x) * Real.sinh (η * θ) : ℝ) : ℂ) * Complex.I := by
    have e : (η : ℂ) * ((x : ℂ) + Complex.I * (θ : ℂ)) =
        ((η * x : ℝ) : ℂ) + ((η * θ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e, Complex.cos_add_mul_I]
    push_cast
    ring
  have key : axialSymbol η ((x : ℂ) + Complex.I * (θ : ℂ)) *
        axialSymbol η (-((x : ℂ) + Complex.I * (θ : ℂ))) =
      ((2 * (η⁻¹) ^ 2 * (1 - Real.cos (η * x) * Real.cosh (η * θ)) : ℝ) : ℂ) +
        ((2 * (η⁻¹) ^ 2 * (Real.sin (η * x) * Real.sinh (η * θ)) : ℝ) : ℂ) * Complex.I := by
    rw [axialSymbol_mul_neg, hc]
    push_cast
    ring
  have aux : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * Complex.I).re = a ∧
      ((a : ℂ) + (b : ℂ) * Complex.I).im = b := by
    intro a b; simp
  rw [key]
  exact aux _ _
theorem norm_sq_axialSymbol {η : ℝ} (hη : 0 < η) (x : ℝ) :
    ‖axialSymbol η x‖ ^ 2 = 2 * (η⁻¹) ^ 2 * (1 - Real.cos (η * x)) := by
  rw [norm_axialSymbol_ofReal hη, mul_pow, sq_abs]
  have h1 : Real.cos (η * x) = Real.cos (2 * (η * x / 2)) := by ring_nf
  have h2 := Real.sin_sq_add_cos_sq (η * x / 2)
  rw [h1, Real.cos_two_mul]
  nlinarith
theorem axialSymbol_mul_neg_bounds {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (x θ : ℝ)
    (hθ : |θ| ≤ 1 / 8) :
    ‖axialSymbol η x‖ ^ 2 - 1 / 40 ≤
        (axialSymbol η ((x : ℂ) + Complex.I * (θ : ℂ)) *
          axialSymbol η (-((x : ℂ) + Complex.I * (θ : ℂ)))).re ∧
    (axialSymbol η ((x : ℂ) + Complex.I * (θ : ℂ)) *
          axialSymbol η (-((x : ℂ) + Complex.I * (θ : ℂ)))).re ≤
        11 / 10 * ‖axialSymbol η x‖ ^ 2 ∧
    |(axialSymbol η ((x : ℂ) + Complex.I * (θ : ℂ)) *
          axialSymbol η (-((x : ℂ) + Complex.I * (θ : ℂ)))).im| ≤
        11 / 80 * (‖axialSymbol η x‖ ^ 2 + 1) := by
  obtain ⟨hre, him⟩ := axialSymbol_mul_neg_re_im η x θ
  rw [hre, him]
  have hne : η ≠ 0 := hη.ne'
  have hy : |η * θ| ≤ 1 / 8 := by
    rw [abs_mul, abs_of_pos hη]
    calc η * |θ| ≤ 1 * (1 / 8) := by gcongr
      _ = 1 / 8 := by norm_num
  have hc1 := Real.one_le_cosh (η * θ)
  have hc2 := cosh_sub_one_le_of_abs_le_eighth hy
  have hθ2 : θ ^ 2 ≤ 1 / 64 := by
    have := sq_le_sq' (neg_le_of_abs_le hθ) (le_of_abs_le hθ)
    nlinarith
  have hcn := norm_sq_axialSymbol hη x
  set c := ‖axialSymbol η x‖ ^ 2 with hcdef
  set C := Real.cosh (η * θ) with hC
  have hre' : 2 * (η⁻¹) ^ 2 * (1 - Real.cos (η * x) * C) =
      c * C - 2 * (η⁻¹) ^ 2 * (C - 1) := by
    rw [hcn]; ring
  have hsmall : 2 * (η⁻¹) ^ 2 * (C - 1) ≤ 1 / 40 := by
    have : 2 * (η⁻¹) ^ 2 * ((η * θ) ^ 2 / 2 * (129 / 128)) = θ ^ 2 * (129 / 128) := by
      field_simp
    have h' : 2 * (η⁻¹) ^ 2 * (C - 1) ≤ 2 * (η⁻¹) ^ 2 * ((η * θ) ^ 2 / 2 * (129 / 128)) := by
      gcongr
    rw [this] at h'
    linarith
  have hpos : 0 ≤ 2 * (η⁻¹) ^ 2 * (C - 1) := by
    have : 0 ≤ C - 1 := by linarith
    positivity
  have hCle : C ≤ 11 / 10 := by
    have : (η * θ) ^ 2 ≤ 1 / 64 := by
      have := sq_le_sq' (neg_le_of_abs_le hy) (le_of_abs_le hy)
      nlinarith
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hre']
    nlinarith
  · rw [hre']
    nlinarith
  · set A := ‖axialSymbol η x‖ with hA
    have hAS : A = 2 * η⁻¹ * |Real.sin (η * x / 2)| := norm_axialSymbol_ofReal hη x
    have hsinx : |Real.sin (η * x)| ≤ η * A := by
      have e : η * x = 2 * (η * x / 2) := by ring
      rw [e, Real.sin_two_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), hAS]
      have hcos : |Real.cos (η * x / 2)| ≤ 1 := Real.abs_cos_le_one _
      have : η * (2 * η⁻¹ * |Real.sin (η * x / 2)|) = 2 * |Real.sin (η * x / 2)| := by
        field_simp
      rw [this]
      have := abs_nonneg (Real.sin (η * x / 2))
      nlinarith
    have hsinh := abs_sinh_le_of_abs_le_eighth hy
    rw [abs_mul, abs_of_pos hη] at hsinh
    have hprod : |Real.sin (η * x) * Real.sinh (η * θ)| ≤ (η * A) * (11 / 10 * (η * |θ|)) := by
      rw [abs_mul]
      gcongr
    have hfin : |2 * (η⁻¹) ^ 2 * (Real.sin (η * x) * Real.sinh (η * θ))| ≤
        2 * (η⁻¹) ^ 2 * ((η * A) * (11 / 10 * (η * |θ|))) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (η⁻¹) ^ 2)]
      gcongr
    have hsimp : 2 * (η⁻¹) ^ 2 * ((η * A) * (11 / 10 * (η * |θ|))) = 11 / 5 * (A * |θ|) := by
      field_simp
      ring
    rw [hsimp] at hfin
    have hAq : A ≤ (A ^ 2 + 1) / 2 := by nlinarith [sq_nonneg (A - 1)]
    have : A * |θ| ≤ A * (1 / 8) := by gcongr
    nlinarith
theorem norm_axialSymbol_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (x θ : ℝ)
    (hθ : |θ| ≤ 1 / 8) :
    ‖axialSymbol η ((x : ℂ) + Complex.I * (θ : ℂ))‖ ≤
      6 / 5 * (‖axialSymbol η x‖ + 1 / 8) := by
  have hne : η ≠ 0 := hη.ne'
  have hy : |η * θ| ≤ 1 / 8 := by
    rw [abs_mul, abs_of_pos hη]
    calc η * |θ| ≤ 1 * (1 / 8) := by gcongr
      _ = 1 / 8 := by norm_num
  set y := η * θ with hydef
  have hy1 : |-y| ≤ 1 := by rw [abs_neg]; linarith
  have hexp := Real.abs_exp_sub_one_sub_id_le hy1
  have hy2 : y ^ 2 ≤ |y| * (1 / 8) := by
    rw [← sq_abs]
    have := abs_nonneg y
    nlinarith
  have hr1 : |Real.exp (-y) - 1| ≤ 6 / 5 * |y| := by
    have h1 : |Real.exp (-y) - 1| ≤ |Real.exp (-y) - 1 - -y| + |-y| := by
      have := abs_add_le (Real.exp (-y) - 1 - -y) (-y)
      simpa using this
    rw [abs_neg] at h1
    have h2 : (-y) ^ 2 = y ^ 2 := by ring
    rw [h2] at hexp
    have := abs_nonneg y
    nlinarith
  have hr2 : Real.exp (-y) ≤ 6 / 5 := by
    have := le_of_abs_le hr1
    linarith
  have e : Complex.exp (Complex.I * (η : ℂ) * ((x : ℂ) + Complex.I * (θ : ℂ))) =
      Complex.exp (Complex.I * ((η * x : ℝ) : ℂ)) * ((Real.exp (-y) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    rw [hydef]
    push_cast
    linear_combination ((η : ℂ) * (θ : ℂ)) * this
  set E := Complex.exp (Complex.I * ((η * x : ℝ) : ℂ)) with hE
  have e2 : axialSymbol η x = (η : ℂ)⁻¹ * (E - 1) := by
    rw [axialSymbol, hE]
    congr 3
    push_cast; ring
  have hsplit : E * ((Real.exp (-y) : ℝ) : ℂ) - 1 =
      ((Real.exp (-y) : ℝ) : ℂ) * (E - 1) + ((Real.exp (-y) - 1 : ℝ) : ℂ) := by
    push_cast; ring
  have hnorm : ‖E * ((Real.exp (-y) : ℝ) : ℂ) - 1‖ ≤ 6 / 5 * ‖E - 1‖ + 6 / 5 * |y| := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_eq_abs]
    gcongr
  have hd : ‖axialSymbol η x‖ = η⁻¹ * ‖E - 1‖ := by
    rw [e2, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hη.le]
  have hyθ : η⁻¹ * |y| = |θ| := by
    rw [hydef, abs_mul, abs_of_pos hη]
    field_simp
  rw [axialSymbol, e, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hη.le, hd]
  calc η⁻¹ * ‖E * ((Real.exp (-y) : ℝ) : ℂ) - 1‖
      ≤ η⁻¹ * (6 / 5 * ‖E - 1‖ + 6 / 5 * |y|) := by gcongr
    _ = 6 / 5 * (η⁻¹ * ‖E - 1‖ + η⁻¹ * |y|) := by ring
    _ ≤ 6 / 5 * (η⁻¹ * ‖E - 1‖ + 1 / 8) := by rw [hyθ]; gcongr
theorem norm_axialSymbol_neg_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (x θ : ℝ)
    (hθ : |θ| ≤ 1 / 8) :
    ‖axialSymbol η (-((x : ℂ) + Complex.I * (θ : ℂ)))‖ ≤
      6 / 5 * (‖axialSymbol η x‖ + 1 / 8) := by
  have h := norm_axialSymbol_le hη hη1 (-x) (-θ) (by rwa [abs_neg])
  rw [norm_axialSymbol_neg hη] at h
  have e : -((x : ℂ) + Complex.I * (θ : ℂ)) = ((-x : ℝ) : ℂ) + Complex.I * ((-θ : ℝ) : ℂ) := by
    push_cast; ring
  rwa [e]
def axialDirichlet (η : ℝ) (N : ℕ) (τ : ℂ) : ℂ :=
  (η : ℂ) * ∑ j ∈ Finset.Icc (-(N : ℤ)) N, Complex.exp (Complex.I * (η : ℂ) * (j : ℂ) * τ)
theorem sin_mul_sum_exp_eq (a : ℂ) (N : ℕ) :
    Complex.sin a * ∑ j ∈ Finset.Icc (-(N : ℤ)) N, Complex.exp (Complex.I * (2 * (j : ℂ) * a)) =
      Complex.sin ((2 * (N : ℂ) + 1) * a) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hset : Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) =
        insert ((n : ℤ) + 1) (insert (-((n : ℤ) + 1)) (Finset.Icc (-(n : ℤ)) n)) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have h1 : ((n : ℤ) + 1) ∉ insert (-((n : ℤ) + 1)) (Finset.Icc (-(n : ℤ)) n) := by
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h2 : (-((n : ℤ) + 1)) ∉ Finset.Icc (-(n : ℤ)) n := by
      simp only [Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert h1, Finset.sum_insert h2, mul_add, mul_add, ih]
    set b : ℂ := (2 * (n : ℂ) + 2) * a with hb
    have hc := Complex.two_cos b
    have e1 : Complex.I * (2 * (((n : ℤ) + 1 : ℤ) : ℂ) * a) = b * Complex.I := by
      rw [hb]; push_cast; ring
    have e2 : Complex.I * (2 * ((-((n : ℤ) + 1) : ℤ) : ℂ) * a) = -b * Complex.I := by
      rw [hb]; push_cast; ring
    have e3 : (2 * (n : ℂ) + 1) * a = b - a := by rw [hb]; ring
    have e4 : (2 * ((n + 1 : ℕ) : ℂ) + 1) * a = b + a := by rw [hb]; push_cast; ring
    rw [e1, e2, e3, e4, Complex.sin_add, Complex.sin_sub]
    linear_combination (-Complex.sin a) * hc
theorem sin_mul_axialDirichlet {η : ℝ} {N : ℕ} (hN : η⁻¹ = 2 * (N : ℝ) + 1) (τ : ℂ) :
    Complex.sin ((η : ℂ) * τ / 2) * axialDirichlet η N τ =
      (η : ℂ) * Complex.sin (τ / 2) := by
  have hη : (η : ℂ) ≠ 0 := by
    intro h
    have h0 : η = 0 := by exact_mod_cast h
    rw [h0] at hN
    norm_num at hN
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hNc : (2 * (N : ℂ) + 1) * (η : ℂ) = 1 := by
    have : ((η : ℂ))⁻¹ = 2 * (N : ℂ) + 1 := by exact_mod_cast hN
    rw [← this]
    exact inv_mul_cancel₀ hη
  have h := sin_mul_sum_exp_eq ((η : ℂ) * τ / 2) N
  have e : (2 * (N : ℂ) + 1) * ((η : ℂ) * τ / 2) = τ / 2 := by
    linear_combination (τ / 2) * hNc
  rw [e] at h
  rw [axialDirichlet, ← h]
  have hsum : ∑ j ∈ Finset.Icc (-(N : ℤ)) N, Complex.exp (Complex.I * (η : ℂ) * (j : ℂ) * τ) =
      ∑ j ∈ Finset.Icc (-(N : ℤ)) N,
        Complex.exp (Complex.I * (2 * (j : ℂ) * ((η : ℂ) * τ / 2))) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring
  rw [hsum]
  ring
theorem card_Icc_neg_self (N : ℕ) :
    ((Finset.Icc (-(N : ℤ)) N).card : ℝ) = 2 * (N : ℝ) + 1 := by apply _root_.YangMills.Construction.Weighted.BoxPoincare.card_symmetricInterval <;> assumption
theorem norm_axialDirichlet_le {η : ℝ} {N : ℕ} (hN : η⁻¹ = 2 * (N : ℝ) + 1) (x θ : ℝ)
    (hθ : |θ| ≤ 1 / 8) :
    ‖axialDirichlet η N ((x : ℂ) + Complex.I * (θ : ℂ))‖ ≤ Real.exp (1 / 16) := by
  have hη : 0 < η := by
    have : 0 < η⁻¹ := by rw [hN]; linarith
    exact inv_pos.mp this
  have hterm : ∀ j ∈ Finset.Icc (-(N : ℤ)) N,
      ‖Complex.exp (Complex.I * (η : ℂ) * (j : ℂ) * ((x : ℂ) + Complex.I * (θ : ℂ)))‖ ≤
        Real.exp (1 / 16) := by
    intro j hj
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have e : Complex.I * (η : ℂ) * (j : ℂ) * ((x : ℂ) + Complex.I * (θ : ℂ)) =
        ((-(η * j * θ) : ℝ) : ℂ) + ((η * j * x : ℝ) : ℂ) * Complex.I := by
      have : Complex.I * Complex.I = -1 := Complex.I_mul_I
      push_cast
      linear_combination ((η : ℂ) * (j : ℂ) * (θ : ℂ)) * this
    have hre : (Complex.I * (η : ℂ) * (j : ℂ) * ((x : ℂ) + Complex.I * (θ : ℂ))).re =
        -(η * j * θ) := by
      rw [e]; simp
    rw [hre]
    have hj' : |(j : ℝ)| ≤ N := by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
      have h1' : -(N : ℝ) ≤ j := by exact_mod_cast h1
      have h2' : (j : ℝ) ≤ N := by exact_mod_cast h2
      exact abs_le.mpr ⟨h1', h2'⟩
    have hηN : η * N ≤ 1 / 2 := by
      have h1 : η * (2 * (N : ℝ) + 1) = 1 := by rw [← hN]; exact mul_inv_cancel₀ hη.ne'
      nlinarith
    have hb : |η * j * θ| ≤ 1 / 16 := by
      rw [abs_mul, abs_mul, abs_of_pos hη]
      calc η * |(j : ℝ)| * |θ| ≤ η * N * (1 / 8) := by gcongr
        _ ≤ 1 / 2 * (1 / 8) := by gcongr
        _ = 1 / 16 := by norm_num
    exact (neg_le_abs _).trans hb
  rw [axialDirichlet, norm_mul, Complex.norm_real, Real.norm_of_nonneg hη.le]
  calc η * ‖∑ j ∈ Finset.Icc (-(N : ℤ)) N,
        Complex.exp (Complex.I * (η : ℂ) * (j : ℂ) * ((x : ℂ) + Complex.I * (θ : ℂ)))‖
      ≤ η * ∑ j ∈ Finset.Icc (-(N : ℤ)) N, Real.exp (1 / 16) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = Real.exp (1 / 16) := by
        rw [Finset.sum_const, nsmul_eq_mul, card_Icc_neg_self, ← hN, ← mul_assoc,
          mul_inv_cancel₀ hη.ne', one_mul]
theorem axialDirichlet_neg (η : ℝ) (N : ℕ) (τ : ℂ) :
    axialDirichlet η N (-τ) = axialDirichlet η N τ := by
  rw [axialDirichlet, axialDirichlet]
  congr 1
  refine Finset.sum_bij (fun j _ => -j) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro a _ b _ h
    omega
  · intro j hj
    refine ⟨-j, ?_, by simp⟩
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j _
    congr 1
    push_cast
    ring
theorem axialDirichlet_ofReal_im (η : ℝ) (N : ℕ) (t : ℝ) :
    (axialDirichlet η N (t : ℂ)).im = 0 := by
  have hconj : (starRingEnd ℂ) (axialDirichlet η N (t : ℂ)) =
      axialDirichlet η N (-(t : ℂ)) := by
    rw [axialDirichlet, axialDirichlet, map_mul, map_sum, Complex.conj_ofReal]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast]
    ring
  exact Complex.conj_eq_iff_im.mp (hconj.trans (axialDirichlet_neg η N (t : ℂ)))
theorem sin_mul_axialDirichlet_re {η : ℝ} {N : ℕ} (hN : η⁻¹ = 2 * (N : ℝ) + 1) (t : ℝ) :
    Real.sin (η * t / 2) * (axialDirichlet η N (t : ℂ)).re = η * Real.sin (t / 2) := by
  have h := sin_mul_axialDirichlet hN (t : ℂ)
  have hs : axialDirichlet η N (t : ℂ) = ((axialDirichlet η N (t : ℂ)).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using axialDirichlet_ofReal_im η N t
  rw [hs] at h
  have e1 : (η : ℂ) * (t : ℂ) / 2 = ((η * t / 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (t : ℂ) / 2 = ((t / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, ← Complex.ofReal_sin, ← Complex.ofReal_sin] at h
  exact_mod_cast h
theorem axialDirichlet_zero {η : ℝ} {N : ℕ} (hN : η⁻¹ = 2 * (N : ℝ) + 1) :
    axialDirichlet η N 0 = 1 := by
  have hη : 0 < η := by
    have : 0 < η⁻¹ := by rw [hN]; linarith
    exact inv_pos.mp this
  have hc : (((Finset.Icc (-(N : ℤ)) N).card : ℝ) : ℂ) = ((η⁻¹ : ℝ) : ℂ) := by
    rw [card_Icc_neg_self, hN]
  have hc' : (((Finset.Icc (-(N : ℤ)) N).card : ℕ) : ℂ) = ((η⁻¹ : ℝ) : ℂ) := by
    rw [← hc]; simp
  simp only [axialDirichlet, mul_zero, Complex.exp_zero, Finset.sum_const, nsmul_eq_mul,
    mul_one]
  rw [hc', ← Complex.ofReal_mul, mul_inv_cancel₀ hη.ne']
  simp
theorem axialDirichlet_re_bounds_of_pos {η : ℝ} {N : ℕ} (hN : η⁻¹ = 2 * (N : ℝ) + 1) {t : ℝ}
    (ht0 : 0 < t) (ht : t ≤ Real.pi) :
    2 / Real.pi ≤ (axialDirichlet η N (t : ℂ)).re ∧
      1 - t ^ 2 / 24 ≤ (axialDirichlet η N (t : ℂ)).re := by
  have hη : 0 < η := by
    have : 0 < η⁻¹ := by rw [hN]; linarith
    exact inv_pos.mp this
  have hη1 : η ≤ 1 := by
    have h1 : η * (2 * (N : ℝ) + 1) = 1 := by rw [← hN]; exact mul_inv_cancel₀ hη.ne'
    nlinarith
  have hid := sin_mul_axialDirichlet_re hN t
  set r := (axialDirichlet η N (t : ℂ)).re with hr
  set u := t / 2 with hu
  have hu0 : 0 < u := by positivity
  have huπ : u ≤ Real.pi / 2 := by rw [hu]; linarith
  have hηt : η * t / 2 = η * u := by rw [hu]; ring
  rw [hηt] at hid
  have hηu0 : 0 < η * u := by positivity
  have hηuπ : η * u ≤ Real.pi / 2 := by nlinarith
  have hb0 : 0 < Real.sin (η * u) :=
    Real.sin_pos_of_pos_of_lt_pi hηu0 (by linarith)
  have hb1 : Real.sin (η * u) ≤ η * u := Real.sin_le hηu0.le
  have hsu : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith)
  have hr0 : 0 ≤ r := by
    have : 0 ≤ Real.sin (η * u) * r := by rw [hid]; positivity
    exact nonneg_of_mul_nonneg_right this hb0
  have hru : Real.sin u ≤ r * u := by
    have h1 : η * Real.sin u ≤ η * (r * u) := by
      rw [← hid]
      nlinarith
    exact le_of_mul_le_mul_left h1 hη
  constructor
  · have hj := Real.mul_le_sin hu0.le huπ
    have : 2 / Real.pi * u ≤ r * u := hj.trans hru
    exact le_of_mul_le_mul_right this hu0
  · have hc := sub_cube_div_six_le_sin hu0.le
    have : (1 - t ^ 2 / 24) * u ≤ r * u := by
      have e : (1 - t ^ 2 / 24) * u = u - u ^ 3 / 6 := by rw [hu]; ring
      rw [e]
      exact hc.trans hru
    exact le_of_mul_le_mul_right this hu0
theorem axialDirichlet_re_bounds {η : ℝ} {N : ℕ} (hN : η⁻¹ = 2 * (N : ℝ) + 1) {t : ℝ}
    (ht : |t| ≤ Real.pi) :
    2 / Real.pi ≤ (axialDirichlet η N (t : ℂ)).re ∧
      1 - (axialDirichlet η N (t : ℂ)).re ^ 2 ≤ 1 / 12 * t ^ 2 := by
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have main : 2 / Real.pi ≤ (axialDirichlet η N (t : ℂ)).re ∧
      1 - t ^ 2 / 24 ≤ (axialDirichlet η N (t : ℂ)).re := by
    rcases lt_trichotomy t 0 with h | h | h
    · have hneg : (axialDirichlet η N (t : ℂ)) = axialDirichlet η N ((-t : ℝ) : ℂ) := by
        rw [Complex.ofReal_neg, axialDirichlet_neg]
      have := axialDirichlet_re_bounds_of_pos hN (neg_pos.mpr h)
        (by rw [abs_of_neg h] at ht; exact ht)
      rw [hneg]
      simpa using this
    · subst h
      have h1 : (axialDirichlet η N ((0 : ℝ) : ℂ)).re = 1 := by
        simp [axialDirichlet_zero hN]
      rw [h1]
      constructor
      · rw [div_le_one (by linarith)]
        linarith
      · norm_num
    · exact axialDirichlet_re_bounds_of_pos hN h (by rwa [abs_of_pos h] at ht)
  refine ⟨main.1, ?_⟩
  have ht2 : t ^ 2 ≤ Real.pi ^ 2 := by
    rw [← sq_abs]
    have := abs_nonneg t
    nlinarith
  have hle : 0 ≤ 1 - t ^ 2 / 24 := by nlinarith
  have := main.2
  nlinarith [sq_nonneg (t ^ 2)]
theorem norm_axialDirichlet_le_of_shift {η : ℝ} {N : ℕ} (hN : η⁻¹ = 2 * (N : ℝ) + 1) {x θ : ℝ}
    (hx : |x| ≤ Real.pi / η) (hθ : |θ| ≤ 1 / 8) {p : ℂ} {n : ℤ}
    (hp : (x : ℂ) + Complex.I * (θ : ℂ) = p + 2 * (Real.pi : ℂ) * (n : ℂ))
    (hpre : |p.re| ≤ Real.pi) (hn : n ≠ 0) :
    ‖axialDirichlet η N ((x : ℂ) + Complex.I * (θ : ℂ))‖ ≤
        ‖Complex.sin (p / 2)‖ * (2 * |(n : ℝ)| - 1)⁻¹ ∧
      ‖Complex.sin (p / 2)‖ * (2 * |(n : ℝ)| - 1)⁻¹ ≤ 2 * (2 * |(n : ℝ)| - 1)⁻¹ := by
  have hη : 0 < η := by
    have : 0 < η⁻¹ := by rw [hN]; linarith
    exact inv_pos.mp this
  have hpi := Real.pi_pos
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    exact_mod_cast this
  have hm : 0 < 2 * |(n : ℝ)| - 1 := by linarith
  have hre : x = p.re + 2 * Real.pi * n := by
    have := congrArg Complex.re hp
    simpa using this
  have him : θ = p.im := by
    have := congrArg Complex.im hp
    simpa using this
  have hxlow : Real.pi * (2 * |(n : ℝ)| - 1) ≤ |x| := by
    have h1 : |2 * Real.pi * (n : ℝ)| ≤ |x| + |p.re| := by
      have : 2 * Real.pi * (n : ℝ) = x - p.re := by rw [hre]; ring
      rw [this]
      exact abs_sub _ _
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hpi] at h1
    nlinarith
  have hsin : ‖Complex.sin (((x : ℂ) + Complex.I * (θ : ℂ)) / 2)‖ = ‖Complex.sin (p / 2)‖ := by
    have e : ((x : ℂ) + Complex.I * (θ : ℂ)) / 2 = p / 2 + (n : ℂ) * (Real.pi : ℂ) := by
      rw [hp]; ring
    have hz : ∀ z : ℂ, ∀ n : ℤ, ‖Complex.sin (z + (n : ℂ) * (Real.pi : ℂ))‖ = ‖Complex.sin z‖ := by
      intro z n
      have := Complex.sin_antiperiodic.add_zsmul_eq (x := z) n
      rw [zsmul_eq_mul] at this
      rw [this]
      rcases Int.even_or_odd n with h | h
      · rw [Int.negOnePow_even n h]
        simp
      · rw [Int.negOnePow_odd n h]
        simp
    rw [e, hz]
  have hden : η * (2 * |(n : ℝ)| - 1) ≤
      ‖Complex.sin ((η : ℂ) * ((x : ℂ) + Complex.I * (θ : ℂ)) / 2)‖ := by
    have e : (η : ℂ) * ((x : ℂ) + Complex.I * (θ : ℂ)) / 2 =
        ((η * x / 2 : ℝ) : ℂ) + ((η * θ / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    have hre' : (Complex.sin ((η : ℂ) * ((x : ℂ) + Complex.I * (θ : ℂ)) / 2)).re =
        Real.sin (η * x / 2) * Real.cosh (η * θ / 2) := by
      have aux : ∀ a b c d : ℝ,
          ((a : ℂ) * (b : ℂ) + (c : ℂ) * (d : ℂ) * Complex.I).re = a * b := by
        intro a b c d
        simp [← Complex.ofReal_mul]
      rw [e, Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
        ← Complex.ofReal_cos, ← Complex.ofReal_sinh]
      exact aux _ _ _ _
    have h1 := Complex.abs_re_le_norm (Complex.sin ((η : ℂ) * ((x : ℂ) + Complex.I * (θ : ℂ)) / 2))
    rw [hre', abs_mul, abs_of_pos (Real.cosh_pos _)] at h1
    have hc := Real.one_le_cosh (η * θ / 2)
    have hs0 := abs_nonneg (Real.sin (η * x / 2))
    have h2 : |Real.sin (η * x / 2)| ≤
        ‖Complex.sin ((η : ℂ) * ((x : ℂ) + Complex.I * (θ : ℂ)) / 2)‖ := by nlinarith
    have ht : |η * x / 2| ≤ Real.pi / 2 := by
      rw [abs_div, abs_mul, abs_of_pos hη, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have : η * |x| ≤ η * (Real.pi / η) := by gcongr
      have e2 : η * (Real.pi / η) = Real.pi := by field_simp
      linarith
    have h3 := two_div_pi_mul_abs_le_abs_sin ht
    have e3 : |η * x / 2| = η * |x| / 2 := by
      rw [abs_div, abs_mul, abs_of_pos hη, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [e3] at h3
    have h4 : η * (2 * |(n : ℝ)| - 1) ≤ 2 / Real.pi * (η * |x| / 2) := by
      have e4 : 2 / Real.pi * (η * |x| / 2) = η * (|x| / Real.pi) := by field_simp
      rw [e4]
      have : 2 * |(n : ℝ)| - 1 ≤ |x| / Real.pi := by
        rw [le_div_iff₀ hpi]
        linarith
      gcongr
    linarith
  have hid := sin_mul_axialDirichlet hN ((x : ℂ) + Complex.I * (θ : ℂ))
  have hnorm := congrArg norm hid
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hη.le, hsin] at hnorm
  have hs0 := norm_nonneg (axialDirichlet η N ((x : ℂ) + Complex.I * (θ : ℂ)))
  constructor
  · rw [← div_eq_mul_inv, le_div_iff₀ hm]
    have h1 : η * (‖axialDirichlet η N ((x : ℂ) + Complex.I * (θ : ℂ))‖ *
        (2 * |(n : ℝ)| - 1)) ≤ η * ‖Complex.sin (p / 2)‖ := by
      rw [← hnorm]
      nlinarith
    exact le_of_mul_le_mul_left h1 hη
  · have hinv : 0 ≤ (2 * |(n : ℝ)| - 1)⁻¹ := (inv_pos.mpr hm).le
    have hsmall : ‖Complex.sin (p / 2)‖ ≤ 2 := by
      have e : p / 2 = ((p.re / 2 : ℝ) : ℂ) + ((p.im / 2 : ℝ) : ℂ) * Complex.I := by
        have := Complex.re_add_im p
        push_cast
        linear_combination (-1 / 2 : ℂ) * this
      have hb : |p.im / 2| ≤ 1 / 8 := by
        rw [← him, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have := abs_nonneg θ
        linarith
      rw [e, Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
        ← Complex.ofReal_cos, ← Complex.ofReal_sinh]
      have h1 := cosh_sub_one_le_of_abs_le_eighth hb
      have h2 := abs_sinh_le_of_abs_le_eighth hb
      have hy2 : (p.im / 2) ^ 2 ≤ 1 / 64 := by
        have := sq_le_sq' (neg_le_of_abs_le hb) (le_of_abs_le hb)
        nlinarith
      have hc0 := Real.cosh_pos (p.im / 2)
      have hsn := Real.abs_sin_le_one (p.re / 2)
      have hcn := Real.abs_cos_le_one (p.re / 2)
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hc0, mul_one]
      have hs1 := abs_nonneg (Real.sin (p.re / 2))
      have hc1 := abs_nonneg (Real.cos (p.re / 2))
      nlinarith
    gcongr
def decayFactor (n : ℤ) : ℝ :=
  (max 1 (2 * |(n : ℝ)| - 1))⁻¹ * (max 1 |(n : ℝ)|) ^ (-(1 / 4) : ℝ)
theorem decayFactor_nonneg (n : ℤ) : 0 ≤ decayFactor n := by
  unfold decayFactor
  positivity
theorem decayFactor_le (n : ℤ) :
    decayFactor n ≤ |(n : ℝ)| ^ (-(5 / 4) : ℝ) + if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst hn
    simp [decayFactor]
  · have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
      exact_mod_cast this
    have hpos : 0 < |(n : ℝ)| := by linarith
    rw [if_neg hn, add_zero, decayFactor, max_eq_right hn1,
      show (-(5 / 4) : ℝ) = -1 + -(1 / 4) by norm_num, Real.rpow_add hpos, Real.rpow_neg_one]
    have h1 : (max 1 (2 * |(n : ℝ)| - 1))⁻¹ ≤ |(n : ℝ)|⁻¹ := by
      apply inv_anti₀ hpos
      rcases le_total 1 (2 * |(n : ℝ)| - 1) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    gcongr
theorem summable_decayFactor : Summable decayFactor := by
  have h1 : Summable fun n : ℤ => |(n : ℝ)| ^ (-(5 / 4) : ℝ) :=
    Real.summable_abs_int_rpow (by norm_num)
  have h2 : Summable fun n : ℤ => if n = 0 then (1 : ℝ) else 0 :=
    (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  exact Summable.of_nonneg_of_le decayFactor_nonneg decayFactor_le (h1.add h2)
theorem harmonicTerm_le_prod (m : Fin 4 → ℤ) (hm : m ≠ 0) :
    (TorusMetric.supNormVec fun ν => (m ν : ℝ))⁻¹ * ∏ ν, oddHarmonicWeight (m ν) ≤
      ∏ ν, decayFactor (m ν) := by
  set M := TorusMetric.supNormVec fun ν => (m ν : ℝ) with hM
  have hcoord : ∀ ν, |(m ν : ℝ)| ≤ M := fun ν =>
    Finset.le_sup' (fun μ => |(m μ : ℝ)|) (Finset.mem_univ ν)
  have hM1 : 1 ≤ M := by
    obtain ⟨ν, hν⟩ : ∃ ν, m ν ≠ 0 := by
      by_contra h
      exact hm (funext fun ν => by_contra fun hν => h ⟨ν, hν⟩)
    have : (1 : ℝ) ≤ |(m ν : ℝ)| := by
      have : (1 : ℤ) ≤ |m ν| := Int.one_le_abs hν
      exact_mod_cast this
    exact this.trans (hcoord ν)
  have hM0 : 0 < M := by linarith
  have hfac : ∀ ν, M ^ (-(1 / 4) : ℝ) ≤ (max 1 |(m ν : ℝ)|) ^ (-(1 / 4) : ℝ) := by
    intro ν
    apply Real.rpow_le_rpow_of_nonpos (lt_max_of_lt_left one_pos) (max_le hM1 (hcoord ν))
    norm_num
  have hMinv : M⁻¹ = ∏ _ν : Fin 4, M ^ (-(1 / 4) : ℝ) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
      ← Real.rpow_mul hM0.le, ← Real.rpow_neg_one]
    norm_num
  rw [hMinv, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro ν _
    have : 0 ≤ oddHarmonicWeight (m ν) := by
      have h' : (0 : ℝ) < max 1 (2 * |(m ν : ℝ)| - 1) := lt_max_of_lt_left one_pos
      unfold oddHarmonicWeight
      positivity
    positivity
  · intro ν _
    rw [decayFactor, mul_comm, oddHarmonicWeight]
    have h' : (0 : ℝ) < max 1 (2 * |(m ν : ℝ)| - 1) := lt_max_of_lt_left one_pos
    have := hfac ν
    gcongr
theorem oddHarmonicWeightSum_lt_top : oddHarmonicWeightSum < ∞ := by
  set C := ∑' n, decayFactor n with hC
  have hfinite : ∀ t : Finset ℤ, ∑ n ∈ t, decayFactor n ≤ C := fun t =>
    summable_decayFactor.sum_le_tsum t fun n _ => decayFactor_nonneg n
  have hle : oddHarmonicWeightSum ≤ ENNReal.ofReal (C ^ 4) := by
    refine iSup_le fun s => ?_
    have hterm0 : ∀ m : {m : Fin 4 → ℤ // m ≠ 0}, 0 ≤ oddHarmonicWeightTerm m := by
      intro m
      have hM : 0 ≤ TorusMetric.supNormVec fun ν => ((m : Fin 4 → ℤ) ν : ℝ) :=
        (abs_nonneg _).trans (Finset.le_sup' (fun μ => |((m : Fin 4 → ℤ) μ : ℝ)|) (Finset.mem_univ 0))
      unfold oddHarmonicWeightTerm
      refine mul_nonneg (inv_nonneg.mpr hM) (Finset.prod_nonneg fun ν _ => ?_)
      unfold oddHarmonicWeight
      positivity
    rw [← ENNReal.ofReal_sum_of_nonneg fun m _ => hterm0 m]
    apply ENNReal.ofReal_le_ofReal
    set t : Finset ℤ := Finset.univ.biUnion fun ν : Fin 4 =>
      s.image fun m : {m : Fin 4 → ℤ // m ≠ 0} => m.1 ν
      with ht
    have hbox : ∀ m ∈ s, (m : Fin 4 → ℤ) ∈ Fintype.piFinset fun _ : Fin 4 => t := by
      intro m hm
      rw [Fintype.mem_piFinset]
      intro ν
      exact Finset.mem_biUnion.mpr ⟨ν, Finset.mem_univ ν, Finset.mem_image.mpr ⟨m, hm, rfl⟩⟩
    have hinj : Set.InjOn (fun m : {m : Fin 4 → ℤ // m ≠ 0} => (m : Fin 4 → ℤ)) s :=
      Subtype.val_injective.injOn
    calc ∑ m ∈ s, oddHarmonicWeightTerm m
        ≤ ∑ m ∈ s, ∏ ν, decayFactor ((m : Fin 4 → ℤ) ν) :=
          Finset.sum_le_sum fun m _ => harmonicTerm_le_prod m m.2
      _ = ∑ m ∈ s.image (fun m : {m : Fin 4 → ℤ // m ≠ 0} => (m : Fin 4 → ℤ)),
            ∏ ν, decayFactor (m ν) := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ m ∈ Fintype.piFinset fun _ : Fin 4 => t, ∏ ν, decayFactor (m ν) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm
            obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hm
            exact hbox m' hm'
          · intro m _ _
            exact Finset.prod_nonneg fun ν _ => decayFactor_nonneg _
      _ = ∏ _ν : Fin 4, ∑ n ∈ t, decayFactor n := by
          rw [Finset.prod_univ_sum]
      _ = (∑ n ∈ t, decayFactor n) ^ 4 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ C ^ 4 := by
          have := Finset.sum_nonneg fun n (_ : n ∈ t) => decayFactor_nonneg n
          have := hfinite t
          gcongr
  exact hle.trans_lt ENNReal.ofReal_lt_top
theorem exists_halfWidth {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) :
    ∃ N : ℕ, (finestMesh L k)⁻¹ = 2 * (N : ℝ) + 1 ∧
      freqWindow L k = Finset.Icc (-(N : ℤ)) N := by
  obtain ⟨N, hN⟩ := hL.1.pow (n := k)
  have hinv : (finestMesh L k)⁻¹ = 2 * (N : ℝ) + 1 := by
    have : ((L ^ k : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by
      rw [hN]; push_cast; ring
    rw [← this, finestMesh, meshAt]
    simp [zpow_neg]
  refine ⟨N, hinv, ?_⟩
  have hfl : ⌊1 / 2 * ((finestMesh L k)⁻¹ - 1)⌋ = (N : ℤ) := by
    rw [hinv, show (1 / 2 * (2 * (N : ℝ) + 1 - 1)) = (N : ℝ) by ring]
    exact Int.floor_natCast N
  rw [freqWindow, hfl]
theorem mesh_pos_and_le_one {η : ℝ} {N : ℕ} (hN : η⁻¹ = 2 * (N : ℝ) + 1) : 0 < η ∧ η ≤ 1 := by
  have hη : 0 < η := by
    have : 0 < η⁻¹ := by rw [hN]; linarith
    exact inv_pos.mp this
  refine ⟨hη, ?_⟩
  have h1 : η * (2 * (N : ℝ) + 1) = 1 := by rw [← hN]; exact mul_inv_cancel₀ hη.ne'
  nlinarith
theorem symbolSquare_eq (L k : ℕ) (q : Fin 4 → ℂ) :
    symbolSquare L k q = ∑ μ, axialSymbol (finestMesh L k) (q μ) *
      axialSymbol (finestMesh L k) (-q μ) := rfl
theorem realSymbolSquare_eq (L k : ℕ) (q' : Fin 4 → ℝ) :
    realSymbolSquare L k q' =
      ∑ ν, ‖axialSymbol (finestMesh L k) (q' ν)‖ ^ 2 := rfl
theorem dirichletSum_eq {L k N : ℕ} (h : freqWindow L k = Finset.Icc (-(N : ℤ)) N) (τ : ℂ) :
    dirichletSum L k τ = axialDirichlet (finestMesh L k) N τ := by
  rw [dirichletSum, h]
  rfl
theorem symbolSquare_toComplexVec {L k : ℕ} (hη : 0 < finestMesh L k) (q' : Fin 4 → ℝ) :
    symbolSquare L k (toComplexVec q') = (realSymbolSquare L k q' : ℂ) := by
  rw [symbolSquare_eq, realSymbolSquare_eq, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have e : toComplexVec q' μ = (q' μ : ℂ) := rfl
  rw [e, axialSymbol_mul_neg, norm_sq_axialSymbol hη]
  push_cast
  ring
theorem sum_four_bounds (T : Fin 4 → ℂ) (c : Fin 4 → ℝ)
    (h : ∀ ν, c ν - 1 / 40 ≤ (T ν).re ∧ (T ν).re ≤ 11 / 10 * c ν ∧
      |(T ν).im| ≤ 11 / 80 * (c ν + 1)) :
    ∑ ν, c ν - 1 / 10 ≤ (∑ ν, T ν).re ∧ (∑ ν, T ν).re ≤ 11 / 10 * ∑ ν, c ν ∧
      |(∑ ν, T ν).im| ≤ 11 / 80 * (∑ ν, c ν + 4) := by
  simp only [Fin.sum_univ_four, Complex.add_re, Complex.add_im]
  obtain ⟨a0, b0, c0⟩ := h 0
  obtain ⟨a1, b1, c1⟩ := h 1
  obtain ⟨a2, b2, c2⟩ := h 2
  obtain ⟨a3, b3, c3⟩ := h 3
  refine ⟨by linarith, by linarith, ?_⟩
  have e1 := abs_add_le ((T 0).im + (T 1).im + (T 2).im) (T 3).im
  have e2 := abs_add_le ((T 0).im + (T 1).im) (T 2).im
  have e3 := abs_add_le (T 0).im (T 1).im
  linarith
theorem symbolBounds {L k : ℕ} (hη : 0 < finestMesh L k)
    (hη1 : finestMesh L k ≤ 1) {q' θ : Fin 4 → ℝ}
    (hq' : ∀ ν, |q' ν| ≤ Real.pi / finestMesh L k) (hθ : ∀ ν, |θ ν| ≤ 1 / 8) :
    SymbolBounds L k q' θ := by
  have hb := fun ν => axialSymbol_mul_neg_bounds hη hη1 (q' ν) (θ ν) (hθ ν)
  have hD0 : 0 ≤ realSymbolSquare L k q' := by
    rw [realSymbolSquare_eq]; positivity
  set S := symbolSquare L k (complexPoint q' θ) with hSdef
  set D := realSymbolSquare L k q' with hDdef
  obtain ⟨hlow, hup, hIm⟩ : D - 1 / 10 ≤ S.re ∧ S.re ≤ 11 / 10 * D ∧
      |S.im| ≤ 11 / 80 * (D + 4) := sum_four_bounds _ _ hb
  have hplus : (S + 1).re = S.re + 1 := by simp
  refine ⟨fun ν => axialSymbol_norm_bounds hη (hq' ν), ?_, Complex.re_le_norm _, ?_, ?_, ?_⟩
  · rw [hplus]; linarith
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have himp : (S + 1).im = S.im := by simp
    rw [hplus, himp, abs_of_nonneg (by linarith)]
    linarith
  · intro ν
    exact ⟨norm_axialSymbol_le hη hη1 (q' ν) (θ ν) (hθ ν),
      norm_axialSymbol_neg_le hη hη1 (q' ν) (θ ν) (hθ ν)⟩
  · intro h4
    have := Complex.re_le_norm S
    linarith
theorem dirichletSumBounds {L k N : ℕ} (hN : (finestMesh L k)⁻¹ = 2 * (N : ℝ) + 1)
    (hF : freqWindow L k = Finset.Icc (-(N : ℤ)) N) {q' θ : Fin 4 → ℝ}
    (hq' : ∀ ν, |q' ν| ≤ Real.pi / finestMesh L k) (hθ : ∀ ν, |θ ν| ≤ 1 / 8) :
    DirichletSumBounds L k q' θ := by
  intro ν
  have hpt : complexPoint q' θ ν = (q' ν : ℂ) + Complex.I * (θ ν : ℂ) := rfl
  rw [dirichletSum_eq hF]
  refine ⟨?_, ?_, ?_⟩
  · rw [hpt]
    exact norm_axialDirichlet_le hN (q' ν) (θ ν) (hθ ν)
  · intro hq h0
    have hreal : complexPoint q' θ ν = (q' ν : ℂ) := by
      rw [hpt, h0]; simp
    rw [hreal]
    exact ⟨axialDirichlet_ofReal_im _ N _, axialDirichlet_re_bounds hN hq⟩
  · intro p n hp hpre hn
    rw [hpt] at hp ⊢
    exact norm_axialDirichlet_le_of_shift hN (hq' ν) (hθ ν) hp hpre hn
theorem claim_holds : Claim := by
  refine ⟨?_, oddHarmonicWeightSum_lt_top⟩
  intro L k hL _ q' θ hq' hθ
  obtain ⟨N, hN, hF⟩ := exists_halfWidth hL k
  obtain ⟨hη, hη1⟩ := mesh_pos_and_le_one hN
  exact ⟨symbolSquare_toComplexVec hη q', symbolBounds hη hη1 hq' hθ,
    dirichletSumBounds hN hF hq' hθ⟩
end YangMills.Construction.Tower.PlaneWaves.PlaneWaveBounds
end
