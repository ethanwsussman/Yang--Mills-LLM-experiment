import YangMills.Construction.FreeKernel.MonomialFactorDerivatives
import YangMills.Construction.FreeKernel.SymbolDerivatives
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open Complex YangMills.Construction.LatticeKernel YangMills.Construction.Constants.HeatKernel
open scoped ContDiff
namespace MonomialFactors
lemma two_le_symmetryConstant : 2 ≤ symmetryConstant := by
  unfold symmetryConstant
  nlinarith [Real.pi_gt_three]
lemma diffOrder_le_two (α : DiffKind) : diffOrder α ≤ 2 := by
  cases α <;> simp [diffOrder]
lemma descFactorial_le_two_of_le_two {b : ℕ} (hb : b ≤ 2) (k : ℕ) : b.descFactorial k ≤ 2 := by
  interval_cases b <;> rcases k with _ | _ | _ | j <;> simp [Nat.descFactorial]
lemma hasDerivAt_const_mul_ofReal_pow (c : ℂ) (b : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => c * (y : ℂ) ^ b) (c * ((b : ℂ) * (x : ℂ) ^ (b - 1))) x := by
  have h : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  simpa using (h.pow b).const_mul c
lemma iteratedDeriv_const_mul_ofReal_pow (k : ℕ) : ∀ (c : ℂ) (b : ℕ),
    iteratedDeriv k (fun y : ℝ => c * (y : ℂ) ^ b) =
      fun x : ℝ => c * (b.descFactorial k : ℂ) * (x : ℂ) ^ (b - k) := by
  induction k with
  | zero =>
    intro c b
    funext x
    simp
  | succ j ih =>
    intro c b
    rw [iteratedDeriv_succ']
    have hd : deriv (fun y : ℝ => c * (y : ℂ) ^ b) =
        fun y : ℝ => (c * (b : ℂ)) * (y : ℂ) ^ (b - 1) := by
      funext x
      rw [(hasDerivAt_const_mul_ofReal_pow c b x).deriv]
      ring
    rw [hd, ih]
    funext x
    rcases b with _ | b
    · simp
    · rw [Nat.succ_descFactorial_succ, Nat.add_sub_cancel, Nat.add_sub_add_right]
      push_cast
      ring
lemma iteratedDeriv_I_mul_pow (b k : ℕ) (θ : ℝ) :
    iteratedDeriv k (fun x : ℝ => (I * (x : ℂ)) ^ b) θ =
      I ^ b * (b.descFactorial k : ℂ) * (θ : ℂ) ^ (b - k) := by
  have h : (fun x : ℝ => (I * (x : ℂ)) ^ b) = fun x : ℝ => I ^ b * (x : ℂ) ^ b := by
    funext x
    rw [mul_pow]
  rw [h, iteratedDeriv_const_mul_ofReal_pow]
lemma iteratedDeriv_I_mul_pow_eq_zero {b k : ℕ} (h : b < k) (θ : ℝ) :
    iteratedDeriv k (fun x : ℝ => (I * (x : ℂ)) ^ b) θ = 0 := by
  rw [iteratedDeriv_I_mul_pow, Nat.descFactorial_of_lt h]
  simp
lemma norm_iteratedDeriv_I_mul_pow_le {b : ℕ} (hb : b ≤ 2) (k : ℕ) (θ : ℝ) :
    ‖iteratedDeriv k (fun x : ℝ => (I * (x : ℂ)) ^ b) θ‖ ≤ 2 * |θ| ^ (b - k) := by
  rw [iteratedDeriv_I_mul_pow, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_I,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, one_pow, one_mul]
  have h : (b.descFactorial k : ℝ) ≤ 2 := by
    exact_mod_cast descFactorial_le_two_of_le_two hb k
  gcongr
lemma contDiff_I_mul_pow (b : ℕ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun x : ℝ => (I * (x : ℂ)) ^ b) :=
  (contDiff_const.mul Complex.ofRealCLM.contDiff).pow b
lemma contDiff_symbolError {n : WithTop ℕ∞} : ContDiff ℝ n symbolError := by
  have h : symbolError = fun θ : ℝ => 2 - 2 * Real.cos θ - θ ^ 2 := by
    funext θ
    rfl
  rw [h]
  exact (contDiff_const.sub (contDiff_const.mul Real.contDiff_cos)).sub (contDiff_id.pow 2)
lemma contDiff_ofReal_symbolError {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun x : ℝ => (symbolError x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp contDiff_symbolError
lemma iteratedDeriv_ofReal_comp (k : ℕ) : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f →
    iteratedDeriv k (fun x : ℝ => (f x : ℂ)) = fun x : ℝ => ((iteratedDeriv k f x : ℝ) : ℂ) := by
  induction k with
  | zero =>
    intro f _
    funext x
    simp
  | succ j ih =>
    intro f hf
    have hd : deriv (fun x : ℝ => (f x : ℂ)) = fun x : ℝ => ((deriv f x : ℝ) : ℂ) := by
      funext x
      exact ((hf.differentiable (by simp)) x).hasDerivAt.ofReal_comp.deriv
    rw [iteratedDeriv_succ', hd, ih (deriv f) (contDiff_infty_iff_deriv.1 hf).2]
    funext x
    rw [iteratedDeriv_succ']
lemma pow_mul_pow_le_pi_sq_mul_pow {y : ℝ} (hy : 0 ≤ y) (hyπ : y ≤ Real.pi) {a i k : ℕ}
    (ha : a ≤ 2) (hia : i ≤ a) (hik : i ≤ k) :
    y ^ (a - i) * y ^ (4 - (k - i)) ≤ Real.pi ^ 2 * y ^ (a + 4 - k) := by
  have hπ : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  obtain ⟨e, he, he2⟩ : ∃ e, (a - i) + (4 - (k - i)) = (a + 4 - k) + e ∧ e ≤ 2 :=
    ⟨(a - i) + (4 - (k - i)) - (a + 4 - k), by omega, by omega⟩
  rw [← pow_add, he, pow_add, mul_comm]
  have h1 : y ^ e ≤ Real.pi ^ 2 :=
    (pow_le_pow_left₀ hy hyπ e).trans (pow_le_pow_right₀ hπ he2)
  gcongr
lemma norm_iteratedDeriv_I_mul_pow_mul_symbolError_le
    (hψ : ∀ (k : ℕ) (θ : ℝ), |iteratedDeriv k symbolError θ| ≤ symmetryConstant * |θ| ^ (4 - k))
    {b : ℕ} (hb : b ≤ 2) {n k : ℕ} (hk : k ≤ n) {θ : ℝ} (hθ : |θ| ≤ Real.pi) :
    ‖iteratedDeriv k (fun x : ℝ => (I * (x : ℂ)) ^ b * (symbolError x : ℂ)) θ‖ ≤
      2 ^ (n + 1) * Real.pi ^ 2 * symmetryConstant * |θ| ^ (b + 4 - k) := by
  have hC : 0 ≤ symmetryConstant := by linarith [two_le_symmetryConstant]
  have hy : 0 ≤ |θ| := abs_nonneg θ
  set K : ℝ := 2 * symmetryConstant * (Real.pi ^ 2 * |θ| ^ (b + 4 - k)) with hK
  have hterm : ∀ i ∈ Finset.range (k + 1),
      ‖(k.choose i : ℂ) * iteratedDeriv i (fun x : ℝ => (I * (x : ℂ)) ^ b) θ *
        iteratedDeriv (k - i) (fun x : ℝ => (symbolError x : ℂ)) θ‖ ≤
      (k.choose i : ℝ) * K := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    by_cases hib : b < i
    · rw [iteratedDeriv_I_mul_pow_eq_zero hib]
      simp only [mul_zero, zero_mul, norm_zero]
      positivity
    · have hib' : i ≤ b := not_lt.1 hib
      have h1 := norm_iteratedDeriv_I_mul_pow_le hb i θ
      have h2 : ‖iteratedDeriv (k - i) (fun x : ℝ => (symbolError x : ℂ)) θ‖ ≤
          symmetryConstant * |θ| ^ (4 - (k - i)) := by
        rw [iteratedDeriv_ofReal_comp (k - i) symbolError contDiff_symbolError]
        simpa [Complex.norm_real, Real.norm_eq_abs] using hψ (k - i) θ
      have h3 := pow_mul_pow_le_pi_sq_mul_pow hy hθ hb hib' hik
      rw [norm_mul, norm_mul, Complex.norm_natCast, mul_assoc]
      gcongr
      calc ‖iteratedDeriv i (fun x : ℝ => (I * (x : ℂ)) ^ b) θ‖ *
            ‖iteratedDeriv (k - i) (fun x : ℝ => (symbolError x : ℂ)) θ‖
          ≤ (2 * |θ| ^ (b - i)) * (symmetryConstant * |θ| ^ (4 - (k - i))) := by gcongr
        _ = 2 * symmetryConstant * (|θ| ^ (b - i) * |θ| ^ (4 - (k - i))) := by ring
        _ ≤ K := by
          rw [hK]
          gcongr
  have hfun : (fun x : ℝ => (I * (x : ℂ)) ^ b * (symbolError x : ℂ)) =
      (fun x : ℝ => (I * (x : ℂ)) ^ b) * (fun x : ℝ => (symbolError x : ℂ)) := rfl
  rw [hfun, iteratedDeriv_mul (contDiff_I_mul_pow b).contDiffAt
    contDiff_ofReal_symbolError.contDiffAt]
  calc _ ≤ ∑ i ∈ Finset.range (k + 1),
        ‖(k.choose i : ℂ) * iteratedDeriv i (fun x : ℝ => (I * (x : ℂ)) ^ b) θ *
          iteratedDeriv (k - i) (fun x : ℝ => (symbolError x : ℂ)) θ‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K := Finset.sum_le_sum hterm
    _ = 2 ^ k * K := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring
    _ ≤ 2 ^ n * K := by
      have : (2 : ℝ) ^ k ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hk
      gcongr
    _ = 2 ^ (n + 1) * Real.pi ^ 2 * symmetryConstant * |θ| ^ (b + 4 - k) := by
      rw [hK]
      ring
end MonomialFactors
open MonomialFactors in
theorem monomialFactorDerivativeBounds (h : SymbolDerivativeBounds) :
    MonomialFactorDerivativeBounds := by
  obtain ⟨_, _, _, ⟨_, hψ, _⟩, _⟩ := h
  refine ⟨fun α k θ => ?_, fun α n k hk θ hθ => ?_⟩
  · calc ‖iteratedDeriv k (fun x : ℝ => (I * (x : ℂ)) ^ diffOrder α) θ‖
        ≤ 2 * |θ| ^ (diffOrder α - k) := norm_iteratedDeriv_I_mul_pow_le (diffOrder_le_two α) k θ
      _ ≤ symmetryConstant * |θ| ^ (diffOrder α - k) := by
        have := two_le_symmetryConstant
        gcongr
  · exact norm_iteratedDeriv_I_mul_pow_mul_symbolError_le hψ (diffOrder_le_two α) hk (abs_le.2 hθ)
end YangMills.Construction.FreeKernel
end
