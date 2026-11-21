import YangMills.Construction.FormsOnATorus.DerivativesOfAnExponentialSum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ExponentialSums
private def derivTerm (c : (Fin 4 → ℤ) → ℂ) (w φ : (Fin 4 → ℤ) → ℝ) (d : ℕ) (z : Fin 4 → ℤ) (s : ℝ) : ℂ :=
  c z * (Complex.I * (w z : ℂ)) ^ d * Complex.exp (Complex.I * ((s * w z + φ z : ℝ) : ℂ))
private lemma norm_derivTerm (c : (Fin 4 → ℤ) → ℂ) (w φ : (Fin 4 → ℤ) → ℝ) (d : ℕ) (z : Fin 4 → ℤ) (s : ℝ) :
    ‖derivTerm c w φ d z s‖ = ‖c z‖ * |w z| ^ d := by
  unfold derivTerm
  rw [norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, norm_pow, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
private lemma hasDerivAt_derivTerm (c : (Fin 4 → ℤ) → ℂ) (w φ : (Fin 4 → ℤ) → ℝ) (d : ℕ) (z : Fin 4 → ℤ) (s : ℝ) :
    HasDerivAt (derivTerm c w φ d z) (derivTerm c w φ (d + 1) z s) s := by
  have h1 : HasDerivAt (fun s : ℝ => Complex.I * ((s * w z + φ z : ℝ) : ℂ)) (Complex.I * (w z : ℂ)) s := by
    have h0 : HasDerivAt (fun s : ℝ => s * w z + φ z) (w z) s := by
      simpa using ((hasDerivAt_id s).mul_const (w z)).add_const (φ z)
    exact h0.ofReal_comp.const_mul Complex.I
  have h2 := h1.cexp.const_mul (c z * (Complex.I * (w z : ℂ)) ^ d)
  unfold derivTerm
  refine h2.congr_deriv ?_
  rw [pow_succ]
  ring
private lemma hasDerivAt_tsum_derivTerm (c : (Fin 4 → ℤ) → ℂ) (w φ : (Fin 4 → ℤ) → ℝ)
    (hS : ∀ d : ℕ, Summable fun z => ‖c z‖ * |w z| ^ d) (d : ℕ) (s : ℝ) :
    HasDerivAt (fun s => ∑' z, derivTerm c w φ d z s) (∑' z, derivTerm c w φ (d + 1) z s) s := by
  refine hasDerivAt_tsum (y₀ := 0) (hS (d + 1)) (fun z y => hasDerivAt_derivTerm c w φ d z y)
    (fun z y => (norm_derivTerm c w φ (d + 1) z y).le) ?_ s
  exact Summable.of_norm ((hS d).congr fun z => (norm_derivTerm c w φ d z 0).symm ▸ rfl)
theorem iteratedDeriv_bound_exponentialSum : IteratedDerivBoundOfExponentialSum := by
  intro c w φ hS d t
  have key : ∀ d : ℕ, iteratedDeriv d (fun s : ℝ => ∑' z, c z * Complex.exp (Complex.I * ((s * w z + φ z : ℝ) : ℂ))) =
      fun s => ∑' z, derivTerm c w φ d z s := by
    intro d
    induction d with
    | zero =>
      funext s
      simp [derivTerm]
    | succ d ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      exact (hasDerivAt_tsum_derivTerm c w φ hS d s).deriv
  rw [key]
  have hs : Summable fun z => ‖derivTerm c w φ d z t‖ :=
    (hS d).congr fun z => (norm_derivTerm c w φ d z t).symm ▸ rfl
  refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq ?_)
  exact tsum_congr fun z => norm_derivTerm c w φ d z t
end YangMills.Construction.ExponentialSums
end
