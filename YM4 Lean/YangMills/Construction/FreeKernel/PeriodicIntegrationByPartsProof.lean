import YangMills.Construction.FreeKernel.PeriodicIntegrationByParts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.PeriodicIntegration
open Complex
theorem cexp_I_mul_int_mul_pi_eq_neg_pi (m : ℤ) :
    Complex.exp (I * (m : ℂ) * ((Real.pi : ℝ) : ℂ)) =
      Complex.exp (I * (m : ℂ) * ((-Real.pi : ℝ) : ℂ)) := by
  have h : I * (m : ℂ) * ((Real.pi : ℝ) : ℂ) =
      I * (m : ℂ) * ((-Real.pi : ℝ) : ℂ) + (m : ℂ) * (2 * Real.pi * I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
theorem integral_character_mul_eq_deriv (f : ℝ → ℂ) (m : ℤ) (hm : m ≠ 0) (hf : ContDiff ℝ 1 f)
    (hper : Function.Periodic f (2 * Real.pi)) :
    ∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (m : ℂ) * (θ : ℂ)) * f θ =
      (I / (m : ℂ)) *
        ∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (m : ℂ) * (θ : ℂ)) * deriv f θ := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hdu : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => Complex.exp (I * (m : ℂ) * (θ : ℂ)))
      (I * (m : ℂ) * Complex.exp (I * (m : ℂ) * (θ : ℂ))) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ => I * (m : ℂ) * (θ : ℂ)) (I * (m : ℂ)) θ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).const_mul (I * (m : ℂ))
    have h2 := h1.cexp
    convert h2 using 1
    ring
  have hdv : ∀ θ : ℝ, HasDerivAt f (deriv f θ) θ := fun θ =>
    ((hf.differentiable (by norm_num)) θ).hasDerivAt
  have hcont' : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hexpc : Continuous (fun θ : ℝ => Complex.exp (I * (m : ℂ) * (θ : ℂ))) := by fun_prop
  have hu'c : Continuous (fun θ : ℝ => I * (m : ℂ) * Complex.exp (I * (m : ℂ) * (θ : ℂ))) :=
    continuous_const.mul hexpc
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -Real.pi) (b := Real.pi)
    (fun θ _ => hdu θ) (fun θ _ => hdv θ)
    (hu'c.intervalIntegrable _ _) (hcont'.intervalIntegrable _ _)
  have hfb : f Real.pi = f (-Real.pi) := by
    have := hper (-Real.pi)
    rw [← this]
    congr 1
    ring
  rw [hfb, cexp_I_mul_int_mul_pi_eq_neg_pi m, sub_self, zero_sub] at hparts
  have hpull : ∫ θ in (-Real.pi)..Real.pi,
        I * (m : ℂ) * Complex.exp (I * (m : ℂ) * (θ : ℂ)) * f θ =
      I * (m : ℂ) * ∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (m : ℂ) * (θ : ℂ)) * f θ := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext θ
    ring
  rw [hparts, hpull]
  have hI : I * I = -1 := Complex.I_mul_I
  field_simp
  linear_combination (∫ θ in (-Real.pi)..Real.pi,
    Complex.exp (I * (m : ℂ) * (θ : ℂ)) * f θ) * hI
theorem periodicFourierIntegrationByParts_proof : PeriodicFourierIntegrationByParts := by
  intro n
  induction n with
  | zero =>
    intro f m _ _ _
    simp
  | succ n ih =>
    intro f m hm hf hper
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hf' : ContDiff ℝ n (deriv f) := by
      exact ((contDiff_succ_iff_deriv (n := n)).1 (by exact_mod_cast hf)).2.2
    have hper' : Function.Periodic (deriv f) (2 * Real.pi) := by
      intro θ
      have h : (fun x => f (x + 2 * Real.pi)) = f := funext hper
      have := deriv_comp_add_const f (2 * Real.pi) θ
      rw [h] at this
      exact this.symm
    rw [integral_character_mul_eq_deriv f m hm hf1 hper, ih (deriv f) m hm hf' hper',
      iteratedDeriv_succ', pow_succ]
    ring
end YangMills.Construction.FreeKernel.PeriodicIntegration
end
