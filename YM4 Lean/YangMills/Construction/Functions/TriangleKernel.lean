import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TriangleKernel
open Real
structure IsSmearingSeq (s : ℤ → ℤ) : Prop where
  periodic : ∀ n, s (n + 4) = s n
  zero : s 0 = 0
  one : s 1 = 1
  two : s 2 = -2
  three : s 3 = 1
def smearingSeq (n : ℤ) : ℤ :=
  if n % 4 = 0 then 0 else if n % 4 = 1 then 1 else if n % 4 = 2 then -2 else 1
theorem isSmearingSeq_smearingSeq : IsSmearingSeq smearingSeq where
  periodic n := by
    have h : (n + 4) % 4 = n % 4 := by omega
    simp only [smearingSeq, h]
  zero := by decide
  one := by decide
  two := by decide
  three := by decide
structure IsTentFunction (g : ℝ → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ g x
  periodic : Function.Periodic g (2 * π)
  formula : ∀ x, |x| ≤ π → g x = 8 * max (1 - 4 * |x| / π) 0
def tentFunction (x : ℝ) : ℝ :=
  8 * max (1 - 4 * |toIocMod Real.two_pi_pos (-π) x| / π) 0
theorem abs_toIocMod_le_pi (x : ℝ) : |toIocMod Real.two_pi_pos (-π) x| ≤ π := by
  have h := toIocMod_mem_Ioc Real.two_pi_pos (-π) x
  rw [abs_le]
  constructor
  · exact h.1.le
  · have h2 := h.2
    linarith
theorem abs_toIocMod_eq_of_abs_le {x : ℝ} (hx : |x| ≤ π) :
    |toIocMod Real.two_pi_pos (-π) x| = |x| := by
  obtain ⟨h1, h2⟩ := abs_le.mp hx
  rcases h1.eq_or_lt with h | h
  · have hv : toIocMod Real.two_pi_pos (-π) (-π) = π := by
      have h' : toIocMod Real.two_pi_pos (-π) (-π + 2 * π) = -π + 2 * π :=
        (toIocMod_eq_self Real.two_pi_pos).mpr
          ⟨by linarith [Real.pi_pos], le_refl _⟩
      rw [toIocMod_add_right] at h'
      rw [h']
      ring
    rw [← h, hv, abs_neg]
  · rw [(toIocMod_eq_self Real.two_pi_pos).mpr ⟨h, by linarith⟩]
theorem isTentFunction_tentFunction : IsTentFunction tentFunction where
  nonneg x := mul_nonneg (by norm_num) (le_max_right _ _)
  periodic x := by simp only [tentFunction, toIocMod_add_right]
  formula x hx := by rw [tentFunction, abs_toIocMod_eq_of_abs_le hx]
def tentFourierCoeff (n : ℤ) : ℂ :=
  1 / (2 * π) * ∫ x in (-π)..π, (tentFunction x : ℂ) * Complex.exp (-(Complex.I * n * x))
end YangMills.Construction.TriangleKernel
