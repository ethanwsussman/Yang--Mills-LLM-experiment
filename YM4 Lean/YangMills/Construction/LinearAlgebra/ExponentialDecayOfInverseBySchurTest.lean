import YangMills.Construction.LinearAlgebra.ExponentialDecayOfInverseOfPositiveMatrix
import Mathlib
set_option autoImplicit false
open Matrix
noncomputable section
namespace YangMills.Construction.LinearAlgebra.DecayingInverse
variable {X : Type} [Fintype X]
lemma abs_exp_sub_one_le_abs_mul_exp_abs (u : ℝ) : |Real.exp u - 1| ≤ |u| * Real.exp |u| := by
  rcases le_total 0 u with hu | hu
  · have h1 : -u + 1 ≤ Real.exp (-u) := Real.add_one_le_exp (-u)
    have h2 : 0 < Real.exp u := Real.exp_pos u
    have h3 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have h4 : 1 ≤ Real.exp u := Real.one_le_exp hu
    rw [abs_of_nonneg (by linarith), abs_of_nonneg hu]
    nlinarith
  · have h1 : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
    have h2 : Real.exp u ≤ 1 := Real.exp_le_one_iff.mpr hu
    have h3 : 1 ≤ Real.exp (-u) := Real.one_le_exp (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonpos hu]
    nlinarith [mul_nonneg (neg_nonneg.mpr hu) (sub_nonneg.mpr h3)]
variable [DecidableEq X]
end YangMills.Construction.LinearAlgebra.DecayingInverse
