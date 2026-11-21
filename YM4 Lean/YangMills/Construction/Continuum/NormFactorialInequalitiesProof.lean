import YangMills.Construction.Continuum.NormFactorialInequalities
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ElementaryInequalities
theorem euclidNorm_eq_sqrt_sum {D : ℕ} (v : Fin D → ℝ) :
    euclidNorm v = Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
  unfold euclidNorm
  rw [EuclideanSpace.norm_eq]
theorem norm_le_euclidNorm {D : ℕ} (v : Fin D → ℝ) : ‖v‖ ≤ euclidNorm v := by
  rw [euclidNorm_eq_sqrt_sum, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ i)
theorem euclidNorm_le_sqrt_dim_mul_norm {D : ℕ} (v : Fin D → ℝ) :
    euclidNorm v ≤ Real.sqrt (D : ℝ) * ‖v‖ := by
  have hle : ∑ i, ‖v i‖ ^ 2 ≤ (D : ℝ) * ‖v‖ ^ 2 := by
    calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin D, ‖v‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
      _ = (D : ℝ) * ‖v‖ ^ 2 := by simp
  rw [euclidNorm_eq_sqrt_sum]
  calc Real.sqrt (∑ i, ‖v i‖ ^ 2) ≤ Real.sqrt ((D : ℝ) * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt (D : ℝ) * ‖v‖ := by
      rw [Real.sqrt_mul (Nat.cast_nonneg D), Real.sqrt_sq (norm_nonneg v)]
theorem normPowerFactorialBounds_holds : NormPowerFactorialBounds := by
  refine ⟨fun D _ v => ⟨norm_le_euclidNorm v, euclidNorm_le_sqrt_dim_mul_norm v⟩, fun s t ht => ?_,
    fun s _ k => ?_⟩
  · have hexp := Real.pow_div_factorial_le_exp t ht s
    have hpos : (0 : ℝ) < (s.factorial : ℝ) := by exact_mod_cast s.factorial_pos
    rwa [div_le_iff₀' hpos] at hexp
  · exact Nat.le_of_dvd (Nat.factorial_pos _)
      (Nat.prod_factorial_dvd_factorial_sum Finset.univ k)
end YangMills.Construction.ElementaryInequalities
