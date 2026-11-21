import YangMills.Construction.ResponseInTheExpansion.MomentsOfWeightedSums
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.Moments
theorem evenMomentOfWeightedSumBound_holds : EvenMomentOfWeightedSumBound := by
  intro Ω _ μ _ κ _ c g f r D hr hc hD hf hint hmom hb
  classical
  set S := ∑ i, c i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hc i
  have hnn : ∀ (z : ℝ), 0 ≤ z ^ (2 * r) := fun z => Even.pow_nonneg (even_two_mul r) _
  rcases hS0.eq_or_lt with h0 | hpos
  · have hc0 : ∀ i, c i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hc i).1 h0.symm i (Finset.mem_univ i)
      exact this
    have hz : (fun ω => f ω ^ (2 * r)) =ᵐ[μ] fun _ => 0 := by
      filter_upwards [hb] with ω hω
      have : |f ω| ≤ 0 := by simpa [hc0] using hω
      have h1 : f ω = 0 := abs_eq_zero.1 (le_antisymm this (abs_nonneg _))
      rw [h1]
      exact zero_pow (by omega)
    refine ⟨(integrable_zero _ _ _).congr hz.symm, ?_⟩
    rw [integral_congr_ae hz, ← h0]
    simp
    positivity
  · set h : Ω → ℝ := fun ω => S ^ (2 * r) * ∑ i, (c i / S) * g i ω ^ (2 * r) with hh
    have hhint : Integrable h μ :=
      (integrable_finsetSum _ fun i _ => (hint i).const_mul _).const_mul _
    have hdom : ∀ᵐ ω ∂μ, f ω ^ (2 * r) ≤ h ω := by
      filter_upwards [hb] with ω hω
      have hw : ∑ i, c i / S = 1 := by
        rw [← Finset.sum_div, ← hS]
        exact div_self hpos.ne'
      have hj := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun i => c i / S)
        (fun i => |g i ω|) (fun i _ => div_nonneg (hc i) hS0) hw (fun i _ => abs_nonneg _) (2 * r)
      have h1 : ∑ i, c i * |g i ω| = S * ∑ i, (c i / S) * |g i ω| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp
      have h2 : |f ω| ^ (2 * r) ≤ (S * ∑ i, (c i / S) * |g i ω|) ^ (2 * r) := by
        rw [← h1]
        exact pow_le_pow_left₀ (abs_nonneg _) hω _
      have h3 : f ω ^ (2 * r) = |f ω| ^ (2 * r) := by
        rw [pow_mul, pow_mul, sq_abs]
      have h4 : ∑ i, (c i / S) * |g i ω| ^ (2 * r) = ∑ i, (c i / S) * g i ω ^ (2 * r) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pow_mul, pow_mul, sq_abs]
      rw [h3]
      refine h2.trans ?_
      rw [mul_pow]
      simp only [hh]
      rw [← h4]
      exact mul_le_mul_of_nonneg_left hj (by positivity)
    refine ⟨?_, ?_⟩
    · refine hhint.mono' (hf.pow _) ?_
      filter_upwards [hdom] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn _)]
      exact hω
    · have h1 : ∫ ω, f ω ^ (2 * r) ∂μ ≤ ∫ ω, h ω ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => hnn _) hhint hdom
      refine h1.trans ?_
      simp only [hh]
      rw [integral_const_mul, integral_finsetSum _ fun i _ => (hint i).const_mul _]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      simp only [integral_const_mul]
      calc ∑ i, (c i / S) * ∫ ω, g i ω ^ (2 * r) ∂μ ≤ ∑ i, (c i / S) * D :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hmom i)
              (div_nonneg (hc i) hS0)
        _ = D := by
            rw [← Finset.sum_mul, ← Finset.sum_div, ← hS, div_self hpos.ne', one_mul]
end YangMills.Construction.Moments
end
