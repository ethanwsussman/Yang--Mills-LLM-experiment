import YangMills.Construction.Lattice.DecayOfTheOneScaleGreenOperator
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N L j : ℕ}
private theorem norm_sq_eq_sum {s : Mesh N} {X : Type} [Fintype X] (f : ScaledFun d s X) :
    ‖f‖ ^ 2 = ∑ x, s.h ^ d * f x * f x := by
  rw [← real_inner_self_eq_norm_sq, ScaledFun.inner_eq]
private theorem addCircle_norm_coe_le_abs (hN : 0 < N) (r : ℝ) :
    ‖(r : AddCircle (N : ℝ))‖ ≤ |r| := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  by_cases h : |r| ≤ |(N : ℝ)| / 2
  · exact ((AddCircle.norm_coe_eq_abs_iff _ hN').mpr h).le
  · exact (AddCircle.norm_le_half_period _ hN').trans (not_le.mp h).le
abbrev _root_.YangMills.SharedProofs.p53979 := @addCircle_norm_coe_le_abs
section Indicator
variable {s : Mesh N} {ι : Type}
private theorem indicatorMul_apply (U : Set (GridPoint d s)) (f : MultiField d s ι)
    (q : ι × GridPoint d s) :
    MultiField.indicatorMul U f q = U.indicator 1 q.2 * f q := rfl
private theorem norm_indicatorMul_le [Fintype ι] (U : Set (GridPoint d s)) (f : MultiField d s ι) :
    ‖MultiField.indicatorMul U f‖ ≤ ‖f‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [norm_sq_eq_sum, norm_sq_eq_sum]
  refine sum_le_sum fun q _ => ?_
  by_cases h : q.2 ∈ U
  · simp [indicatorMul_apply, Set.indicator_of_mem h]
  · have h0 : 0 ≤ s.h ^ d * f q * f q := by
      rw [mul_assoc]
      exact mul_nonneg (pow_pos s.h_pos d).le (mul_self_nonneg _)
    simpa [indicatorMul_apply, Set.indicator_of_notMem h] using h0
end Indicator
namespace Scales
variable (S : Scales d L j N)
include S in
private theorem fineScale_pos : 0 < fineScale L j := S.fineMesh.h_pos
end Scales
end YangMills.Construction.PeriodicLattice
