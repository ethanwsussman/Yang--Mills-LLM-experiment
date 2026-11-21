import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAtTheLastFarLevelInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.SupTestFunctionsAreTestFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open TestFunctions
private theorem supDist_le_dist (x y : EuclideanFourSpace) : supDist x y ≤ dist x y := by apply _root_.YangMills.SharedProofs.p2932 <;> assumption
private theorem norm_le_two_mul_of_abs_coord_le (x : EuclideanFourSpace) (R : ℝ) (hR : 0 ≤ R)
    (h : ∀ a, |x a| ≤ R) : ‖x‖ ≤ 2 * R := by
  have hsq : ‖x‖ ^ 2 ≤ (2 * R) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hterm : ∀ a ∈ (Finset.univ : Finset (Fin 4)), ‖x a‖ ^ 2 ≤ R ^ 2 := fun a _ => by
      rw [Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (h a) 2
    calc ∑ a, ‖x a‖ ^ 2 ≤ ∑ _a : Fin 4, R ^ 2 := Finset.sum_le_sum hterm
      _ = (2 * R) ^ 2 := by simp; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
theorem supTestFamilyIsTestFamily : supTestFamilyIsTestFamilyStatement := by
  intro k R d φ h
  refine ⟨fun i => ?_, h.abs_le_one, fun i x hx => ?_, fun i j hij x hx y hy => ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq]
    simpa using (h.lipschitz i x y).trans (supDist_le_dist x y)
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_two_mul_of_abs_coord_le x R ((abs_nonneg _).trans (h.abs_coord_le i x hx 0)) (h.abs_coord_le i x hx)
  · exact (h.le_supDist i j hij x hx y hy).trans (supDist_le_dist x y)
end YangMills.Construction.MomentLaw
end
