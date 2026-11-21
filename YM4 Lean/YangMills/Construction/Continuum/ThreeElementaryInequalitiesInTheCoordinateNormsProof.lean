import YangMills.Construction.Continuum.ThreeElementaryInequalitiesInTheCoordinateNorms
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.CoordNormBounds
open EuclideanCoords
theorem abs_apply_le_supCoord {D : ℕ} (w : Fin D → ℝ) (i : Fin D) : |w i| ≤ supCoord w :=
  le_ciSup (f := fun ι => |w ι|) (Set.finite_range _).bddAbove i
theorem supCoord_le_sqrtSumSq {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    supCoord w ≤ sqrtSumSq w := by
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  refine ciSup_le fun i => Real.le_sqrt_of_sq_le ?_
  rw [sq_abs]
  exact Finset.single_le_sum (f := fun ι => w ι ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ i)
theorem sqrtSumSq_le_sqrt_mul_supCoord {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    sqrtSumSq w ≤ Real.sqrt (D : ℝ) * supCoord w := by
  have hm : 0 ≤ supCoord w := (abs_nonneg _).trans (abs_apply_le_supCoord w ⟨0, hD⟩)
  have hsum : ∑ ι, w ι ^ 2 ≤ (D : ℝ) * supCoord w ^ 2 := by
    calc ∑ ι, w ι ^ 2 ≤ ∑ _ι : Fin D, supCoord w ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (abs_apply_le_supCoord w i) 2
      _ = (D : ℝ) * supCoord w ^ 2 := by simp
  unfold sqrtSumSq
  calc Real.sqrt (∑ ι, w ι ^ 2) ≤ Real.sqrt ((D : ℝ) * supCoord w ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (D : ℝ) * supCoord w := by
      rw [Real.sqrt_mul (Nat.cast_nonneg D), Real.sqrt_sq hm]
theorem inequalitiesClaim_holds : inequalitiesClaim := by
  refine ⟨fun D hD w => ⟨supCoord_le_sqrtSumSq hD w, sqrtSumSq_le_sqrt_mul_supCoord hD w⟩,
    fun s v hv => ?_, fun s _ k => ?_⟩
  · have h := Real.pow_div_factorial_le_exp v hv s
    have hs : (0 : ℝ) < (s.factorial : ℝ) := by exact_mod_cast s.factorial_pos
    rwa [div_le_iff₀' hs] at h
  · exact Nat.le_of_dvd (Nat.factorial_pos _)
      (Nat.prod_factorial_dvd_factorial_sum Finset.univ k)
end YangMills.Construction.CoordNormBounds
