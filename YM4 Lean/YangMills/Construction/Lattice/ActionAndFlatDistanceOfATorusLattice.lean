import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
def torusDist (L m : ℕ) (u v : FourTorus L m) : ℝ := torusEuclidDist L m u v
theorem isLeast_torusDist_torusProj (hL : 0 < L) (x y : Fin 4 → ℝ) :
    IsLeast (range fun k : Fin 4 → ℤ =>
        TorusMetric.euclidNormVec (x - y - TestFunctions.latticeTranslate (torusSide L m) k))
      (torusDist L m (TorusMetric.torusProj (torusSide L m) x)
        (TorusMetric.torusProj (torusSide L m) y)) := by
  have hpos : 0 < torusSide L m := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    unfold torusSide
    positivity
  have hmin : IsLeast (range fun k : Fin 4 → ℤ =>
      TorusMetric.euclidNormVec (x - y - TestFunctions.latticeTranslate (torusSide L m) k))
      (TorusMetric.euclidNormVec (x - y - TestFunctions.latticeTranslate (torusSide L m)
        fun μ => round ((x - y) μ / torusSide L m))) := by
    refine ⟨⟨_, rfl⟩, ?_⟩
    rintro _ ⟨k, rfl⟩
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun μ _ => ?_)
    refine sq_le_sq.mpr ?_
    have hr := round_le ((x - y) μ / torusSide L m) (k μ)
    have hs : ∀ z : ℤ, |(x - y) μ - torusSide L m * (z : ℝ)| =
        torusSide L m * |(x - y) μ / torusSide L m - (z : ℝ)| := fun z => by
      rw [← abs_of_pos hpos, ← abs_mul, abs_of_pos hpos, mul_sub, mul_div_cancel₀ _ hpos.ne']
    simp only [Pi.sub_apply, TestFunctions.latticeTranslate] at hr hs ⊢
    rw [hs, hs]
    exact mul_le_mul_of_nonneg_left hr hpos.le
  rw [torusDist, torusEuclidDist_torusProj, hmin.csInf_eq]
  exact hmin
end YangMills.Construction.PeriodicLattice
