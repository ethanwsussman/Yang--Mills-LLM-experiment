import YangMills.Construction.DirichletOperator.AveragingOperatorsAgreeOnTheLocalTorusProof
import YangMills.Construction.DirichletOperator.WhereThePartitionFunctionOfACubeLives
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
open YangMills.Construction.Torus YangMills.Construction.PartitionCubes
noncomputable section
namespace YangMills.Construction.ThickenedCubeLocation
theorem supNorm_eq_norm {S : ℝ} (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem supSetDist_singleton_le_add {S : ℝ} (A : Set (PeriodicTorus 4 S)) (x y : PeriodicTorus 4 S) :
    supSetDist {x} A ≤ supSetDist {y} A + ENNReal.ofReal (supNorm (x - y)) := by
  rw [← tsub_le_iff_right]
  refine le_iInf₂ fun p hp => le_iInf₂ fun q hq => ?_
  obtain rfl : p = y := hp
  rw [tsub_le_iff_right]
  have h₀ : supSetDist {x} A ≤ ENNReal.ofReal (supNorm (x - q)) :=
    iInf₂_le_of_le x rfl (iInf₂_le q hq)
  refine h₀.trans ?_
  rw [supNorm_eq_norm, supNorm_eq_norm, supNorm_eq_norm,
    ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : x - q = (p - q) + (x - p) := by abel
  rw [e]
  exact norm_add_le _ _
end YangMills.Construction.ThickenedCubeLocation
end
