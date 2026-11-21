import YangMills.Construction.DirichletOperator.LocalPartOfACubeOfTheSecondKindProof
import YangMills.Construction.Lattice.CubesLayersAndTopsOfADecreasingSequenceProof
import YangMills.Construction.Torus.CellsThatMeetAreNearProof
import YangMills.Construction.Torus.WeightedLengthsAndLocalLipschitzNumbersProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric MeasureTheory
namespace GeneralTorus
namespace EndpointsNear
variable {S : ℝ}
theorem abs_piSingle_apply_le (μ ν : Fin 4) (a : ℝ) : |(Pi.single μ a : Fin 4 → ℝ) ν| ≤ |a| := by
  by_cases h : ν = μ
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]
theorem continuous_pointAt (s : LiftedSegment) : Continuous (s.pointAt S) := by apply _root_.YangMills.Construction.Weighted.WeightedLengthProof.continuous_pointAt <;> assumption
variable {D : ScaleData}
theorem admitsPartition_levelSpacing {n : ℕ} (hn : n ≤ D.lastLevel) :
    D.AdmitsPartition (D.levelSpacing n) := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.admitsPartition_levelSpacing_of_le_lastLevel <;> assumption
end EndpointsNear
end GeneralTorus
end YangMills.Construction
end
