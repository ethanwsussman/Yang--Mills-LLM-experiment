import YangMills.Construction.DirichletOperator.FactsOfTheSettingInLevelUnitsProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.WeightedLength
variable {d : ℕ} {S : ℝ}
theorem lOneLength_nonneg (s : TorusSegment d) : 0 ≤ s.lOneLength :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem continuous_pointAt (s : TorusSegment d) : Continuous fun τ : ℝ => s.pointAt S τ := by apply _root_.YangMills.Construction.LevelUnitFacts.pointAt_continuous <;> assumption
end YangMills.Construction.WeightedLength
