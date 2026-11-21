import YangMills.Construction.DirichletOperator.FactsOfTheSettingInLevelUnitsProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open YangMills.Construction.Torus YangMills.Construction.WeightedLength
noncomputable section
namespace YangMills.Construction.WeightedLength.ChainGrowth
variable {d : ℕ} {S : ℝ}
theorem lengthWithin_append (A B : List (TorusSegment d)) (X : Set (PeriodicTorus d S)) :
    lengthWithin (A ++ B) X = lengthWithin A X + lengthWithin B X := by
  simp [lengthWithin]
theorem lOneLength_nonneg (s : TorusSegment d) : 0 ≤ s.lOneLength :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem weightedTerm_nonneg (s : TorusSegment d) (X : Set (PeriodicTorus d S)) :
    0 ≤ s.lOneLength * (volume {τ ∈ Icc (0 : ℝ) 1 | s.pointAt S τ ∈ X}).toReal :=
  mul_nonneg (lOneLength_nonneg s) ENNReal.toReal_nonneg
theorem segmentUnion_append (A B : List (TorusSegment d)) :
    segmentUnion S (A ++ B) = segmentUnion S A ∪ segmentUnion S B := by apply _root_.YangMills.Construction.LevelUnitFacts.segmentUnion_append <;> assumption
theorem continuous_pointAt (s : TorusSegment d) : Continuous (s.pointAt S) := by apply _root_.YangMills.Construction.LevelUnitFacts.pointAt_continuous <;> assumption
end YangMills.Construction.WeightedLength.ChainGrowth
