import YangMills.Construction.TestSpaces.PointsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.BoundsOnEverySide
open YangMills.Construction.TestFunctions
def unitMassBumps : Set ((Fin 4 → ℝ) → ℝ) :=
  {g | g ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) ∧
    tsupport g ⊆ closedBallR4 0 1 ∧ ∫ x, g x = 1}
end YangMills.Construction.BoundsOnEverySide
end
