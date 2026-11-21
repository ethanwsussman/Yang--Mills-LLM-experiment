import YangMills.Construction.RunningCouplingSlope.FirstOrderOfTheLeastPoint
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def FirstVariationExists : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ B : edgeFormSpace L n k k, ∃ t : LevelTriple L n k, IsFirstVariation a B t
end YangMills.Construction.RunningCouplingSlope
end
