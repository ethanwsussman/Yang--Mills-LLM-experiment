import YangMills.Construction.RunningCouplingSlope.FirstOrderOfTheLeastPoint
import YangMills.Construction.RunningCouplingSlope.SystemOfTheFirstOrder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def FirstVariationSolvesSystem : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ (B : edgeFormSpace L n k k) (τ : LevelTriple L n k), IsFirstVariation a B τ →
      SolvesFirstOrderSystem a B τ
end YangMills.Construction.RunningCouplingSlope
end
