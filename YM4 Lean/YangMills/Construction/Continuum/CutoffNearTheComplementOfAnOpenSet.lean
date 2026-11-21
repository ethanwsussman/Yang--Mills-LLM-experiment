import YangMills.Construction.Continuum.OpenHalvesAndFlatnessOutsideAnOpenSet
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces
def approxByCompactSuppInOpen : Prop :=
  ∀ n k : ℕ, 0 < n → 0 < k → ∀ (V : Set (PointTuple n)) (φ₁ : PointTuple n → ℂ),
    HasCompactSupport φ₁ → VanishesToInfiniteOrderOff φ₁ V → ∀ ε : ℝ, 0 < ε →
      ∃ φ₂ ∈ (smoothCompactSupp V : Set (PointTuple n → ℂ)),
        weightedSeminorm k (φ₁ - φ₂) ≤ ENNReal.ofReal ε ∧
        ((∀ x, (φ₁ x).im = 0) → ∀ x, (φ₂ x).im = 0)
end YangMills.Construction.TestSpaces
