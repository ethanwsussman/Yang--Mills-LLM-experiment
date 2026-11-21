import YangMills.Construction.Continuum.OpenHalvesAndFlatnessOutsideAnOpenSet
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.TestSpaces
def SchwartzTruncationApprox : Prop :=
  ∀ n k : ℕ, 0 < n → 0 < k → ∀ V : Set (PointTuple n), ∀ φ ∈ schwartzSet n,
    VanishesToInfiniteOrderOff φ V → ∀ ε : ℝ, 0 < ε →
      ∃ ψ : PointTuple n → ℂ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        VanishesToInfiniteOrderOff ψ V ∧
        weightedSeminorm k (φ - ψ) ≤ ENNReal.ofReal ε ∧
        ((∀ x, (φ x).im = 0) → ∀ x, (ψ x).im = 0)
end YangMills.Construction.TestSpaces
end
