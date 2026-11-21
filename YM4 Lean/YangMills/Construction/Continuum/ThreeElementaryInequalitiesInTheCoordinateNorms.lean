import YangMills.Construction.Continuum.FlatSchwartzAndTuples
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.CoordNormBounds
open EuclideanCoords
def inequalitiesClaim : Prop :=
  (∀ (d : ℕ), 1 ≤ d → ∀ w : Fin d → ℝ,
    supCoord w ≤ sqrtSumSq w ∧ sqrtSumSq w ≤ Real.sqrt (d : ℝ) * supCoord w) ∧
  (∀ (s : ℕ) (t : ℝ), 0 ≤ t → t ^ s ≤ (s.factorial : ℝ) * Real.exp t) ∧
  (∀ (s : ℕ), 1 ≤ s → ∀ k : Fin s → ℕ,
    ∏ a, (k a).factorial ≤ (∑ a, k a).factorial)
end YangMills.Construction.CoordNormBounds
