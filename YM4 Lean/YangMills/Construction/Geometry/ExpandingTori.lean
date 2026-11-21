import YangMills.Construction.Geometry.TorusMetric
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ExpandingTori
open TorusMetric
def openEuclidBall (ρ : ℝ) : Set (Fin 4 → ℝ) := {x | euclidNormVec x < ρ}
structure PeriodizationMargin (L : ℕ) where
  value : ℝ
  pos : 0 < value
  lt_half : value < (L : ℝ) / 2
def PeriodizationMargin.radius {L : ℕ} (c : PeriodizationMargin L) (ℓ : ℝ) : ℝ := ℓ / 4 - c.value
end YangMills.Construction.ExpandingTori
end
