import YangMills.Construction.Geometry.ExpandingTori
import YangMills.Construction.Geometry.Periodization
import YangMills.Construction.SourcesAndGluing.BallTransportAndInducedIsometries
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice.MarginPeriodization
section Radius
variable {L : ℕ} (c : ExpandingTori.PeriodizationMargin L)
theorem margin_radius_lt_quarter (ℓ : ℝ) : c.radius ℓ < ℓ / 4 := by
  have h := c.pos
  simp only [ExpandingTori.PeriodizationMargin.radius]
  linarith
end Radius
section Periodize
def HasCompactSupportInBall {E : Type*} [Zero E] (r : ℝ)
    (f : (Fin 4 → ℝ) → E) : Prop :=
  ∃ C : Set (Fin 4 → ℝ), IsCompact C ∧ C ⊆ SourcesAndGluing.ballR4 r ∧
    ∀ x, x ∉ C → f x = 0
structure IsPeriodizableAtRadius {L : ℕ} (c : ExpandingTori.PeriodizationMargin L) (ℓ r : ℝ)
    (f : (Fin 4 → ℝ) → ℝ) : Prop where
  pos : 0 < r
  le_margin : r ≤ c.radius ℓ
  support : HasCompactSupportInBall r f
theorem hasDiameterLE_ballR4 (r : ℝ) :
    TestFunctions.HasDiameterLE (SourcesAndGluing.ballR4 r) (2 * r) := by
  intro x hx y hy
  have hx' : TorusMetric.euclidNormVec x < r := hx
  have hy' : TorusMetric.euclidNormVec y < r := hy
  have hneg : TorusMetric.euclidNormVec (-y) = TorusMetric.euclidNormVec y := by
    simp [TorusMetric.euclidNormVec]
  have h := Periodization.euclidNormVec_triangle x (-y)
  rw [← sub_eq_add_neg, hneg] at h
  linarith
variable {L : ℕ} {c : ExpandingTori.PeriodizationMargin L} {ℓ r : ℝ} {f : (Fin 4 → ℝ) → ℝ}
end Periodize
end YangMills.Construction.InfiniteLattice.MarginPeriodization
end
