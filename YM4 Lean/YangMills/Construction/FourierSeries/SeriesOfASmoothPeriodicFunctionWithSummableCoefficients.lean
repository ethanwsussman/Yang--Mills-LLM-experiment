import YangMills.Construction.Continuum.FlatSchwartzAndTuples
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Matrix
noncomputable section
namespace YangMills.Construction.FourierSeries
variable {D : ℕ}
def IsPeriodicInEachCoord (p : ℝ) (f : (Fin D → ℝ) → ℂ) : Prop :=
  ∀ (i : Fin D) (y : Fin D → ℝ), f (Function.update y i (y i + p)) = f y
def dualLattice (D : ℕ) (m : ℝ) : Set (Fin D → ℝ) :=
  {ξ | ∃ k : Fin D → ℤ, ∀ i, ξ i = Real.pi / m * k i}
def cubeCoeff (m : ℝ) (a : Fin D → ℝ) (f : (Fin D → ℝ) → ℂ)
    (ξ : Fin D → ℝ) : ℂ :=
  (((2 * m) ^ D)⁻¹ : ℝ) *
    ∫ y in {y : Fin D → ℝ | YangMills.Construction.EuclideanCoords.supCoord (y - a) ≤ m},
      f y * Complex.exp (-(Complex.I * ((ξ ⬝ᵥ (y - a) : ℝ) : ℂ)))
def fourierSeries_eq_of_smooth_periodic_summable : Prop :=
  ∀ (D : ℕ), 1 ≤ D → ∀ (m : ℝ), 0 < m → ∀ (a : Fin D → ℝ) (f : (Fin D → ℝ) → ℂ),
    f ∈ YangMills.Construction.SmoothMaps.smoothSet (Fin D → ℝ) →
    IsPeriodicInEachCoord (2 * m) f →
    Summable (fun ξ : dualLattice D m => ‖cubeCoeff m a f ξ‖) →
    ∀ y : Fin D → ℝ,
      f y = ∑' ξ : dualLattice D m,
        cubeCoeff m a f ξ *
          Complex.exp (Complex.I * (((ξ : Fin D → ℝ) ⬝ᵥ (y - a) : ℝ) : ℂ))
end YangMills.Construction.FourierSeries
