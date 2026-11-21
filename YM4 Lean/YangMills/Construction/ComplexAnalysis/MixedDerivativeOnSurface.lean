import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SurfaceMixedDerivative
def surfaceParam {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (a b c d : E)
    (r : Coordinates.ComplexCoordinates 2 → E) (s t : ℂ) : E :=
  s • a + t • b + (s * t) • c + t ^ 2 • d + r ![s, t]
def mixedDerivAtOrigin (f : ℂ → ℂ → ℂ) : ℂ :=
  deriv (fun s : ℂ => deriv (fun t : ℂ => f s t) 0) 0
def MixedDerivAlongSurface : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (O : Set E) (Φ : E → ℂ) (O' : Set (Coordinates.ComplexCoordinates 2))
    (r : Coordinates.ComplexCoordinates 2 → E) (a b c d : E) (C δ : ℝ),
    IsOpen O → (0 : E) ∈ O → DifferentiableOn ℂ Φ O →
    IsOpen O' → (0 : Coordinates.ComplexCoordinates 2) ∈ O' → DifferentiableOn ℂ r O' →
    0 < δ → (∀ z : Coordinates.ComplexCoordinates 2, ‖z‖ < δ → ‖r z‖ ≤ C * ‖z‖ ^ 3) →
      mixedDerivAtOrigin (fun s t => Φ (surfaceParam a b c d r s t)) =
        mixedDerivAtOrigin (fun s t => Φ (s • a + t • b)) +
          deriv (fun t : ℂ => Φ (t • c)) 0
end YangMills.Construction.SurfaceMixedDerivative
