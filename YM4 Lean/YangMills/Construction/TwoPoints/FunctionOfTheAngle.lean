import YangMills.Construction.TwoPoints.PlaneKernelOfAForm
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
structure IsAngleFunction (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (φ : (Fin 2 → ℝ) → ℂ) (r : ℝ) (F : ℂ → ℂ) : Prop where
  holomorphic : Coordinates.ComplexCoordinates.IsHolomorphicVia (Equiv.funUnique (Fin 1) ℂ).symm
    (Equiv.funUnique (Fin 1) ℂ).symm univ F
  ofReal_eq : ∀ θ : ℝ, F (θ : ℂ) = transverseAveragedKernel S φ (planeCoords (r • planeUnit θ))
def angleFunction (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (φ : (Fin 2 → ℝ) → ℂ)
    (r : ℝ) : ℂ → ℂ :=
  Classical.epsilon (IsAngleFunction S φ r)
end YangMills.Construction.TwoPoints
end
