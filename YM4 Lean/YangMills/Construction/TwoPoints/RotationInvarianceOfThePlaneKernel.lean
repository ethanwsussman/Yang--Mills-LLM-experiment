import YangMills.Construction.TwoPoints.PlaneKernelOfAForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
def IsRotationInvariantAveragedKernel (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (φ : (Fin 2 → ℝ) → ℂ) : Prop :=
  ∀ y : Fin 2 → ℝ, y ≠ 0 → ∀ θ : ℝ,
    transverseAveragedKernel S φ (planeCoords (rotateInPlane θ (embedPlane y))) =
      transverseAveragedKernel S φ y
end YangMills.Construction.TwoPoints
end
