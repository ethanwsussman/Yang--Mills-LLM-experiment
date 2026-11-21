import YangMills.Construction.TwoPoints.KernelOfAForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def transverseAveragedKernel (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (φ : (Fin 2 → ℝ) → ℂ) (y : Fin 2 → ℝ) : ℂ :=
  lebesgueIntegral fun ζ : Fin 2 → ℝ => ((ofCoords (formKernel S) y ζ : ℝ) : ℂ) * profileCorr φ φ ζ
end YangMills.Construction.TwoPoints
end
