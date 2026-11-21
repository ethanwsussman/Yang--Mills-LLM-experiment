import YangMills.Construction.TwoPoints.SpectralMeasuresOfThePlaneKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
def AveragedKernelSpectralMeasureExists.Statement : Prop :=
  ∀ (c : FixedScale) (B : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (ψ : (Fin 2 → ℝ) → ℂ),
    IsDisjointForm B → IsAdmissibleForm c B → ψ ∈ transProfiles →
      ∀ n ∈ planeReflectionNormals, ∃ μ : MeasureTheory.Measure SpectralCalculus.SpectralPlane,
        IsAveragedKernelSpectralMeasure B ψ n μ
end YangMills.Construction.TwoPoints
end
