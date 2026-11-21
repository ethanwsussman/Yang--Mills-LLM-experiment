import YangMills.Construction.TwoPoints.OneFieldSpaceAtAMirror
import YangMills.Construction.TwoPoints.SpectralMeasuresOfThePlaneKernel
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
def PlateNormViaSpectralMeasure.Statement : Prop :=
  ∀ (c : FixedScale) (B : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (ψ : (Fin 2 → ℝ) → ℂ),
    IsDisjointForm B → IsAdmissibleForm c B → ψ ∈ transProfiles →
      ∀ n ∈ planeReflectionNormals, ∀ μ : Measure SpectralCalculus.SpectralPlane,
        IsAveragedKernelSpectralMeasure B ψ n μ →
        ∀ f ∈ cc1In {y : Fin 2 → ℝ | 0 < euclidDot (planeCoords n) y},
          ∀ hf : tensorPlate f ψ ∈ halfSpaceDomain n,
            ENNReal.ofReal (‖reflectedClass B n ⟨tensorPlate f ψ, hf⟩‖ ^ 2) =
              ∫⁻ z : SpectralCalculus.SpectralPlane,
                ‖TwoPoints.lebesgueIntegral fun t : ℝ => TwoPoints.lebesgueIntegral fun s : ℝ =>
                    f (planeCoords (t • n + s • planePerp n)) *
                      Complex.exp (((-t * (z.1 : ℝ) : ℝ) : ℂ) +
                        Complex.I * ((s * z.2 : ℝ) : ℂ))‖ₑ ^ 2 ∂μ
end YangMills.Construction.TwoPoints
end
