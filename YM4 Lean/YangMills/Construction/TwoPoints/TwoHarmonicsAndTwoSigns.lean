import YangMills.Construction.TwoPoints.FunctionOfTheAngle
import YangMills.Construction.TwoPoints.RotationInvarianceOfThePlaneKernel
import YangMills.Construction.TwoPoints.SpectralMeasuresOfThePlaneKernel
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def TwoHarmonicsVanishing.Statement : Prop :=
  ∀ (κ : FixedScale) (B : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (φ : (Fin 2 → ℝ) → ℂ),
    IsDisjointForm B → IsAdmissibleForm κ B → φ ∈ transProfiles →
      Tendsto (fun t : ℝ => t ^ 8 * axisDecayTransform B φ t) (𝓝[>] 0) (𝓝 0) →
        (∀ r : ℝ, 0 < r → ∃ a₀ a₄ : ℝ,
          (∀ θ : ℂ, angleFunction B φ r θ = (a₀ : ℂ) + (a₄ : ℂ) * Complex.cos (4 * θ)) ∧
          a₄ = 0 ∧
          ∀ θ : ℝ, transverseAveragedKernel B φ (planeCoords (r • planeUnit θ)) = (a₀ : ℂ)) ∧
        IsRotationInvariantAveragedKernel B φ
end YangMills.Construction.TwoPoints
end
