import YangMills.Construction.TwoPoints.FunctionOfTheAngle
import YangMills.Construction.TwoPoints.SpectralMeasuresOfThePlaneKernel
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def HarmonicCountFromGrowth.Statement : Prop :=
  ∀ (L : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (φ : (Fin 2 → ℝ) → ℂ),
    IsDisjointForm S → IsAdmissibleForm L S → φ ∈ transProfiles →
      ∀ n : ℕ,
        Tendsto (fun t : ℝ => t ^ (4 * (n + 1)) * axisDecayTransform S φ t) (𝓝[>] 0) (𝓝 0) →
          ∀ r : ℝ, 0 < r → ∃ c : Fin (n + 1) → ℝ, ∀ z : ℂ,
            angleFunction S φ r z =
              ∑ k : Fin (n + 1), (c k : ℂ) * Complex.cos (((4 * (k : ℕ) : ℕ) : ℂ) * z)
end YangMills.Construction.TwoPoints
end
