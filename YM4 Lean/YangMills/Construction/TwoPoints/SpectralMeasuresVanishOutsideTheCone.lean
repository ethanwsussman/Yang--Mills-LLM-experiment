import YangMills.Construction.TwoPoints.ThirdPropertyAndFamiliesOfSpectralMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.SpectralCalculus (SpectralPlane)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def SpectralSupportInCone.Statement : Prop :=
  ∀ (L : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (φ : (Fin 2 → ℝ) → ℂ)
    (ρ : planeReflectionNormals → Measure SpectralPlane),
    IsDisjointForm S → IsAdmissibleForm L S → φ ∈ transProfiles →
      IsSpectralFamily S φ ρ →
      ∀ m : planeReflectionNormals, ρ m {p : SpectralPlane | (p.1 : ℝ) < |p.2|} = 0
end YangMills.Construction.TwoPoints
end
