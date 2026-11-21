import YangMills.Construction.ClusterExpansionOfAStep.FamiliesAtConstantCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TorusLumps
open BlockAverages TorusFields
def AbelianFieldOfAnglesHasCurvature : Prop :=
  ∀ (n : ℕ) [NeZero n] (X : imaginaryQuaternions) (ω : Fin 4 → Fin 4 → ℝ) (l : ℕ), ‖X‖ = 1 →
    (∀ i j, ω i j = - ω j i) →
    (∀ i j, ∃ z : ℤ, (l : ℝ) * ω i j = z) →
    IsAbelianWithCurvature X ω (2 * Real.pi * l / (n : ℝ) ^ 2)
      (abelianFieldOfAngles n X (2 * Real.pi * l / (n : ℝ) ^ 2) ω)
end TorusLumps
end YangMills.Construction
end
