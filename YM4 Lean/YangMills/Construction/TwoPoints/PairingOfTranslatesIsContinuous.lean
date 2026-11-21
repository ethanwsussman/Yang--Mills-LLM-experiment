import YangMills.Construction.TwoPoints.ThreePropertiesOfAForm
import YangMills.Construction.TwoPoints.TranslationModulusAndSuperpositionsOfTranslates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
def ShiftPairingContinuity.Statement : Prop :=
  ∀ scale : FixedScale, ∀ S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ, IsDisjointForm S →
    IsAdmissibleForm scale S →
    ∀ ε : ℝ, 0 < ε → ∀ φ₁ ∈ cc1NearZero ε, ∀ φ₂ ∈ cc1NearZero ε,
      (∀ z ∈ farShifts ε,
        translateFun z φ₂ ∈ compactC1Complex ∧ DisjointSupports φ₁ (translateFun z φ₂)) ∧
      ContinuousOn (shiftPairing S φ₁ φ₂) {z | 2 * ε < euclidNorm z}
end YangMills.Construction.TwoPoints
end
