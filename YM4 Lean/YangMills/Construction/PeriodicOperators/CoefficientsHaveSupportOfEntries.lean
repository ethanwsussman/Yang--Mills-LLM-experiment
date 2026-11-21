import YangMills.Construction.PeriodicOperators.LocalOperatorFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.CoeffLocality
def Claim : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I' T →
    ∀ (j' : I'.Carrier) (j : I.Carrier),
      (∀ (r : ℝ) (A : Set F.Carrier), 0 < r →
        (∀ φ φ' : F.Carrier → ℂ, IsSupBelow F φ r → IsSupBelow F φ' r → EqOn φ φ' A →
          T φ j' j = T φ' j' j) →
        (∀ φ φ' : F.Carrier → ℂ, EqOn φ φ' A →
          coeffOne F I I' T φ j' j = coeffOne F I I' T φ' j' j) ∧
        ∀ φ₁ φ₂ φ₁' φ₂' : F.Carrier → ℂ, EqOn φ₁ φ₁' A → EqOn φ₂ φ₂' A →
          coeffTwo F I I' T φ₁ φ₂ j' j = coeffTwo F I I' T φ₁' φ₂' j' j) ∧
      (∀ r : ℝ, 0 < r → (∀ φ : F.Carrier → ℂ, IsSupBelow F φ r → T φ j' j = 0) →
        ∀ φ φ' : F.Carrier → ℂ, coeffOne F I I' T φ j' j = 0 ∧
          coeffTwo F I I' T φ φ' j' j = 0) ∧
      (∀ (c : ℂ) (φ : F.Carrier → ℂ),
        coeffOne F I I' T (c • φ) j' j = c * coeffOne F I I' T φ j' j) ∧
      ∀ (c c' : ℂ) (φ φ' : F.Carrier → ℂ),
        coeffTwo F I I' T (c • φ) (c' • φ') j' j =
          c * c' * coeffTwo F I I' T φ φ' j' j
end YangMills.Construction.PeriodicOperators.CoeffLocality
end
