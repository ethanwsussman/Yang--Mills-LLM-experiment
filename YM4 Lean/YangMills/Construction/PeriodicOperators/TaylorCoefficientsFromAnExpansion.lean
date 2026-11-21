import YangMills.Construction.PeriodicOperators.LocalOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.ExpansionCoefficients
def Claim : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I' T →
    ∀ (a : I'.Carrier) (b : I.Carrier) (S : Set F.Carrier), S.Finite →
    ∀ (l : (F.Carrier → ℂ) →ₗ[ℂ] ℂ) (B : (F.Carrier → ℂ) →ₗ[ℂ] (F.Carrier → ℂ) →ₗ[ℂ] ℂ) (r C : ℝ), 0 < r →
      (∀ ζ ζ', B ζ ζ' = B ζ' ζ) →
      (∀ ζ ζ', (∀ κ ∈ S, ζ κ = ζ' κ) → l ζ = l ζ' ∧ ∀ ξ, B ζ ξ = B ζ' ξ) →
      (∀ (ζ : F.Carrier → ℂ) (δ : ℝ), δ ≤ r → (∀ κ ∈ S, ‖ζ κ‖ ≤ δ) →
        ‖T ζ a b - T 0 a b - l ζ - (1 / 2 : ℂ) * B ζ ζ‖ ≤ C * δ ^ 3) →
      ∀ ζ ζ' : F.Carrier → ℂ,
        coeffOne F I I' T ζ a b = l ζ ∧ coeffTwo F I I' T ζ ζ' a b = B ζ ζ'
end YangMills.Construction.PeriodicOperators.ExpansionCoefficients
end
