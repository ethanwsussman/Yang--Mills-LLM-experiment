import YangMills.Construction.PeriodicOperators.LocalOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
open Coordinates.QuadraticTaylor (IsSecondOrderExpansion)
def CoeffsOnSuperset.Claim : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (ρ R : ℝ),
      IsLocalWith F I I' T ρ R →
      ∀ (a : I'.Carrier) (b : I.Carrier) (A : Set F.Carrier) (n : ℕ) (e : Fin n ≃ A),
        nearIndices F (I'.pos a) R ⊆ A →
        ∃ (φ : Coordinates.ComplexCoordinates n →ₗ[ℂ] ℂ)
          (β : Coordinates.ComplexCoordinates n →ₗ[ℂ] Coordinates.ComplexCoordinates n →ₗ[ℂ] ℂ),
          IsSecondOrderExpansion (entryFun T a b e) φ β ∧
            (∀ ζ : F.Carrier → ℂ, φ (fieldValues e ζ) = coeffOne F I I' T ζ a b) ∧
            ∀ ζ ζ' : F.Carrier → ℂ,
              β (fieldValues e ζ) (fieldValues e ζ') = coeffTwo F I I' T ζ ζ' a b
end YangMills.Construction.PeriodicOperators
end
