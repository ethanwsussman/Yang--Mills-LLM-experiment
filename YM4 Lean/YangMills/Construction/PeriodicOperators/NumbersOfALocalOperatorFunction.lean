import YangMills.Construction.PeriodicOperators.LocalOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
open Coordinates.QuadraticTaylor (IsSecondOrderExpansion)
section WithParameters
variable (F I I' : PeriodicData)
def IsCoeffOneWith (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (ρ R : ℝ)
    (ζ : F.Carrier → ℂ) (a : I'.Carrier) (b : I.Carrier) (t : ℂ) : Prop :=
  IsLocalWith F I I' T ρ R ∧
    ∃ (n : ℕ) (e : Fin n ≃ nearIndices F (I'.pos a) R)
      (φ : Coordinates.ComplexCoordinates n →ₗ[ℂ] ℂ)
      (β : Coordinates.ComplexCoordinates n →ₗ[ℂ] Coordinates.ComplexCoordinates n →ₗ[ℂ] ℂ),
      IsSecondOrderExpansion (entryFun T a b e) φ β ∧ φ (fieldValues e ζ) = t
def IsCoeffTwoWith (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (ρ R : ℝ)
    (ζ ζ' : F.Carrier → ℂ) (a : I'.Carrier) (b : I.Carrier) (t : ℂ) : Prop :=
  IsLocalWith F I I' T ρ R ∧
    ∃ (n : ℕ) (e : Fin n ≃ nearIndices F (I'.pos a) R)
      (φ : Coordinates.ComplexCoordinates n →ₗ[ℂ] ℂ)
      (β : Coordinates.ComplexCoordinates n →ₗ[ℂ] Coordinates.ComplexCoordinates n →ₗ[ℂ] ℂ),
      IsSecondOrderExpansion (entryFun T a b e) φ β ∧
        β (fieldValues e ζ) (fieldValues e ζ') = t
def IsPeriodicValueWith (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (ρ R : ℝ) (s : ℕ)
    (ζ : F.QuotMod s → ℂ) (a : I'.Carrier) (b : I.Carrier) (t : ℂ) : Prop :=
  IsLocalWith F I I' T ρ R ∧ 4 * R < s ∧ IsSupBelow F (liftQuotField F s ζ) ρ ∧
    t = periodicValue F I I' T s ζ a b
end WithParameters
def ParameterIndependence.Claim : Prop :=
  ∀ (F I I' : PeriodicData), IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (ρ R ρ' R' : ℝ),
      IsLocalWith F I I' T ρ R → IsLocalWith F I I' T ρ' R' →
      ((∀ ρ'' R'' : ℝ, 0 < ρ'' → ρ'' ≤ ρ → R ≤ R'' → IsLocalWith F I I' T ρ'' R'') ∧
        IsLocalWith F I I' T (min ρ ρ') (max R R')) ∧
      ((∀ (ζ ζ' : F.Carrier → ℂ) (a : I'.Carrier) (b : I.Carrier),
          ((∀ t, IsCoeffOneWith F I I' T ρ R ζ a b t ↔
                t = coeffOne F I I' T ζ a b) ∧
            (∀ t, IsCoeffOneWith F I I' T ρ' R' ζ a b t ↔
                t = coeffOne F I I' T ζ a b) ∧
            IsLinearCoeff F I I' T ζ a b (coeffOne F I I' T ζ a b)) ∧
          ((∀ t, IsCoeffTwoWith F I I' T ρ R ζ ζ' a b t ↔
                t = coeffTwo F I I' T ζ ζ' a b) ∧
            (∀ t, IsCoeffTwoWith F I I' T ρ' R' ζ ζ' a b t ↔
                t = coeffTwo F I I' T ζ ζ' a b) ∧
            IsBilinearCoeff F I I' T ζ ζ' a b (coeffTwo F I I' T ζ ζ' a b))) ∧
        coeffZero F I I' T = T 0) ∧
      (∀ (s : ℕ), 0 < s → ∀ ζ : F.QuotMod s → ℂ,
        4 * R < s → IsSupBelow F (liftQuotField F s ζ) ρ →
        4 * R' < s → IsSupBelow F (liftQuotField F s ζ) ρ' →
        ∀ (a : I'.Carrier) (b : I.Carrier) (t : ℂ),
          IsPeriodicValueWith F I I' T ρ R s ζ a b t ↔
            IsPeriodicValueWith F I I' T ρ' R' s ζ a b t)
end YangMills.Construction.PeriodicOperators
end
