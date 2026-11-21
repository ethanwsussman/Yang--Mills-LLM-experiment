import YangMills.Construction.PeriodicOperators.ExpansionsOfTheComponentsOfAJet
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfABoundedOperatorFunction
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.BoundedExpansionJets
open CauchyTaylorBounds (IsFieldNorm BoundedOnBall)
structure RowLocalized (F I I' : PeriodicData) (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ)
    (A : I'.Carrier → Set F.Carrier) (B : I'.Carrier → Set I.Carrier) (s r : ℝ) (m : ℕ) : Prop where
  eq_of_eqOn : ∀ (j : I'.Carrier) (i : I.Carrier) (φ ψ : F.Carrier → ℂ), IsSupBelow F φ s →
    IsSupBelow F ψ s → EqOn φ ψ (A j) → T φ j i = T ψ j i
  eq_zero_of_not_mem : ∀ (j : I'.Carrier) (i : I.Carrier), i ∉ B j → ∀ φ : F.Carrier → ℂ,
    IsSupBelow F φ s → T φ j i = 0
  finite_support : ∀ j, (B j).Finite
  pos_near : ∀ j, ∀ i ∈ B j, ∀ μ, |I.pos i μ - I'.pos j μ| ≤ r
  encard_le : ∀ i, {j | i ∈ B j}.encard ≤ m
def ComponentBounds : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I' T →
    ∀ (N : (F.Carrier → ℂ) → ℝ≥0∞) (ρ C : ℝ), 0 < ρ → 0 ≤ C → IsFieldNorm F N →
      BoundedOnBall F I I' T N ρ C →
    ∀ (A : I'.Carrier → Set F.Carrier) (B : I'.Carrier → Set I.Carrier) (s r : ℝ) (m : ℕ), 0 < s →
      0 ≤ r → RowLocalized F I I' T A B s r m →
    ∀ (p : Fin 4 → ℂ) (u v : F.UnitQuot → ℂ) (M : ℝ), 0 ≤ M →
      (∀ j, N ((A j).indicator (phaseField F p u (I'.pos j))) ≤ ENNReal.ofReal M) →
      (∀ j, N ((A j).indicator (phaseField F (-p) v (I'.pos j))) ≤ ENNReal.ofReal M) →
      ∀ κ : Fin 4 → ℂ,
        quotHomNorm ((jetAlong F I I' T p u v).f10 κ) ≤
            ENNReal.ofReal (Real.sqrt m * (C * ρ⁻¹ * M) * Real.exp (r * ∑ μ, |(κ μ).im|)) ∧
          quotHomNorm ((jetAlong F I I' T p u v).f01 κ) ≤
            ENNReal.ofReal (Real.sqrt m * (C * ρ⁻¹ * M) * Real.exp (r * ∑ μ, |(κ μ).im|)) ∧
          quotHomNorm ((jetAlong F I I' T p u v).f11 κ) ≤
            ENNReal.ofReal
              (Real.sqrt m * (4 * C * ρ⁻¹ ^ 2 * M * M) * Real.exp (r * ∑ μ, |(κ μ).im|))
end YangMills.Construction.PeriodicOperators.BoundedExpansionJets
end
