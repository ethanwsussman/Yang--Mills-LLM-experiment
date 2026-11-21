import YangMills.Construction.InfiniteLattice.ErgodicPhases
import YangMills.Construction.InfiniteLattice.IntegrableVersionsAndVariance
import YangMills.Construction.InfiniteLattice.OneLatticeItsConfigurationsAndMeasuresOnCompactSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace LatticePhases
namespace CondExpInvariant
variable {a : ℝ}
def IsRealValued (F : GaugeField a → ℂ) : Prop := ∀ U, (F U).im = 0
def VersionsExistUniqueBounded (ρ : Measure (GaugeField a)) (A : GaugeField a → ℂ) : Prop :=
  (∃ Y, IsIntegrableCondExpRepresentative ρ A Y) ∧
  IsIntegrableCondExpRepresentative ρ A (condExpShiftInvariant ρ A) ∧
  (∀ Y Z, IsIntegrableCondExpRepresentative ρ A Y → IsIntegrableCondExpRepresentative ρ A Z → Y =ᵐ[ρ] Z) ∧
  (∀ Y, IsIntegrableCondExpRepresentative ρ A Y → ∀ᵐ U ∂ρ, ‖Y U‖ ≤ observableSupNorm A) ∧
  (∃ Y, IsIntegrableCondExpRepresentative ρ A Y ∧ ∀ U, ‖Y U‖ ≤ observableSupNorm A) ∧
  (IsRealValued A → ∃ Y, IsIntegrableCondExpRepresentative ρ A Y ∧
    (∀ U, ‖Y U‖ ≤ observableSupNorm A) ∧ IsRealValued Y)
def VersionsLinearAndConj (ρ : Measure (GaugeField a)) (A B : GaugeField a → ℂ) : Prop :=
  ∀ Y Z, IsIntegrableCondExpRepresentative ρ A Y → IsIntegrableCondExpRepresentative ρ B Z →
    (∀ w : ℂ, IsIntegrableCondExpRepresentative ρ (fun U => A U + w * B U) (fun U => Y U + w * Z U)) ∧
    IsIntegrableCondExpRepresentative ρ (fun U => conj (A U)) (fun U => conj (Y U))
def VersionsPreserveMeanContractModulus (ρ : Measure (GaugeField a))
    (A : GaugeField a → ℂ) : Prop :=
  ∀ Y, IsIntegrableCondExpRepresentative ρ A Y →
    ∫ U, Y U ∂ρ = ∫ U, A U ∂ρ ∧ ∫ U, ‖Y U‖ ∂ρ ≤ ∫ U, ‖A U‖ ∂ρ
def BoundedInvariantIsOwnConditionalExpectation (ρ : Measure (GaugeField a)) : Prop :=
  ∀ J : GaugeField a → ℂ, Measurable[shiftInvariantSigma a] J → (∃ C : ℝ, ∀ U, ‖J U‖ ≤ C) →
    IsIntegrableCondExpRepresentative ρ J J
def PlateauIndependentOfRepresentative (ρ : Measure (GaugeField a)) (A B : GaugeField a → ℂ) : Prop :=
  Integrable A ρ ∧
  (∀ Y Z, IsIntegrableCondExpRepresentative ρ A Y → IsIntegrableCondExpRepresentative ρ B Z →
    Integrable (fun U => conj (Y U) * Z U) ρ ∧
      ∫ U, conj (Y U) * Z U ∂ρ = plateauPairing ρ A B) ∧
  ‖plateauPairing ρ A B‖ ≤ observableSupNorm A * observableSupNorm B ∧
  ∀ Z, IsIntegrableCondExpRepresentative ρ B Z →
    Integrable (fun U => conj (A U) * Z U) ρ ∧
      plateauPairing ρ A B = ∫ U, conj (A U) * Z U ∂ρ
def Claim : Prop :=
  ∀ (D : Setup) (ρ : Measure (GaugeField D.mesh)) [IsProbabilityMeasure ρ],
    IsShiftInvariant ρ → ∀ A B : GaugeField D.mesh → ℂ, IsBoundedObservable A →
      IsBoundedObservable B →
      VersionsExistUniqueBounded ρ A ∧
      VersionsLinearAndConj ρ A B ∧
      VersionsPreserveMeanContractModulus ρ A ∧
      BoundedInvariantIsOwnConditionalExpectation ρ ∧
      PlateauIndependentOfRepresentative ρ A B
end CondExpInvariant
end LatticePhases
end YangMills.Construction
end
