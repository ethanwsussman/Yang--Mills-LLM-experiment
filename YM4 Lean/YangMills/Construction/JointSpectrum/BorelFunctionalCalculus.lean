import YangMills.Construction.JointSpectrum.SpectralIntegral
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ENNReal
noncomputable section
namespace YangMills.Construction
open JointSpectrum JointSpectrum.SpectralIntegral
namespace JointSpectrum.BorelCalculus
def IsBoundedFn {J : Type*} (f : SpectralDomain J → ℂ) : Prop :=
  ∃ M : ℝ, ∀ p, ‖f p‖ ≤ M
def HasSystemMoments {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {J : Type*} [Fintype J] [Nonempty J] (S : CommutingFamily H J)
    (P : ProjectionValuedMeasure J H) : Prop :=
  ∀ ψ : H, ∃ μ : Measure (SpectralDomain J), IsFiniteMeasure μ ∧
    (∀ T, inner ℂ ψ (P.E T ψ) = ((μ.real T.1 : ℝ) : ℂ)) ∧
    ∀ (n : ℕ) (y : J → ℤ),
      inner ℂ ψ (FamilyPolynomials.familyMonomial S n y ψ) = ∫ p, spectralMonomial n y p ∂μ
def BorelCalculusStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : Type) [Fintype J] [Nonempty J] (S : CommutingFamily H J),
    (∀ f : SpectralDomain J → ℂ, Measurable f →
      (∃ D : Submodule ℂ H, (D : Set H) = integralDomain S f) ∧
      (∀ ψ ∈ integralDomain S f, ∀ ψ' ∈ integralDomain S f,
        spectralIntegral S f (ψ + ψ') = spectralIntegral S f ψ + spectralIntegral S f ψ') ∧
      (∀ c : ℂ, ∀ ψ ∈ integralDomain S f,
        spectralIntegral S f (c • ψ) = c • spectralIntegral S f ψ) ∧
      (∀ ψ ∈ integralDomain S f,
        ‖spectralIntegral S f ψ‖ₑ ^ 2 =
            ScalarSpectralMeasures.sqNormLIntegral (ScalarSpectralMeasures.spectralMeasure S ψ) f ∧
        inner ℂ ψ (spectralIntegral S f ψ) =
          ∫ p, f p ∂(ScalarSpectralMeasures.spectralMeasure S ψ)) ∧
      (IsBoundedFn f →
        integralDomain S f = univ ∧
        ∃ C : H →L[ℂ] H, ⇑C = spectralIntegral S f ∧ ‖C‖ ≤ ⨆ p, ‖f p‖ ∧
          ∀ C' : H →L[ℂ] H,
            (∀ ψ, inner ℂ ψ (C' ψ) = ∫ p, f p ∂(ScalarSpectralMeasures.spectralMeasure S ψ)) →
              C' = C)) ∧
    (∀ q ∈ spectralPolynomials J, integralDomain S q = univ ∧
      spectralIntegral S q = ⇑(FamilyPolynomials.polynomialCalculus S q)) ∧
    (∀ (n : ℕ) (y : J → ℤ),
      integralDomain S (spectralMonomial n y) = univ ∧
      spectralIntegral S (spectralMonomial n y) = ⇑(FamilyPolynomials.familyMonomial S n y)) ∧
    (∀ f g : SpectralDomain J → ℂ, Measurable f → Measurable g →
      ∀ (c : ℂ), ∀ ψ ∈ integralDomain S f, ψ ∈ integralDomain S g →
        ψ ∈ integralDomain S (f + c • g) ∧
        spectralIntegral S (f + c • g) ψ = spectralIntegral S f ψ + c • spectralIntegral S g ψ) ∧
    (∀ f : SpectralDomain J → ℂ, Measurable f →
      ∀ c : ℂ, c ≠ 0 → integralDomain S (c • f) = integralDomain S f) ∧
    (∀ f : SpectralDomain J → ℂ, Measurable f →
      integralDomain S (fun p => conj (f p)) = integralDomain S f ∧
      (∀ ψ ∈ integralDomain S f, ∀ ψ' ∈ integralDomain S f,
        inner ℂ ψ' (spectralIntegral S f ψ) =
          inner ℂ (spectralIntegral S (fun p => conj (f p)) ψ') ψ) ∧
      (IsBoundedFn f →
        ∃ C : H →L[ℂ] H, ⇑C = spectralIntegral S f ∧
          ⇑(star C) = spectralIntegral S (fun p => conj (f p)))) ∧
    (∀ g : SpectralDomain J → ℂ, Measurable g → ∀ ψ ∈ integralDomain S g,
      ScalarSpectralMeasures.spectralMeasure S (spectralIntegral S g ψ) =
          (ScalarSpectralMeasures.spectralMeasure S ψ).withDensity (fun p => ‖g p‖ₑ ^ 2) ∧
      ∀ f : SpectralDomain J → ℂ, Measurable f → ψ ∈ integralDomain S (f * g) →
        spectralIntegral S g ψ ∈ integralDomain S f ∧
        spectralIntegral S f (spectralIntegral S g ψ) = spectralIntegral S (f * g) ψ) ∧
    (∀ f g : SpectralDomain J → ℂ, Measurable f → Measurable g →
      IsBoundedFn f → IsBoundedFn g →
        spectralIntegral S (f * g) = spectralIntegral S f ∘ spectralIntegral S g ∧
        spectralIntegral S f ∘ spectralIntegral S g = spectralIntegral S g ∘ spectralIntegral S f) ∧
    (∃ P : ProjectionValuedMeasure J H,
      (∀ T, ⇑(P.E T) = jointSpectralMeasure S T.1) ∧
      HasSystemMoments S P ∧
      ∀ P' : ProjectionValuedMeasure J H, HasSystemMoments S P' → P' = P) ∧
    (∀ (T : Set (SpectralDomain J)) (ψ : H), MeasurableSet T →
      inner ℂ ψ (jointSpectralMeasure S T ψ) =
          (((ScalarSpectralMeasures.spectralMeasure S ψ).real T : ℝ) : ℂ) ∧
      ‖jointSpectralMeasure S T ψ‖ₑ ^ 2 = ScalarSpectralMeasures.spectralMeasure S ψ T) ∧
    (∀ T T' : Set (SpectralDomain J), MeasurableSet T → MeasurableSet T' →
      jointSpectralMeasure S T ∘ jointSpectralMeasure S T' = jointSpectralMeasure S (T ∩ T')) ∧
    (∀ 𝒯 : Set (Set (SpectralDomain J)), 𝒯.Countable →
      (∀ T ∈ 𝒯, MeasurableSet T ∧ jointSpectralMeasure S T = 0) →
        MeasurableSet (⋃₀ 𝒯) ∧ jointSpectralMeasure S (⋃₀ 𝒯) = 0) ∧
    (∀ f g : SpectralDomain J → ℂ, Measurable f → Measurable g →
      jointSpectralMeasure S {p | f p ≠ g p} = 0 →
        integralDomain S f = integralDomain S g ∧ spectralIntegral S f = spectralIntegral S g)
end JointSpectrum.BorelCalculus
end YangMills.Construction
