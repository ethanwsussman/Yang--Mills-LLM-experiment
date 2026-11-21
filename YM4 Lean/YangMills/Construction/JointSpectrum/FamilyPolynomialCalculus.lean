import YangMills.Construction.JointSpectrum.CommutingFamilies
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction
open JointSpectrum
namespace FamilyPolynomials
section Sums
variable {J : Type*} [Fintype J]
def spectralSum (s : Finset (ℕ × (J → ℤ))) (c : ℕ × (J → ℤ) → ℂ) (p : SpectralDomain J) :
    ℂ :=
  ∑ i ∈ s, c i * spectralMonomial i.1 i.2 p
end Sums
section Operators
variable {𝒦 : Type*} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
  {J : Type*} [Fintype J] [Nonempty J]
def familyMonomial (S : CommutingFamily 𝒦 J) (n : ℕ) (y : J → ℤ) : 𝒦 →L[ℂ] 𝒦 :=
  S.A ^ n * S.unitaryMonomial y
def familySum (S : CommutingFamily 𝒦 J) (s : Finset (ℕ × (J → ℤ)))
    (c : ℕ × (J → ℤ) → ℂ) : 𝒦 →L[ℂ] 𝒦 :=
  ∑ i ∈ s, c i • familyMonomial S i.1 i.2
def polynomialCalculus (S : CommutingFamily 𝒦 J) (q : SpectralDomain J → ℂ) : 𝒦 →L[ℂ] 𝒦 :=
  let r := Classical.epsilon fun r : Finset (ℕ × (J → ℤ)) × (ℕ × (J → ℤ) → ℂ) =>
    q = spectralSum r.1 r.2
  familySum S r.1 r.2
def generatorSet (S : CommutingFamily 𝒦 J) : Set (𝒦 →L[ℂ] 𝒦) :=
  {S.A} ∪ range (fun α => (S.B α : 𝒦 →L[ℂ] 𝒦)) ∪
    range (fun α => (((S.B α)⁻¹ : unitary (𝒦 →L[ℂ] 𝒦)) : 𝒦 →L[ℂ] 𝒦))
end Operators
def PolynomialCalculusStatement : Prop :=
  ∀ (𝒦 : Type) [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
    (J : Type) [Fintype J] [Nonempty J] (S : CommutingFamily 𝒦 J),
    (∀ C ∈ generatorSet S, ∀ D ∈ generatorSet S, Commute C D) ∧
    (∀ (s s' : Finset (ℕ × (J → ℤ))) (c c' : ℕ × (J → ℤ) → ℂ),
      spectralSum s c = spectralSum s' c' →
        (s : Set (ℕ × (J → ℤ))).indicator c = (s' : Set (ℕ × (J → ℤ))).indicator c') ∧
    (∀ (s : Finset (ℕ × (J → ℤ))) (c : ℕ × (J → ℤ) → ℂ),
      polynomialCalculus S (spectralSum s c) = familySum S s c) ∧
    (0 : SpectralDomain J → ℂ) ∈ spectralPolynomials J ∧
    (∀ q ∈ spectralPolynomials J, ∀ q' ∈ spectralPolynomials J, q + q' ∈ spectralPolynomials J) ∧
    (∀ (a : ℂ), ∀ q ∈ spectralPolynomials J, a • q ∈ spectralPolynomials J) ∧
    (∀ q ∈ spectralPolynomials J, ∀ q' ∈ spectralPolynomials J, q * q' ∈ spectralPolynomials J) ∧
    (∀ q ∈ spectralPolynomials J, (fun p => conj (q p)) ∈ spectralPolynomials J) ∧
    (∀ q ∈ spectralPolynomials J, ∀ q' ∈ spectralPolynomials J,
      polynomialCalculus S (q + q') = polynomialCalculus S q + polynomialCalculus S q') ∧
    (∀ (a : ℂ), ∀ q ∈ spectralPolynomials J,
      polynomialCalculus S (a • q) = a • polynomialCalculus S q) ∧
    (∀ q ∈ spectralPolynomials J, ∀ q' ∈ spectralPolynomials J,
      polynomialCalculus S (q * q') = polynomialCalculus S q * polynomialCalculus S q') ∧
    (∀ q ∈ spectralPolynomials J,
      polynomialCalculus S (fun p => conj (q p)) = star (polynomialCalculus S q)) ∧
    (∀ q ∈ spectralPolynomials J, (∀ p, 0 ≤ q p) → 0 ≤ polynomialCalculus S q) ∧
    (∀ q ∈ spectralPolynomials J, ‖polynomialCalculus S q‖ ≤ ⨆ p, ‖q p‖)
end FamilyPolynomials
end YangMills.Construction
