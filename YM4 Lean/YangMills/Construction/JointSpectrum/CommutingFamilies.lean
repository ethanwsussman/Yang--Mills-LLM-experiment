import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.JointSpectrum
structure CommutingFamily (𝒦 : Type*) [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦]
    [CompleteSpace 𝒦] (J : Type*) [Fintype J] [Nonempty J] where
  A : 𝒦 →L[ℂ] 𝒦
  B : J → unitary (𝒦 →L[ℂ] 𝒦)
  isSelfAdjoint_A : IsSelfAdjoint A
  zero_le_A : 0 ≤ A
  A_le_one : A ≤ 1
  commute_A_B : ∀ α, Commute A (B α : 𝒦 →L[ℂ] 𝒦)
  commute_B_B : ∀ α α', Commute (B α : 𝒦 →L[ℂ] 𝒦) (B α' : 𝒦 →L[ℂ] 𝒦)
section Powers
variable {𝒦 : Type*} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
  {J : Type*} [Fintype J] [Nonempty J]
theorem CommutingFamily.commute_zpow_unitary (S : CommutingFamily 𝒦 J) (y : J → ℤ) (α α' : J) :
    Commute (S.B α ^ y α) (S.B α' ^ y α') :=
  Commute.zpow_zpow (Subtype.ext (S.commute_B_B α α').eq) _ _
def CommutingFamily.unitaryMonomial (S : CommutingFamily 𝒦 J) (y : J → ℤ) : 𝒦 →L[ℂ] 𝒦 :=
  ((Finset.univ.noncommProd (fun α => S.B α ^ y α)
    (fun α _ α' _ _ => S.commute_zpow_unitary y α α') : unitary (𝒦 →L[ℂ] 𝒦)) : 𝒦 →L[ℂ] 𝒦)
end Powers
instance : MeasurableSpace Circle := borel Circle
instance : BorelSpace Circle := ⟨rfl⟩
abbrev SpectralDomain (J : Type*) : Type _ := unitInterval × (J → Circle)
section Polynomials
variable {J : Type*} [Fintype J]
def torusMonomial (ζ : J → Circle) (y : J → ℤ) : ℂ := ∏ α, (ζ α : ℂ) ^ y α
def spectralMonomial (n : ℕ) (y : J → ℤ) (p : SpectralDomain J) : ℂ :=
  (((p.1 : ℝ) : ℂ)) ^ n * torusMonomial p.2 y
variable (J) in
def spectralPolynomials : Set (SpectralDomain J → ℂ) :=
  {q | ∃ (s : Finset (ℕ × (J → ℤ))) (c : ℕ × (J → ℤ) → ℂ),
    ∀ p, q p = ∑ i ∈ s, c i * spectralMonomial i.1 i.2 p}
end Polynomials
structure ProjectionValuedMeasure (J : Type*) [Fintype J] [Nonempty J] (𝒦 : Type*)
    [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦] where
  E : {S : Set (SpectralDomain J) // MeasurableSet S} → 𝒦 →L[ℂ] 𝒦
  isStarProjection : ∀ S, IsStarProjection (E S)
  E_univ : E ⟨univ, MeasurableSet.univ⟩ = 1
  exists_scalarMeasure : ∀ ψ : 𝒦, ∃ μ : Measure (SpectralDomain J), IsFiniteMeasure μ ∧
    ∀ S, inner ℂ ψ (E S ψ) = ((μ.real S.1 : ℝ) : ℂ)
end YangMills.Construction.JointSpectrum
