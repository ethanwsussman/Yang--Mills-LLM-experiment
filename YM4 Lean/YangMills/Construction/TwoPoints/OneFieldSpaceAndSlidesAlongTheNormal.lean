import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.TwoPoints.OneFieldSpaceAtAMirror
import Mathlib
set_option autoImplicit false
open YangMills.Construction.SpectralCalculus Filter Set
open scoped NNReal Topology
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def fullDomainOperator (B : H →L[ℂ] H) : PartialOperator H :=
  (B : H →ₗ[ℂ] H).toPMap ⊤
def IsCompositionEq (A A' : PartialOperator H) (B : H →L[ℂ] H) : Prop :=
  ∀ x : H, ∃ (hx : x ∈ A'.domain) (hy : A' ⟨x, hx⟩ ∈ A.domain), A ⟨_, hy⟩ = B x
def IsSemigroupGenerator (T : ℝ≥0 → H →L[ℂ] H) (A : PartialOperator H) : Prop :=
  (∀ x : H, x ∈ A.domain ↔
    ∃ y : H, Tendsto (fun t : ℝ≥0 => (((t : ℝ)⁻¹ : ℝ) : ℂ) • (x - T t x)) (𝓝[>] 0) (𝓝 y)) ∧
    ∀ x : A.domain,
      Tendsto (fun t : ℝ≥0 => (((t : ℝ)⁻¹ : ℝ) : ℂ) • ((x : H) - T t x)) (𝓝[>] 0) (𝓝 (A x))
def IsGroupGenerator (U : ℝ → H →L[ℂ] H) (A : PartialOperator H) : Prop :=
  (∀ x : H, x ∈ A.domain ↔
    ∃ y : H, Tendsto (fun s : ℝ => (Complex.I * (s : ℂ))⁻¹ • (U s x - x)) (𝓝[≠] 0) (𝓝 y)) ∧
    ∀ x : A.domain,
      Tendsto (fun s : ℝ => (Complex.I * (s : ℂ))⁻¹ • (U s (x : H) - x)) (𝓝[≠] 0) (𝓝 (A x))
end Operators
def nonnegEnergyStrip (B : MeasurableSubtype ℝ) : MeasurableSubtype SpectralPlane :=
  ⟨{p | (p.1 : ℝ) ∈ B.1}, (measurable_coe_nnreal_real.comp measurable_fst) B.2⟩
def TranslationRespectsClasses (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (n v : AmbientSpace) : Prop :=
  ∃ h : ∀ f : halfSpaceDomain n, translateFun v (f : AmbientSpace → ℂ) ∈ halfSpaceDomain n,
    ∀ f g : halfSpaceDomain n, reflectedClass S n f = reflectedClass S n g →
      reflectedClass S n ⟨_, h f⟩ = reflectedClass S n ⟨_, h g⟩
def TranslationExtendsUniquely (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (n v : AmbientSpace) : Prop :=
  TranslationRespectsClasses S n v ∧ ∃! B, ActsByTranslation S n v B
structure HasTransferSemigroup (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (n : AmbientSpace) : Prop where
  posHermitian : IsPosHermitianForm (reflectedForm S n)
  complete : IsCompleteForm fun x y : ReflectedSpace S n => inner ℂ x y
  translation_extends : ∀ s : ℝ≥0, TranslationExtendsUniquely S n ((s : ℝ) • n)
  selfAdjointContraction : IsSelfAdjointContractionSemigroup (transferSemigroup S n)
structure HasLateralGroup (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (n m : AmbientSpace) : Prop where
  translation_extends : ∀ s : ℝ, TranslationExtendsUniquely S n (s • m)
  commuting : IsCommutingSemigroupGroup (transferSemigroup S n) (lateralGroup S n m)
  existsUnique_jointMeasure : ∃! P, IsJointSpectralMeasure S n m P
  hamiltonian_nonneg : IsPositivePartial (reflectedHamiltonian S n m)
  momentum_selfAdjoint : IsSelfAdjointPartial (reflectedMomentum S n m)
  hamiltonian_generates : IsSemigroupGenerator (transferSemigroup S n) (reflectedHamiltonian S n m)
  momentum_generates : IsGroupGenerator (lateralGroup S n m) (reflectedMomentum S n m)
  transferSemigroup_eq : ∀ t : ℝ≥0, expNegMul t (reflectedHamiltonian S n m) =
    fullDomainOperator (transferSemigroup S n t)
  lateralGroup_eq : ∀ s : ℝ, expIMul s (reflectedMomentum S n m) =
    fullDomainOperator (lateralGroup S n m s)
  product_eq_integral : ∀ (t : ℝ≥0) (s : ℝ),
    IsCompositionEq (expNegMul t (reflectedHamiltonian S n m))
      (expIMul s (reflectedMomentum S n m))
      ((jointSpectralMeasure S n m).boundedSpectralIntegral (spectralCharacter t s))
  stronglyCommute : CommuteSpectrally (reflectedHamiltonian S n m) (reflectedMomentum S n m)
  spectralProjection_hamiltonian : ∀ B : MeasurableSubtype ℝ,
    spectralProjection (reflectedHamiltonian S n m) B =
      jointSpectralMeasure S n m (nonnegEnergyStrip B)
  spectralProjection_momentum : ∀ B : MeasurableSubtype ℝ,
    spectralProjection (reflectedMomentum S n m) B = jointSpectralMeasure S n m (cylinderSet B)
def shiftedHalfPlane (δ : ℝ) : Set ℂ := {z | -δ < z.re}
structure IsSlideContinuation (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (n : AmbientSpace) (δ : ℝ) (f g : AmbientSpace → ℂ) (F : ℂ → ℂ) : Prop where
  holomorphic : Coordinates.ComplexCoordinates.IsHolomorphicVia (Equiv.funUnique (Fin 1) ℂ).symm
    (Equiv.funUnique (Fin 1) ℂ).symm (shiftedHalfPlane δ) F
  eq_slideFn : ∀ s ∈ slideRange δ, F (s : ℂ) = slideFn S n f g s
def slideContinuation (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (n : AmbientSpace)
    (δ : ℝ) (f g : AmbientSpace → ℂ) : ℂ → ℂ :=
  Classical.epsilon (IsSlideContinuation S n δ f g)
def ReflectedSpaceAndSlides.Statement : Prop :=
  ∀ (κ : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (C : ℝ → ℝ → ℝ)
    (n : AmbientSpace),
    IsReflectedFormData κ S n → IsBallDecayBound κ S C →
      (HasTransferSemigroup S n ∧
        (∀ m : AmbientSpace, IsUnitNormalTo n m → HasLateralGroup S n m) ∧
        ∀ m m' : AmbientSpace, IsUnitNormalTo n m → IsUnitNormalTo n m' →
          reflectedHamiltonian S n m = reflectedHamiltonian S n m') ∧
      ∀ (R c δ : ℝ) (f g : AmbientSpace → ℂ), 0 < R →
        (∃ x : AmbientSpace, tsupport f ⊆ euclidClosedBall x R) →
        (∃ x : AmbientSpace, tsupport g ⊆ euclidClosedBall x R) →
        IsSeparatedPair n c δ f g →
          IsSlideContinuation S n δ f g (slideContinuation S n δ f g) ∧
          ∀ η : ℝ, 0 < η → η ≤ δ / 2 → ∀ z : ℂ, -δ + 2 * η ≤ z.re →
            ‖slideContinuation S n δ f g z‖ ≤
              4 * C (2 * η) R * κ.sharpNorm f * κ.sharpNorm g
end YangMills.Construction.TwoPoints
end
