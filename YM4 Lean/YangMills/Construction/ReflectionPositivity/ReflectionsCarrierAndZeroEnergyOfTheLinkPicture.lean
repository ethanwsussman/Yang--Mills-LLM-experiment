import YangMills.Construction.ReflectionPositivity.SpectralVariablesOfTheTwoPictures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open InfiniteLattice (GaugeField IsBoundedObservable)
open MirrorHyperplanes (unitPositiveClass UnitMirrorPair)
open FormHilbert (StrongTendsto)
def linkCone (i : Fin 4) : Set (ℝ≥0∞ × (TransverseAxis i → ℝ)) :=
  {p | p ∈ variableDomain i ∧ p.1 ≠ ⊤ ∧ slopeConstant * angleSupNorm i p.2 ≤ p.1.toReal}
def LinkPictureReflectionsConeGround : Prop :=
  ∀ (ρ : unitPositiveClass) (i : Fin 4),
    (∀ P : UnitMirrorPair,
      (∀ A : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable A →
        ∫ U, P.reflect.actOn A U ∂(ρ : Measure (GaugeField (1 : ℝ))) =
          ∫ U, A U ∂(ρ : Measure (GaugeField (1 : ℝ)))) ∧
      ∀ A B : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable A → IsBoundedObservable B →
        ‖∫ U, conj (P.reflect.actOn A U) * B U
            ∂(ρ : Measure (GaugeField (1 : ℝ)))‖ ≤
          √(∫ U, ‖A U‖ ^ 2 ∂(ρ : Measure (GaugeField (1 : ℝ)))) *
            √(∫ U, ‖B U‖ ^ 2 ∂(ρ : Measure (GaugeField (1 : ℝ))))) ∧
    (Function.Injective (ReflectionPair.link.transferOp ρ i) ∧
      ReflectionPair.link.jointPVM ρ i (spectrumBottom (TransverseAxis i)) = 0) ∧
    (∃ h : MeasurableSet (imageInSpectrum i (linkCone i)),
      (ReflectionPair.link.jointPVM ρ i).IsSupportedOn ⟨imageInSpectrum i (linkCone i), h⟩) ∧
    (StrongTendsto (fun n => ReflectionPair.link.transferOp ρ i ^ n)
        (groundProjection i ReflectionPair.link ρ) ∧
      ∀ l : TransverseAxis i,
        ReflectionPair.link.shiftOp ρ i l * groundProjection i ReflectionPair.link ρ =
            groundProjection i ReflectionPair.link ρ ∧
          groundProjection i ReflectionPair.link ρ * ReflectionPair.link.shiftOp ρ i l =
            groundProjection i ReflectionPair.link ρ)
end YangMills.Construction.ReflectionPositivity.DirectionPictures
