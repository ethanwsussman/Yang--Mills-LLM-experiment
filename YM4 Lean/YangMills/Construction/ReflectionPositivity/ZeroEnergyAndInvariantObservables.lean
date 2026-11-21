import YangMills.Construction.InfiniteLattice.ShiftInvariantConditioningAndPlateau
import YangMills.Construction.ReflectionPositivity.SpectralVariablesOfTheTwoPictures
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField LatticePoint IsBoundedObservable shift
  halfSpaceLocalObservables shiftInvariantSigma axisShiftInvariantSigma condExpGiven)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass linkReflect)
def GroundStateAndInvariance : Prop :=
  ∀ (ν : unitPositiveClass) (μ : Fin 4),
    (∀ F : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable F → ∀ v : LatticePoint (1 : ℝ),
      condExpGiven ν (shiftInvariantSigma 1) ((linkReflect μ).actOn F)
          =ᵐ[(ν : Measure (GaugeField (1 : ℝ)))]
        condExpGiven ν (shiftInvariantSigma 1) F ∧
      condExpGiven ν (shiftInvariantSigma 1) F
          =ᵐ[(ν : Measure (GaugeField (1 : ℝ)))]
        condExpGiven ν (shiftInvariantSigma 1) ((shift v).actOn F)) ∧
    (∀ F ∈ halfSpaceLocalObservables μ, ∀ H ∈ halfSpaceLocalObservables μ,
      inner ℂ (ReflectionPair.link.obsClass ν μ F)
          (groundProjection μ ReflectionPair.link ν (ReflectionPair.link.obsClass ν μ H)) =
        ∫ U, conj (condExpGiven ν (shiftInvariantSigma 1) F U) *
          condExpGiven ν (shiftInvariantSigma 1) H U
          ∂(ν : Measure (GaugeField (1 : ℝ)))) ∧
    (∀ J : GaugeField (1 : ℝ) → ℂ, Measurable[axisShiftInvariantSigma μ] J →
      MemLp J 2 (ν : Measure (GaugeField (1 : ℝ))) →
      ∃ J' : GaugeField (1 : ℝ) → ℂ, Measurable[shiftInvariantSigma 1] J' ∧
        J =ᵐ[(ν : Measure (GaugeField (1 : ℝ)))] J') ∧
    (∀ I' : Set (GaugeField (1 : ℝ)), MeasurableSet[axisShiftInvariantSigma μ] I' →
      ∃ I : Set (GaugeField (1 : ℝ)), MeasurableSet[shiftInvariantSigma 1] I ∧
        (ν : Measure (GaugeField (1 : ℝ))) (symmDiff I I') = 0) ∧
    (∀ F : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable F →
      condExpGiven ν (axisShiftInvariantSigma μ) F
          =ᵐ[(ν : Measure (GaugeField (1 : ℝ)))]
        condExpGiven ν (shiftInvariantSigma 1) F)
end YangMills.Construction.ReflectionPositivity.DirectionPictures
