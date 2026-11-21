import YangMills.Construction.InfiniteLattice.ShiftInvariantConditioningAndPlateau
import YangMills.Construction.ReflectionPositivity.SpectralVariablesOfTheTwoPictures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField LatticePoint shift halfSpaceLocalObservables
  IsBoundedObservable condExpGiven shiftInvariantSigma)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass siteReflect)
def SitePictureGroundStateTheorem : Prop :=
  ∀ (ν : unitPositiveClass) (μ : Fin 4),
  (∀ F ∈ halfSpaceLocalObservables μ, ∀ H ∈ halfSpaceLocalObservables μ,
    inner ℂ (ReflectionPair.site.obsClass ν μ F)
        (groundProjection μ ReflectionPair.site ν (ReflectionPair.site.obsClass ν μ H)) =
      ∫ U, conj (condExpGiven ν (shiftInvariantSigma 1) F U) *
        condExpGiven ν (shiftInvariantSigma 1) H U
        ∂(ν : Measure (GaugeField (1 : ℝ)))) ∧
  ∀ F : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable F → ∀ v : LatticePoint (1 : ℝ),
    condExpGiven ν (shiftInvariantSigma 1) ((siteReflect μ).actOn F)
        =ᵐ[(ν : Measure (GaugeField (1 : ℝ)))] condExpGiven ν (shiftInvariantSigma 1) F ∧
      condExpGiven ν (shiftInvariantSigma 1) F
        =ᵐ[(ν : Measure (GaugeField (1 : ℝ)))]
          condExpGiven ν (shiftInvariantSigma 1) ((shift v).actOn F)
end YangMills.Construction.ReflectionPositivity.DirectionPictures
