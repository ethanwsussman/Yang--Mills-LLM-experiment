import YangMills.Construction.Continuum.CentredMomentsOfTheCumulantsAndOfTheirLimits
import YangMills.Construction.LimitsAlongPeriodicGibbsStates.MomentsAndObservablesAreFormed
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
open InfiniteLattice (GaugeField IsBoundedBorelCompactlySupported IsBoundedObservable AmbientSpace
  smearedEnergy)
open PeriodicGibbsLimits (complexObservable)
open PeriodicGibbsLimits.ObservablesAndMomentsDefined (HasFiniteFaceSum)
open AmbientPoints (ConnectedFamily)
def SmearedObservablesWellDefined : Prop :=
  ∀ a : ℝ, 0 < a →
    (∀ f : AmbientSpace → ℝ, IsBoundedBorelCompactlySupported f →
      (∀ U : GaugeField a, HasFiniteFaceSum f U) ∧
      Probability.IsBoundedRealRV (smearedEnergy f : GaugeField a → ℝ)) ∧
    (∀ f : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported f →
      (∀ U : GaugeField a, HasFiniteFaceSum f U) ∧
      IsBoundedObservable (smearedEnergy f : GaugeField a → ℂ) ∧
      IsBoundedObservable (complexObservable f : GaugeField a → ℂ))
def ConnectedFamilyMomentsAreFunctional : Prop :=
  ∀ (s : Conventions.StandingParameters) (S : ConnectedFamily s .euclidean),
    CumulantLimits.MomentsIsFunctional S
theorem smearedObservablesWellDefined_of
    (h : PeriodicGibbsLimits.ObservablesAndMomentsDefined.Statement) :
    SmearedObservablesWellDefined := h.1
theorem connectedFamilyMomentsAreFunctional_of
    (h : CumulantLimits.CentredMomentsAndTheirLimits) :
    ConnectedFamilyMomentsAreFunctional := h.2.2.2
end YangMills.Construction.SystemsWithFiveBounds
end
