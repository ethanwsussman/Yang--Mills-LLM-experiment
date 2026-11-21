import YangMills.Construction.EuclideanFunctionals.TuplesIsometriesFreeSpaceAndMirrorOfFourSpace
import YangMills.Construction.InfiniteLattice.CentredMomentsAtOneIndexAndTheTwoFormsOfVolumeFirst
import YangMills.Construction.LimitsAlongPeriodicGibbsStates.FirstPassageSequencesSetsOfStatesAndTheObservable
import YangMills.Construction.LimitsAlongPeriodicGibbsStates.PeriodicGibbsLimitStandingDefs
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicGibbsLimits.ObservablesAndMomentsDefined
def HasFiniteFaceSum {a : ℝ} {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f : YangMills.Construction.InfiniteLattice.AmbientSpace → E)
    (U : YangMills.Construction.InfiniteLattice.GaugeField a) : Prop :=
  (Function.support fun p : YangMills.Construction.InfiniteLattice.ElementaryPlaquette a =>
    YangMills.Construction.InfiniteLattice.faceEnergy U p • f p.center).Finite
def CenteredMomentIntegrable {a : ℝ}
    (ρ ν : Measure (YangMills.Construction.InfiniteLattice.GaugeField a))
    (X : YangMills.Construction.EuclideanFunctionals.FnList) : Prop :=
  (∀ i, Integrable (fun U =>
      ((YangMills.Construction.InfiniteLattice.smearedEnergy (X.get i) U : ℝ) : ℂ)) ν) ∧
    Integrable (YangMills.Construction.CutoffLimits.CenteredMomentsAndVolumeFirst.centeredProduct
      ν X.get) ρ
def Statement : Prop :=
  (∀ a : ℝ, 0 < a →
    (∀ f : YangMills.Construction.InfiniteLattice.AmbientSpace → ℝ,
      YangMills.Construction.InfiniteLattice.IsBoundedBorelCompactlySupported f →
      (∀ U : YangMills.Construction.InfiniteLattice.GaugeField a, HasFiniteFaceSum f U) ∧
      YangMills.Construction.Probability.IsBoundedRealRV
        (YangMills.Construction.InfiniteLattice.smearedEnergy f :
          YangMills.Construction.InfiniteLattice.GaugeField a → ℝ)) ∧
    (∀ f : YangMills.Construction.InfiniteLattice.AmbientSpace → ℂ,
      YangMills.Construction.InfiniteLattice.IsBoundedBorelCompactlySupported f →
      (∀ U : YangMills.Construction.InfiniteLattice.GaugeField a, HasFiniteFaceSum f U) ∧
      YangMills.Construction.InfiniteLattice.IsBoundedObservable
        (YangMills.Construction.InfiniteLattice.smearedEnergy f :
          YangMills.Construction.InfiniteLattice.GaugeField a → ℂ) ∧
      YangMills.Construction.InfiniteLattice.IsBoundedObservable
        (YangMills.Construction.PeriodicGibbsLimits.complexObservable f :
          YangMills.Construction.InfiniteLattice.GaugeField a → ℂ))) ∧
  (∀ (D : YangMills.Construction.PeriodicGibbsLimits.LimitData)
    (Q : YangMills.Construction.PeriodicGibbsLimits.CutoffSequence D) (k : ℕ+)
    (ρ ν : Measure (Q.Fields k)),
    ρ ∈ Q.states k → ν ∈ Q.states k →
      ∀ X ∈ YangMills.Construction.EuclideanFunctionals.sepAll,
        CenteredMomentIntegrable ρ ν X) ∧
  (∀ (D : YangMills.Construction.GrowingTori.GrowthParameters) (g : ℝ)
    (Q : YangMills.Construction.FirstPassageSeqs.FirstPassageSequence D g) (k : ℕ+)
    (ρ ν : Measure (Q.Fields k)),
    ρ ∈ Q.gibbsStates k → ν ∈ Q.gibbsStates k →
      ∀ X ∈ YangMills.Construction.EuclideanFunctionals.sepAll,
        CenteredMomentIntegrable ρ ν X)
end YangMills.Construction.PeriodicGibbsLimits.ObservablesAndMomentsDefined
end
