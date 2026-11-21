import YangMills.Construction.InfiniteLattice.IntegrableVersionsAndVariance
import YangMills.Construction.InfiniteLattice.RegularConditionalProbabilityOfAPeriodicGibbsState
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.LatticePhases
open YangMills.Construction.InfiniteLattice (GaugeField periodicGibbsSet shiftInvariantSigma
  IsBoundedObservable IsIntegrableCondExpRepresentative)
variable (S : Setup)
def SatisfiesIndicatorCriterion (ν : periodicGibbsSet S.L S.K S.β)
    (k : GaugeField S.mesh → ProbMeasure (GaugeField S.mesh)) : Prop :=
  ∀ B : Set (GaugeField S.mesh), MeasurableSet B →
    Measurable[shiftInvariantSigma S.mesh]
        (fun A => (k A).eval (B.indicator (1 : GaugeField S.mesh → ℂ))) ∧
      ∀ T : Set (GaugeField S.mesh), MeasurableSet[shiftInvariantSigma S.mesh] T →
        ∫ A, T.indicator (1 : GaugeField S.mesh → ℂ) A *
            (k A).eval (B.indicator (1 : GaugeField S.mesh → ℂ)) ∂ν.1 =
          ∫ A, T.indicator (1 : GaugeField S.mesh → ℂ) A *
            B.indicator (1 : GaugeField S.mesh → ℂ) A ∂ν.1
def InvariantConditionalFamilyFacts (ν : periodicGibbsSet S.L S.K S.β) : Prop :=
  (∀ k : GaugeField S.mesh → ProbMeasure (GaugeField S.mesh),
    SatisfiesIndicatorCriterion S ν k → IsInvariantConditionalFamily S ν k) ∧
  (∃ k : GaugeField S.mesh → ProbMeasure (GaugeField S.mesh),
    IsInvariantConditionalFamily S ν k) ∧
  (∀ k : GaugeField S.mesh → ProbMeasure (GaugeField S.mesh),
    IsInvariantConditionalFamily S ν k →
      ∀ G : GaugeField S.mesh → ℂ, IsBoundedObservable G →
        IsIntegrableCondExpRepresentative ν.1 G (fun A => (k A).eval G) ∧
          ∀ V : GaugeField S.mesh → ℂ, IsIntegrableCondExpRepresentative ν.1 G V →
            ∀ᵐ A ∂ν.1, (k A).eval G = V A) ∧
  (∀ k : GaugeField S.mesh → ProbMeasure (GaugeField S.mesh),
    IsInvariantConditionalFamily S ν k →
      ∀ G : GaugeField S.mesh → ℂ, IsBoundedObservable G →
        ∫ A, G A ∂ν.1 = ∫ A, (k A).eval G ∂ν.1)
def InvariantConditionalFamilies.Statement : Prop :=
  ∀ (S : Setup) (ν : periodicGibbsSet S.L S.K S.β), InvariantConditionalFamilyFacts S ν
end YangMills.Construction.LatticePhases
