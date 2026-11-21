import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.BondsIsometriesAndStatesOfTheLatticeOfACutoff
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.CutoffLatticeStates
open YangMills.Construction.InfiniteLattice
section Transport
variable {a : ℝ}
def PlaquetteTransport (r : latticeMotions a) (p : ElementaryPlaquette a)
    (U : GaugeField a) : Prop :=
  (mapPlaquette r p).closedSquare = p.squareImage r.1 ∧
    (mapPlaquette r p).center = r.1 p.center ∧
    faceEnergy (latticeMotionField r U) p = faceEnergy U (mapPlaquette r p)
def ObservableTransport {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (r : latticeMotions a) (f : AmbientSpace → E) : Prop :=
  (fun U : GaugeField a => smearedEnergy f (latticeMotionField r U)) =
      smearedEnergy (f ∘ motionInverse r) ∧
    (smearedEnergy (f ∘ motionInverse r) : GaugeField a → E) =
      smearedEnergy (pushFunction r f)
def ConnectedFunctionsInvariant {n : ℕ} (r : latticeMotions a)
    (μ μ' : Measure (GaugeField a)) (X : Fin n → AmbientSpace → ℝ) : Prop :=
  connectedFunction μ (pushTuple r X) = connectedFunction μ X ∧
    centeredMoment μ (pushTuple r X) = centeredMoment μ X ∧
    centeredMomentAgainst μ' μ (pushTuple r X) = centeredMomentAgainst μ' μ X
end Transport
def StatesInvariantUnderMotions : Prop :=
  ∀ (s : Conventions.StandingParameters) (β : ℝ), 0 < β →
    (∀ m : ℕ, 0 < m →
      ∃ _ : IsProbabilityMeasure (liftedWilsonMeasure s.L m s.K β),
        IsMotionInvariant (liftedWilsonMeasure s.L m s.K β)) ∧
    (∀ (μ : Measure (RefinedGaugeField s.L s.K)) [IsProbabilityMeasure μ],
      μ ∈ weakLimitPoints s.L s.K β → IsMotionInvariant μ) ∧
    (∀ (μ : Measure (RefinedGaugeField s.L s.K)) [IsProbabilityMeasure μ],
      IsPeriodicGibbs β μ → IsMotionInvariant μ) ∧
    ∀ r : refinedLatticeMotions s.L s.K,
      (∀ (p : ElementaryPlaquette (refinedSpacing s.L s.K)) (U : RefinedGaugeField s.L s.K),
        PlaquetteTransport r p U) ∧
      (∀ f : AmbientSpace → ℝ, IsBoundedBorelCompactlySupported f → ObservableTransport r f) ∧
      (∀ f : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported f → ObservableTransport r f) ∧
      ∀ (μ μ' : Measure (RefinedGaugeField s.L s.K)) [IsProbabilityMeasure μ]
        [IsProbabilityMeasure μ'], IsLatticeMotionInvariant μ r → IsLatticeMotionInvariant μ' r →
        ∀ (n : ℕ), 1 ≤ n → ∀ X : Fin n → AmbientSpace → ℝ,
          (∀ i, IsBoundedBorelCompactlySupported (X i)) →
          ConnectedFunctionsInvariant r μ μ' X
end YangMills.Construction.CutoffLatticeStates
