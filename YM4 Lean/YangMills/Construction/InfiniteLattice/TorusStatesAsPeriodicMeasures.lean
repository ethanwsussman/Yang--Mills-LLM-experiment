import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.WeakLimitPointsAlongSides
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def LiftIsBijectionOntoPeriodicFields (L m K : ℕ) : Prop :=
  (∀ (W : PeriodicLattice.CompactGaugeField L m (K : ℤ))
      (b : Link (PeriodicLattice.meshSize L (K : ℤ))),
      liftCompactField W b = W.linkValue (projectLink L m (K : ℤ) b)) ∧
    BijOn (liftCompactField : PeriodicLattice.CompactGaugeField L m (K : ℤ) → _) univ
      (periodicFields L m (K : ℤ))
def LiftedWilsonMeasureIsShiftInvariantProbability (L m K : ℕ) (β : ℝ) : Prop :=
  IsProbabilityMeasure (liftedWilsonMeasure L m K β) ∧
    ∀ v : LatticePoint (PeriodicLattice.meshSize L (K : ℤ)),
      IsSymmetricUnder (liftedWilsonMeasure L m K β) (shift v)
def LimitsAlongSidesAreShiftInvariant (L K : ℕ) (β : ℝ) : Prop :=
  ∀ ν ∈ weakLimitsAlongSides L K β, IsProbabilityMeasure ν ∧ IsShiftInvariant ν
def TorusStatesAsPeriodic.Statement : Prop :=
  ∀ (s : Conventions.StandingParameters) (β : ℝ), 0 < β →
    LiftIsBijectionOntoPeriodicFields s.L s.m s.K ∧
      LiftedWilsonMeasureIsShiftInvariantProbability s.L s.m s.K β ∧
      LimitsAlongSidesAreShiftInvariant s.L s.K β
end YangMills.Construction.InfiniteLattice
