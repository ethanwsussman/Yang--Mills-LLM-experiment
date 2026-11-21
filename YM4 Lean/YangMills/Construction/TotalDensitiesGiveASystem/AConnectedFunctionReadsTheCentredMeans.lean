import YangMills.Construction.InfiniteLattice.RepresentativeOfASeparatedTupleCentredAtAState
import YangMills.Construction.LimitTheorem.FunctionalDefs
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
open LimitTheorem SeparatedTuples
open InfiniteLattice (GaugeField smearedEnergyCumulant)
open TestSpaces (SepTupleOfCard)
def connectedOfCentredMeansStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ X : SepTupleOfCard n, ∃ (k : ℕ) (W : Fin k → SepTuple) (P : (Fin k → ℝ) → ℝ), Continuous P ∧
    (∀ σ : TupleFunctional, connectedFn σ X = P fun i => σ (W i)) ∧
    ∀ (L : ℕ) (K : ℕ), Conventions.IsAdmissibleBlockingFactor L →
      ∀ ν ρ : Measure (GaugeField (PeriodicLattice.meshSize L (K : ℤ))), IsProbabilityMeasure ρ →
        smearedEnergyCumulant ρ X.1 =
          ((P fun i => ∫ U, CenteredRepresentatives.centeredRep L K ν (W i) U ∂ρ : ℝ) : ℂ)
end YangMills.Construction.TotalDensitiesGiveASystem
end
