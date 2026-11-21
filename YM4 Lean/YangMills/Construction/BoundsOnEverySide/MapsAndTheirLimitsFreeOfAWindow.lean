import YangMills.Construction.BoundsOnEverySide.LimitsAlongStatesFreeOfAWindow
import YangMills.Construction.LimitsAlongPeriodicGibbsStates.MapsAlongStatesAndTheirLimitsAreFunctionals
import Mathlib
set_option autoImplicit false
open MeasureTheory
namespace YangMills.Construction.BoundsOnEverySide
def StateMapsAndLimitsAreSeparatedFunctionals : Prop :=
  (∀ (s : Conventions.StandingParameters) (K : ℕ → ℕ) (β : ℕ → ℝ)
      (ρ ν : ∀ k, Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L (K k : ℤ)))),
      (∀ k, 0 < K k) → StateLimits.IsPeriodicGibbsSeq K β ρ ν →
      (∀ k, StateLimits.SeparatedFunctionals.HasConnectedParts K ρ ν k) ∧
        ∀ σ : R4TupleForms.FinTuple s → ℝ, IsPeriodicStateLimit K β ρ ν σ →
          StateLimits.SeparatedFunctionals.IsSymmSepFunctional σ ∧
            StateLimits.SeparatedFunctionals.ConnectedTendsto K ρ ν σ ∧
            StateLimits.SeparatedFunctionals.FirstOrderTendsto K ρ ν σ ∧
            StateLimits.SeparatedFunctionals.HigherOrderTendstoCumulant K ρ σ ∧
            (∀ (n : ℕ), 1 ≤ n → AmbientPoints.IsTupleSymmetric (AmbientPoints.connectedOf σ n) ∧
              AmbientPoints.IsTupleMultilinear (AmbientPoints.connectedOf σ n)) ∧
            ∃ S : AmbientPoints.ConnectedFamily s .euclidean,
              ∀ (n : ℕ) (hn : 2 ≤ n), S.fn n hn = AmbientPoints.connectedOf σ n) ∧
    ∀ (s : Conventions.StandingParameters) (σ : R4TupleForms.FinTuple s → ℝ),
      AmbientPoints.IsTupleFunctional σ →
      StateLimits.SeparatedFunctionals.IsPartitionExpansion σ
end YangMills.Construction.BoundsOnEverySide
