import YangMills.Construction.InfiniteLattice.RepresentativeOfATupleAndLimitsAlongStates
import Mathlib
set_option autoImplicit false
open MeasureTheory
namespace YangMills.Construction.BoundsOnEverySide
open InfiniteLattice R4TupleForms StateLimits
structure IsPeriodicStateLimit {s : Conventions.StandingParameters} (K : ℕ → ℕ) (β : ℕ → ℝ)
    (ρ ν : ∀ j, Measure (GaugeField (PeriodicLattice.meshSize s.L (K j : ℤ))))
    (σ : FinTuple s → ℝ) : Prop where
  cutoff_pos : ∀ j, 0 < K j
  periodicGibbs : IsPeriodicGibbsSeq K β ρ ν
  pointwise : IsPointwiseLimit K ρ ν σ
end YangMills.Construction.BoundsOnEverySide
