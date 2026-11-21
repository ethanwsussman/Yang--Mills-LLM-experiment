import YangMills.Construction.BoundsOnEverySide.LimitsAlongStatesFreeOfAWindow
import YangMills.Construction.SystemsWithFiveBounds.BoundsAtNumbers
import YangMills.Construction.SystemsWithFiveBounds.InsertionConditionsOnConstants
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
def SingleCellBoundOfLimit : Prop :=
  ∀ (F : StatedSideFamily) (N : BoundConstants), BoundsHoldAt F N →
    ∀ (s : Conventions.StandingParameters) (K : ℕ → ℕ) (β : ℕ → ℝ)
    (ρ ν : ∀ k, Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L (K k : ℤ))))
    (σ : R4TupleForms.FinTuple s → ℝ) (hσ : AmbientPoints.IsTupleFunctional σ),
    s.L = F.L → BoundsOnEverySide.IsPeriodicStateLimit K β ρ ν σ →
    (∀ k (hk : 0 < K k), F.IsFirstPassage ⟨K k, hk⟩ (β k)) →
    (∀ k (hk : 0 < K k), ρ k ∈ F.stateSet s.L ⟨K k, hk⟩ (β k)) →
    (∀ k (hk : 0 < K k), ν k ∈ F.stateSet s.L ⟨K k, hk⟩ (β k)) →
    SingleCellBound F.L F.M N (R4TupleForms.toTupleFunctional σ hσ)
end YangMills.Construction.SystemsWithFiveBounds
end
