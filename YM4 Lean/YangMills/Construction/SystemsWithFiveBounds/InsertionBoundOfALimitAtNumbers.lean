import YangMills.Construction.BoundsOnEverySide.InsertionBoundAtAFrameOverTheBounds
import YangMills.Construction.BoundsOnEverySide.LimitsAlongStatesFreeOfAWindow
import YangMills.Construction.LimitsAlongPeriodicGibbsStates.TheLetterSForALimitAlongPeriodicGibbsStates
import YangMills.Construction.SystemsWithFiveBounds.BoundsAtNumbers
import YangMills.Construction.SystemsWithFiveBounds.InsertionConditionsOnConstants
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
def InsertionBoundsOfLimitWithConstants : Prop :=
  ∀ (F : StatedSideFamily) (N : BoundConstants) (_ : BoundsHoldAt F N)
    (s : Conventions.StandingParameters) (K : ℕ → ℕ) (β : ℕ → ℝ)
    (ρ ν : ∀ k, Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L (K k : ℤ))))
    (σ : R4TupleForms.FinTuple s → ℝ),
    s.L = F.L → BoundsOnEverySide.IsPeriodicStateLimit K β ρ ν σ →
    (∀ k (hk : 0 < K k), F.IsFirstPassage ⟨K k, hk⟩ (β k)) →
    (∀ k (hk : 0 < K k), ρ k ∈ F.stateSet s.L ⟨K k, hk⟩ (β k)) →
    (∀ k (hk : 0 < K k), ν k ∈ F.stateSet s.L ⟨K k, hk⟩ (β k)) →
    ∃ hS : PeriodicGibbsLimit.HasMultilinearConnected σ,
      BoundsOnEverySide.IsRecenteredLimitFunctional σ (PeriodicGibbsLimit.centredOfLimit σ hS) ∧
      (∀ X, Tendsto (fun k => StateLimits.pairedValue K ρ ρ k X) atTop
        (𝓝 (PeriodicGibbsLimit.centredOfLimit σ hS X))) ∧
      BoundsOnEverySide.IsPeriodicStateLimit K β ρ ρ (PeriodicGibbsLimit.centredOfLimit σ hS) ∧
      (∃ hσ : AmbientPoints.IsTupleFunctional σ,
        InsertionBounds F.L F.M N (R4TupleForms.toTupleFunctional σ hσ)) ∧
      ∃ hσ : AmbientPoints.IsTupleFunctional (PeriodicGibbsLimit.centredOfLimit σ hS),
        InsertionBounds F.L F.M N
          (R4TupleForms.toTupleFunctional (PeriodicGibbsLimit.centredOfLimit σ hS) hσ)
end YangMills.Construction.SystemsWithFiveBounds
end
