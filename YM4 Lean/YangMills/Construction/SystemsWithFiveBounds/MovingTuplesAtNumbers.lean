import YangMills.Construction.BoundsOnEverySide.MovingTuplesOfALimitAlongStates
import YangMills.Construction.SystemsWithFiveBounds.OnePointAtEveryRadius
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
def freeMomentConstantsOf (F : StatedSideFamily) (N : BoundConstants) :
    BoundsOnEverySide.FreeMomentConstants where
  M := F.M
  one_le_M := F.one_le_M
  cStar := fun n d R => ENNReal.ofReal (N.cumulantBound n d R)
  cTr := radiusTransferConstant F.M N
def TranslatedTuplesWithConstants : Prop :=
  ∀ (F : StatedSideFamily) (N : BoundConstants), BoundsHoldAt F N →
    ∀ (s : Conventions.StandingParameters) (K : ℕ → ℕ) (β : ℕ → ℝ)
    (ρ ν : ∀ k, Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L (K k : ℤ))))
    (σ : R4TupleForms.FinTuple s → ℝ),
    s.L = F.L → BoundsOnEverySide.IsPeriodicStateLimit K β ρ ν σ →
    (∀ k (hk : 0 < K k), F.IsFirstPassage ⟨K k, hk⟩ (β k)) →
    (∀ k (hk : 0 < K k), ρ k ∈ F.stateSet s.L ⟨K k, hk⟩ (β k)) →
    (∀ k (hk : 0 < K k), ν k ∈ F.stateSet s.L ⟨K k, hk⟩ (β k)) →
    BoundsOnEverySide.TranslatedTuples.LimitProperties (freeMomentConstantsOf F N) ρ ν σ
end YangMills.Construction.SystemsWithFiveBounds
end
