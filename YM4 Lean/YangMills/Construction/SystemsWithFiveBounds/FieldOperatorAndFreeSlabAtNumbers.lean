import YangMills.Construction.BoundsOnEverySide.MovingTuplesOfALimitAlongStates
import YangMills.Construction.SystemsWithFiveBounds.InsertionConditionsOnConstants
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
def FieldOperatorAndFreeSlabFromSingleCell : Prop :=
  ∀ (s : Conventions.StandingParameters) (K : ℕ → ℕ) (V : BoundsOnEverySide.FreeMomentConstants)
    (ρ ν : ∀ k, Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L (K k : ℤ))))
    (σ : R4TupleForms.FinTuple s → ℝ) (hσ : AmbientPoints.IsTupleFunctional σ) (L : ℕ)
    (N : BoundConstants),
    Conventions.IsAdmissibleBlockingFactor L → N.Admissible →
    BoundsOnEverySide.TranslatedTuples.LimitProperties V ρ ν σ →
    SingleCellBound L V.M N (R4TupleForms.toTupleFunctional σ hσ) →
    FieldOperatorBound L V.M N (R4TupleForms.toTupleFunctional σ hσ) ∧
      FreeSlabBound L V.M N (R4TupleForms.toTupleFunctional σ hσ)
end YangMills.Construction.SystemsWithFiveBounds
end
