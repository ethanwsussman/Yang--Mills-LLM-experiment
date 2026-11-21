import YangMills.Construction.Towers.FunctionsOfTwoSidesAndTheirMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.UnitScale
open OneStepChart
def CrossingSmoothingIsPeriodicOperator : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m k j : ℕ, 0 < m → j < k →
    PeriodicOperator (edgeForms L m k j) (edgeForms L m k (j + 1))
      (Tower.FullSpace.crossingSmoothing L) (Tower.crossingSmoothing L m k j)
end YangMills.Construction.Tower.UnitScale
end
