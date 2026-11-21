import YangMills.Construction.Towers.FunctionsOfTwoSidesAndTheirMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.UnitScale.OneStepChart
def PeriodicOperatorIsTwoScaleMap : Prop :=
  ∀ (s : ℕ), 0 < s → ∀ (X Y : TwoScaleFunctions), CellCoordinates s X → CellCoordinates s Y →
    ∀ (O : (X.fullSpace.index → Matrices.ComplexMatrix2) → Y.fullSpace.index → Matrices.ComplexMatrix2)
      (O' : (X.torusSpace.index → Matrices.ComplexMatrix2) → Y.torusSpace.index →
        Matrices.ComplexMatrix2),
      PeriodicOperator X Y O O' → TwoScaleMap X Y O O'
end YangMills.Construction.Tower.UnitScale.OneStepChart
end
