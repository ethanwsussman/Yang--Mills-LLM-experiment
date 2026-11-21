import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LeftChartAlgebra
def GaugeConditionsInfiniteSide : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k →
    FullSpace.LeftChartAlgebra.GaugeCovariance L k j ∧
      FullSpace.LeftChartAlgebra.GaugeUnitarity L k j
end YangMills.Construction.Tower.LeftChartAlgebra
end
