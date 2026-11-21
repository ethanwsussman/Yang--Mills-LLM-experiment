import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower.LeftChartAlgebra
def GaugeConditionsFiniteSide : Prop :=
  ∀ L m k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → j ≤ k →
    GaugeCovariance L m k j ∧ GaugeUnitarity L m k j
end YangMills.Construction.Tower.LeftChartAlgebra
