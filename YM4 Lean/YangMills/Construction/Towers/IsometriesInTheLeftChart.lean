import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.PropertiesOfTheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def LeftChartIsometryEquivariance : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k →
    (∀ n : ℕ, 0 < n → LeftChartFacts.IsometryEquivarianceForms L n k j) ∧
      FullSpace.LeftChartFacts.IsometryEquivarianceForms L k j
end YangMills.Construction.Tower
end
