import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.PropertiesOfTheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def LeftChartFacts.HoldEverywhere : Prop :=
  ∀ L k j j' j'' : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k → j' ≤ k → j'' ≤ k →
    LeftChartFacts.IsBiInvariantMetric ∧
    (∀ n : ℕ, 0 < n →
      LeftChartFacts.TangentSpaceIsoForms L n k j ∧
      LeftChartFacts.DifferentialsFromCurves L n k j j' ∧
      LeftChartFacts.CompChainRule L n k j j' j'' ∧
      LeftChartFacts.GaugeOrbitTangent L n k j ∧
      LeftChartFacts.GaugeEquivarianceForms L n k j ∧
      LeftChartFacts.IsometryEquivarianceForms L n k j) ∧
    FullSpace.LeftChartFacts.DifferentialsFromCurves L k j j' ∧
    FullSpace.LeftChartFacts.CompChainRule L k j j' j'' ∧
    FullSpace.LeftChartFacts.ChainRuleViaPresentations L k j j' j'' ∧
    FullSpace.LeftChartFacts.GaugeOrbitTangent L k j ∧
    FullSpace.LeftChartFacts.GaugeEquivarianceForms L k j ∧
    FullSpace.LeftChartFacts.IsometryEquivarianceForms L k j
end Tower
end YangMills.Construction
end
