import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.PropertiesOfTheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def LeftChartTangentSpaces : Prop :=
  LeftChartFacts.IsBiInvariantMetric ∧
    ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k → ∀ n : ℕ, 0 < n →
      LeftChartFacts.TangentSpaceIsoForms L n k j
end YangMills.Construction.Tower
end
