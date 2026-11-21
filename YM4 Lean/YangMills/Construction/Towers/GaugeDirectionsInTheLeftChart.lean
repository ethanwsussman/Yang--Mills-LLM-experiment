import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.PropertiesOfTheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def GaugeOrbitTangentInLeftChart.Statement : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k →
    (∀ n : ℕ, 0 < n → LeftChartFacts.GaugeOrbitTangent L n k j) ∧
      FullSpace.LeftChartFacts.GaugeOrbitTangent L k j
end Tower
end YangMills.Construction
end
