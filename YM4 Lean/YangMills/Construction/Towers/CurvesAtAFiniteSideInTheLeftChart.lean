import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.PropertiesOfTheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def FiniteLevelCurveDifferentials.Statement : Prop :=
  ∀ L k j j' : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k → j' ≤ k →
    ∀ n : ℕ, 0 < n → LeftChartFacts.DifferentialsFromCurves L n k j j'
end Tower
end YangMills.Construction
end
