import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.PropertiesOfTheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def FullSpaceChainRule.Statement : Prop :=
  ∀ L k j j' j'' : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k → j' ≤ k → j'' ≤ k →
    FullSpace.LeftChartFacts.CompChainRule L k j j' j''
end Tower
end YangMills.Construction
end
