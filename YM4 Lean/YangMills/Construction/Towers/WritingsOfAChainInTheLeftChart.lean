import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.PropertiesOfTheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def LeftChartChainRule : Prop :=
  ∀ L k j j' j'' : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k → j' ≤ k → j'' ≤ k →
    FullSpace.LeftChartFacts.ChainRuleViaPresentations L k j j' j''
end Tower
end YangMills.Construction
end
