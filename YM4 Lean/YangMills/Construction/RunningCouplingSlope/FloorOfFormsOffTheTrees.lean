import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.FormsOfTheChainAtTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
open Conventions FlatLinearization TorusFields
def offTreeFormLowerBoundStatement : Prop :=
  ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop, ∀ [NeZero n] [NeZero L]
    (ξ : RealOneForm (n * L)), VanishesOnBlockTrees L ξ →
      ∑ b, ξ b ^ 2 ≤ C * (curlEnergy ξ + ∑ c : TorusBond n, FlatLinearization.contourAverage L ξ c ^ 2)
end YangMills.Construction.RunningCouplingSlope
end
