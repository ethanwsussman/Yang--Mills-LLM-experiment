import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.FormsOfTheChainAtTheFlatField
import YangMills.Construction.RunningCouplingSlope.TotalsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Conventions YangMills.Construction.FlatLinearization
namespace RunningCouplingSlope
def WilsonActionHasFlowKernel : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, IsAdmissibleBlockingFactor L →
    ∃ h : BondKernel, IsFlowKernel h ∧
      ∀ᶠ m in Filter.atTop, HasHessianAtTrivial (minimalActionTotal a L 0) (h m)
end RunningCouplingSlope
end YangMills.Construction
end
