import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.GroundOfItsState
import YangMills.Construction.ClusterExpansionOfAStep.GroundsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open YangMills.Construction.StepSettings YangMills.Construction.RenormalizationStepParameters YangMills.Construction.TorusLumps YangMills.Construction.TorusFields YangMills.Construction.StepGas
def NonvanishingStateHotGround : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.IsWellPosed →
    R.nextCoupling ≤ 1.01 * R.coupling → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
      ∀ (V : TorusField n) (q : CoarseState R n),
      IsHullState R.params R.nextRange V q.1 → (∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) →
        (hotCaseGround R V q).IsOverState
end YangMills.Construction.ClusterExpansionOfAStep
end
