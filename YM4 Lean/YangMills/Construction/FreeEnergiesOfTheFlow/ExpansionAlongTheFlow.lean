import YangMills.Construction.FreeEnergiesOfTheFlow.FreeEnergyDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
def expansionAlongFlow : Prop :=
  ∀ p : TorusLumps.StepParameters, ExpansionHolds p → ∀ (β : ℝ) (t : ℕ), CouplingsAboveFloor p β t →
    TorusLumps.HasExpansion p t (ClusterExpansionOfAStep.flowCoupling p β t) (ClusterExpansionOfAStep.flowFunctional p β t) ∧
      ∀ j < t, |ClusterExpansionOfAStep.flowCoupling p β (j + 1) - ClusterExpansionOfAStep.flowCoupling p β j| ≤ 2 * p.B
end YangMills.Construction.FreeEnergies
end
