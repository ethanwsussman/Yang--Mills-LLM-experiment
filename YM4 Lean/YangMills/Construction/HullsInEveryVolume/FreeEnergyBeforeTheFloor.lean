import YangMills.Construction.FreeEnergiesOfTheFlow.FreeEnergyDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HullTrees
def freeEnergyLowerBoundStatement : Prop :=
  ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∃ C y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
    FreeEnergies.ExpansionHolds (T.stepParameters y) →
    ∀ (β : ℝ) (t : ℕ), FreeEnergies.CouplingsAboveFloor (T.stepParameters y) β t → ∀ (n : ℕ) [NeZero n],
      TorusLumps.IsBlockTorusSide (T.stepParameters y) n →
      Real.log (FreeEnergies.flowFunctionalAtTrivial (T.stepParameters y) β t n) -
          (C + 6 * Real.log (ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β t)) * (n : ℝ) ^ 4 ≤
        Real.log (FreeEnergies.torusPartition (T.stepParameters y) β t n)
end YangMills.Construction.HullTrees
end
