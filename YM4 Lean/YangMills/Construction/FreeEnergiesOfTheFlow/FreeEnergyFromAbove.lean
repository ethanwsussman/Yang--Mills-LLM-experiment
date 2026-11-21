import YangMills.Construction.FreeEnergiesOfTheFlow.FreeEnergyDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
def freeEnergyUpperBound : Prop :=
  ∀ p : TorusLumps.StepParameters, p.Admissible → 4 * p.n₀ + 2 ^ 16 ≤ TorusLumps.clusterRange p.y₁ →
    ExpansionHolds p → ∀ (β : ℝ) (t : ℕ), CouplingsAboveFloor p β t →
    ∀ (n : ℕ) [NeZero n], TorusLumps.IsBlockTorusSide p n →
      0 < flowFunctionalAtTrivial p β t n ∧
      Real.log (torusPartition p β t n) ≤
        Real.log (flowFunctionalAtTrivial p β t n) + (Real.log 2 + 2 * p.E) * (n : ℝ) ^ 4
end YangMills.Construction.FreeEnergies
end
