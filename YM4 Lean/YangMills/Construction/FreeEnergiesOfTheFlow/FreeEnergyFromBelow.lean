import YangMills.Construction.FreeEnergiesOfTheFlow.FreeEnergyDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
def freeEnergyLowerBound : Prop :=
  HoldsForAdmissibleParameters fun T y => ∃ C : ℝ, ∀ (β : ℝ) (t : ℕ), CouplingsAboveFloor (T.stepParameters y) β t →
    ∀ (n : ℕ) [NeZero n], TorusLumps.IsBlockTorusSide (T.stepParameters y) n →
      Real.log (flowFunctionalAtTrivial (T.stepParameters y) β t n) -
          (C + 6 * Real.log (ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β t)) * (n : ℝ) ^ 4 ≤
        Real.log (torusPartition (T.stepParameters y) β t n)
end YangMills.Construction.FreeEnergies
end
