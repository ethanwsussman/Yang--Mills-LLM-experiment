import YangMills.Construction.FreeEnergiesOfTheFlow.FreeEnergyDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
def freeEnergyVolumeScaling : Prop :=
  HoldsForAdmissibleParameters fun T y => ∃ C nS : ℝ, 0 ≤ C ∧ 1 ≤ nS ∧ ∀ (β : ℝ) (t : ℕ),
    CouplingsAboveFloor (T.stepParameters y) β t →
    ∀ (n n' : ℕ) [NeZero n] [NeZero n'], TorusLumps.IsBlockTorusSide (T.stepParameters y) n →
      TorusLumps.IsBlockTorusSide (T.stepParameters y) n' → n ≤ n' →
      nS * ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β t ^ ((1 : ℝ) / 100) ≤ n →
        0 < torusPartition (T.stepParameters y) β t n ∧ 0 < torusPartition (T.stepParameters y) β t n' ∧
        |Real.log (torusPartition (T.stepParameters y) β t n') -
            (n' : ℝ) ^ 4 / (n : ℝ) ^ 4 * Real.log (torusPartition (T.stepParameters y) β t n)| ≤
          C * (1 + Real.log (ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β t)) * (n' : ℝ) ^ 4
end YangMills.Construction.FreeEnergies
end
