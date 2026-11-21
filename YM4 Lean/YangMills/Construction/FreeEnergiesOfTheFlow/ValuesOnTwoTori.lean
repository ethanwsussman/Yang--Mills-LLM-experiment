import YangMills.Construction.FreeEnergiesOfTheFlow.FreeEnergyDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
def blockActivityTwoTori : Prop :=
  HoldsForAdmissibleParameters fun T y => ∃ nS : ℝ, 1 ≤ nS ∧ ∀ (β : ℝ) (t : ℕ),
    CouplingsAboveFloor (T.stepParameters y) β t →
    ∀ R : ℕ → StepSettings.StepSetup, (∀ s < t, IsFlowStep T y β s (R s)) →
    ∀ (n n' : ℕ) [NeZero n] [NeZero n'], TorusLumps.IsBlockTorusSide (T.stepParameters y) n →
      TorusLumps.IsBlockTorusSide (T.stepParameters y) n' → n ≤ n' →
      nS * ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β t ^ ((1 : ℝ) / 100) ≤ n → ∀ u < t,
        |blockActivityAtTrivial T.lam (R u) (WeightedResponses.fineSide T.side (t - 1 - u) n) 0 -
            blockActivityAtTrivial T.lam (R u) (WeightedResponses.fineSide T.side (t - 1 - u) n') 0| ≤
          2 * Real.exp (-(T.rt * (T.side : ℝ) ^ (t - 1 - u) * n / 2 ^ 10))
end YangMills.Construction.FreeEnergies
end
