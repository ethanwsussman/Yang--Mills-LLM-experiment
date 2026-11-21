import YangMills.Construction.FreeEnergiesOfTheFlow.FreeEnergyDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
def logFlowAtTrivialEqSum : Prop :=
  HoldsForAdmissibleParameters fun T y => ∀ (β : ℝ) (t : ℕ), CouplingsAboveFloor (T.stepParameters y) β t →
    ∀ R : ℕ → StepSettings.StepSetup, (∀ s < t, IsFlowStep T y β s (R s)) →
    ∀ (n : ℕ) [NeZero n], TorusLumps.IsBlockTorusSide (T.stepParameters y) n →
      (∀ u < t, ∀ Y Y' : TorusFields.TorusSite (WeightedResponses.fineSide T.side (t - 1 - u) n),
        blockActivityAtTrivial T.lam (R u) (WeightedResponses.fineSide T.side (t - 1 - u) n) Y =
          blockActivityAtTrivial T.lam (R u) (WeightedResponses.fineSide T.side (t - 1 - u) n) Y') ∧
      Real.log (flowFunctionalAtTrivial (T.stepParameters y) β t n) =
        ∑ u ∈ Finset.range t, (T.side : ℝ) ^ (4 * (t - 1 - u)) * (n : ℝ) ^ 4 *
          blockActivityAtTrivial T.lam (R u) (WeightedResponses.fineSide T.side (t - 1 - u) n) 0
end YangMills.Construction.FreeEnergies
end
