import YangMills.Construction.FreeEnergiesOfTheFlow.FreeEnergyDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
def scaleRate (T : RenormalizationStepParameters.ParameterAssignment) (nS : ℝ) (j : ℕ) : ℝ :=
  (T.side : ℝ) ^ (4 * j) * (2 * Real.exp (-(T.rt * (T.side : ℝ) ^ j * nS / 2 ^ 10)))
def logFlowAtTrivialTwoTori : Prop :=
  HoldsForAdmissibleParameters fun T y => ∃ nS C : ℝ, 1 ≤ nS ∧ Summable (scaleRate T nS) ∧
    ∑' j, scaleRate T nS j ≤ C ∧
    ∀ (β : ℝ) (t : ℕ), CouplingsAboveFloor (T.stepParameters y) β t →
    ∀ (n n' : ℕ) [NeZero n] [NeZero n'], TorusLumps.IsBlockTorusSide (T.stepParameters y) n →
      TorusLumps.IsBlockTorusSide (T.stepParameters y) n' → n ≤ n' →
      nS * ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β t ^ ((1 : ℝ) / 100) ≤ n →
        |Real.log (flowFunctionalAtTrivial (T.stepParameters y) β t n') -
            (n' : ℝ) ^ 4 / (n : ℝ) ^ 4 * Real.log (flowFunctionalAtTrivial (T.stepParameters y) β t n)| ≤
          (n' : ℝ) ^ 4 * ∑' j, scaleRate T nS j
end YangMills.Construction.FreeEnergies
end
