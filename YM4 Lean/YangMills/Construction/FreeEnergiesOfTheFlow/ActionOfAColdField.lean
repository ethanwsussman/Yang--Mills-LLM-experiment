import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdFieldAction
open RenormalizationStepParameters TorusFields
def ColdActionBound : Prop :=
  ∀ P : ParameterAssignment, P.Admissible → ∃ C : ℝ, 0 ≤ C ∧ ∀ (t n : ℕ) [NeZero n], P.n₀ ≤ n → ∀ (s : ℝ) (A : TorusField n), 0 < s → s ≤ P.threshold →
    IsCold s A → actionAtLevel P.coupling P.side t Finset.univ A ≤ C * s ^ 2 * (n : ℝ) ^ 4
end YangMills.Construction.ColdFieldAction
end
