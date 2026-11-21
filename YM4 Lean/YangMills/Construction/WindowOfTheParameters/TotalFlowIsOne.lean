import YangMills.Construction.WindowOfTheParameters.FlowOfTheTotalDensities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensityFlow
open TorusLumps
def FlowIsUnique : Prop :=
  ∀ (p : StepParameters) (β : ℝ) (t : ℕ) (x : ℕ → ℝ), 2 ≤ p.side → IsFlowUpTo p β t x →
    IsDefinedUpTo p β t ∧ ∀ k ≤ t, x k = coupling p β k
end YangMills.Construction.TotalDensityFlow
end
