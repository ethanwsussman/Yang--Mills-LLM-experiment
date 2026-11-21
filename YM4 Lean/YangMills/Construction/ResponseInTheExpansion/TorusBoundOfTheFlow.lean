import YangMills.Construction.ClusterExpansionOfAStep.FlowOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.TorusLumps
def IsFirstPassage (p : StepParameters) (Ξ β : ℝ) (K : ℕ) : Prop :=
  (couplingFlow p β K).1 ≤ Ξ ∧ ∀ k < K, Ξ < (couplingFlow p β k).1
def couplingWindowTop (p : StepParameters) (g : ℝ) : ℝ := (g ^ 2)⁻¹ + 2 * p.B
end YangMills.Construction.WeightedResponses
end
