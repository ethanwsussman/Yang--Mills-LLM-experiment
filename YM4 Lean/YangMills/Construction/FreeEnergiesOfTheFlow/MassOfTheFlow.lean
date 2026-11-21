import YangMills.Construction.FreeEnergiesOfTheFlow.FreeEnergyDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
open MeasureTheory in
def flowFunctionalIntegral : Prop :=
  ∀ p : TorusLumps.StepParameters, p.Admissible → ∀ (β : ℝ) (t n : ℕ) [NeZero n],
    Measurable (ClusterExpansionOfAStep.flowFunctional p β t n) ∧ (∀ V, 0 < ClusterExpansionOfAStep.flowFunctional p β t n V) ∧
      (∃ C : ℝ, ∀ V, ClusterExpansionOfAStep.flowFunctional p β t n V ≤ C) ∧
      ∫ V, ClusterExpansionOfAStep.flowFunctional p β t n V ∂(TorusFields.fieldHaar n) = torusPartition p β t n ∧
      0 < torusPartition p β t n
end YangMills.Construction.FreeEnergies
end
