import YangMills.Construction.CellOfTheFlow.NoiseOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps WeightedResponses
def samplerExistsStatement : Prop :=
  ∀ (q : StepParameters), q.Admissible → ∀ T : StageTower q, ∃ S : ChainSampler T, ∀ s, (S s).IsFaithful
end YangMills.Construction.CellWindows
end
