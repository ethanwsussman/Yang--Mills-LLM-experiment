import YangMills.Construction.ClusterExpansionOfAStep.LumpsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
def LogPartitionGapLogGrowth : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s → logPartitionGap s ≤ C * Real.log (2 + s)
end YangMills.Construction.TorusLumps
end
