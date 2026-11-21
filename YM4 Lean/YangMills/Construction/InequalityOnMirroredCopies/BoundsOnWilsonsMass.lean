import YangMills.Construction.ClusterExpansionOfAStep.TheFlowIsTheLawOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ReflectedCopies
open ClusterExpansionOfAStep
def WilsonPartitionBounds : Prop :=
  ∃ C : ℝ, ∀ β : ℝ, 1 ≤ β → ∀ (n : ℕ) [NeZero n],
    0 < wilsonPartition β n ∧ wilsonPartition β n ≤ 1 ∧
      -((C + 6 * Real.log β) * (n : ℝ) ^ 4) ≤ Real.log (wilsonPartition β n)
end ReflectedCopies
end YangMills.Construction
end
