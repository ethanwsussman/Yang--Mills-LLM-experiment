import YangMills.Construction.Cumulants.PartitionsMomentsAndTheCentredFunctionalOfAFamily
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SetPartition.SingletonSplit
noncomputable def singletonFreeProdSumOn (y : ℕ → ℝ) {k : ℕ} (I : Finset (Fin k)) : ℝ :=
  ∑ π ∈ atLeastTwoPartitions I, ∏ J ∈ π.parts, y J.card
end YangMills.Construction.SetPartition.SingletonSplit
