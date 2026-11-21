import YangMills.Construction.Cumulants.NumberOfBlocksAndImagesOfPartitions
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SetPartition
def blockFactorialSum (q : ℕ) : ℕ :=
  ∑ π : PartitionsFin q, (blockCount π - 1).factorial
end YangMills.Construction.SetPartition
