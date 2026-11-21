import YangMills.Construction.Cumulants.FactorialSumOverThePartitions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CouplingFlow
def FactorialSumBound : Prop :=
  ∀ n : ℕ, 1 ≤ n → YangMills.Construction.SetPartition.blockFactorialSum n ≤ n.factorial * 2 ^ (n - 1)
end YangMills.Construction.CouplingFlow
end
