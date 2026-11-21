import YangMills.Construction.ConfigurationSpace.WhitneyPiecesCubesConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
def BlockProdPartitionOfUnity : Prop :=
  ∀ (n j : ℕ) (x : Config n),
    setCard {z : IntPoint n | blockProd j z x ≠ 0} ≤ 2 ^ (4 * n) ∧
    ∑' z : IntPoint n, blockProd j z x = 1
end YangMills.Construction.ConfigurationSpace
end
