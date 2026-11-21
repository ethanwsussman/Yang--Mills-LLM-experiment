import YangMills.Construction.ConfigurationSpace.WhitneyPiecesCubesConstants
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
def WhitneyPartitionOfUnityProperty : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ x ∈ TestFunctions.injectiveTuples (Fin 4 → ℝ) n,
    setCard {p : ℕ × IntPoint n | whitneyPiece p.1 p.2 x ≠ 0} ≤ 3 * 2 ^ (4 * n) ∧
    ∑' p : pieceIndexSet n, whitneyPiece p.1.1 p.1.2 x = 1
end YangMills.Construction.ConfigurationSpace
end
