import YangMills.Construction.ConfigurationSpace.WhitneyPiecesCubesConstants
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
open BumpFunctions
def WhitneyCubeBoxBounds : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ p ∈ pieceIndexSet n,
    (∀ i : Fin n, outerCube p.1 p.2 i ⊆
      TestFunctions.closedBallR4 (pieceCenter p.1 p.2 i) (2 * WhitneyScales.whitneySide p.1)) ∧
    2 * WhitneyScales.whitneySide p.1 ≤ 1 ∧
    (∀ i i' : Fin n, i ≠ i' →
      ENNReal.ofReal (WhitneyScales.whitneyScale p.1 / 2) ≤
        TestFunctions.setDistR4 (outerCube p.1 p.2 i) (outerCube p.1 p.2 i')) ∧
    (1 ≤ p.1 → ∀ x ∈ pieceBox p.1 p.2,
      minSeparation x ≤ ENNReal.ofReal (separationConst * WhitneyScales.whitneyScale p.1) ∧
      ∃ y ∈ fatDiagonal n, configNorm (x - y) ≤ diagonalDistConst * WhitneyScales.whitneyScale p.1) ∧
    ∀ x ∈ pieceBox p.1 p.2,
      configNorm (x - pieceCenter p.1 p.2) ≤ Real.sqrt n ∧
      1 + configNorm (pieceCenter p.1 p.2) ≤ (1 + Real.sqrt n) * (1 + configNorm x) ∧
      1 + configNorm x ≤ (1 + Real.sqrt n) * (1 + configNorm (pieceCenter p.1 p.2))
end YangMills.Construction.ConfigurationSpace
end
