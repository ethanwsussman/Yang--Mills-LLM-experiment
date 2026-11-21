import YangMills.Construction.ConfigurationSpace.WhitneyPiecesCubesConstants
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
open WhitneyScales
def WhitneyPieceSupportProperties : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (j : ℕ) (z : IntPoint n),
    ofRealFun (whitneyPiece j z) ∈ testFunctionSet (Config n) ∧
    (∀ x : Config n, 0 ≤ whitneyPiece j z x ∧ whitneyPiece j z x ≤ 1) ∧
    tsupport (whitneyPiece j z) ⊆ translateSet (pieceCenter j z)
      {x | ∀ ι, coords x ι ∈ Set.Icc (-(3 / 8 * whitneySide j)) (3 / 8 * whitneySide j)} ∧
    translateSet (pieceCenter j z)
      {x | ∀ ι, coords x ι ∈ Set.Icc (-(3 / 8 * whitneySide j)) (3 / 8 * whitneySide j)} ⊆
      pieceBox j z ∧
    pieceBox j z ⊆ boxProduct (innerCube j z) ∧
    IsCompact (tsupport (whitneyPiece j z)) ∧
    tsupport (whitneyPiece j z) ⊆ TestFunctions.injectiveTuples (Fin 4 → ℝ) n
end YangMills.Construction.ConfigurationSpace
end
