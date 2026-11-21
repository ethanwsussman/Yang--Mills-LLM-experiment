import YangMills.Construction.ConfigurationSpace.WhitneyPiecesCubesConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
def WhitneyPieceDerivBound : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (j : ℕ) (z : IntPoint n)
    (α : MultiIdx (CoordIndex n)) (x : Config n),
    ‖configMultiDeriv α (ofRealFun (whitneyPiece j z)) x‖ ≤
      pieceDerivBound n (MultiIdx.order α) * 2 ^ (j * MultiIdx.order α)
end YangMills.Construction.ConfigurationSpace
end
