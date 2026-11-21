import YangMills.Construction.Continuum.FlatnessAndDecayOfTheProductsWithThePieces
import YangMills.Construction.Continuum.FormsBoundedOnSeparatedBalls
import YangMills.Construction.Continuum.LocalFunctionalsOfAForm
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PieceTensorSum
open YangMills.Construction.ConfigSpace YangMills.Construction.PieceProducts YangMills.Construction.ShellPieces
def SumOverPiecesEqForm : Prop :=
  ∀ (n : ℕ) (c : ℝ) (a : ℕ) (G : ℝ) (T : smoothRealTupleSet n → ℝ),
    SeparatedBallBound c a G T → ∀ φ : smoothRealTupleSet n,
      ∑' p : activeIndices n,
          localPairing T (pieceBoxSystem p) (pieceMul p.1.1 p.1.2 (tensorProd φ.1)) =
        (T φ : ℂ)
end YangMills.Construction.PieceTensorSum
