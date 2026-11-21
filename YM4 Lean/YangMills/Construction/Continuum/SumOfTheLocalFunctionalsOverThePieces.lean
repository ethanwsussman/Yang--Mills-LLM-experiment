import YangMills.Construction.Continuum.ConstantOfTheExtension
import YangMills.Construction.Continuum.FlatnessAndDecayOfTheProductsWithThePieces
import YangMills.Construction.Continuum.FormsBoundedOnSeparatedBalls
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PieceLocalSum
def PieceLocalSumBound : Prop :=
  ∀ (n : ℕ) (c : ℝ) (a : ℕ) (G : ℝ) (T : ConfigSpace.smoothRealTupleSet n → ℝ),
    ConfigSpace.SeparatedBallBound c a G T → ∀ φ ∈ ConfigSpace.flatSchwartzSet n,
      ∑' p : ShellPieces.activeIndices n,
          ENNReal.ofReal ‖ConfigSpace.localPairing T (PieceProducts.pieceBoxSystem p)
            (PieceProducts.pieceMul p.1.1 p.1.2 φ)‖ ≤
        ENNReal.ofReal (ExtensionConstants.extConst n a * max 1 c ^ n * G) *
          ConfigSpace.decaySeminorm (4 * n + 2) (10 * n + a - 2) φ
end YangMills.Construction.PieceLocalSum
