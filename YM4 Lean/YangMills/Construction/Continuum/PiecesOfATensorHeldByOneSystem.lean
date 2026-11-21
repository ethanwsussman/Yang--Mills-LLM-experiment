import YangMills.Construction.Continuum.FlatnessAndDecayOfTheProductsWithThePieces
import YangMills.Construction.Continuum.FormsBoundedOnSeparatedBalls
import YangMills.Construction.Continuum.LocalFunctionalsOfAForm
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PieceProducts
def PieceSumOnSeparatedBoxes : Prop :=
  ∀ (n : ℕ) (C : ℝ) (m : ℕ) (R : ℝ) (B : ConfigSpace.smoothRealTupleSet n → ℝ),
    ConfigSpace.SeparatedBallBound C m R B → ∀ (P : ConfigSpace.PointSystem n)
      (f : ConfigSpace.smoothRealTupleSet n),
      P.IsSeparated → (∀ i, tsupport (f.1 i) ⊆ P.box i) →
        ∑' p : ShellPieces.activeIndices n,
            ConfigSpace.localPairing B (pieceBoxSystem p)
              (pieceMul p.1.1 p.1.2 (ConfigSpace.tensorProd f.1)) =
          (B f : ℂ)
end YangMills.Construction.PieceProducts
