import YangMills.Construction.Continuum.FlatnessAndDecayOfTheProductsWithThePieces
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PieceProducts
def PieceMulSummableSeminorms : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ f ∈ ConfigSpace.flatSchwartzSet n, ∀ k l : ℕ,
    ∑' p : ShellPieces.activeIndices n,
      ConfigSpace.decaySeminorm k l (pieceMul p.1.1 p.1.2 f) < ⊤
end YangMills.Construction.PieceProducts
end
