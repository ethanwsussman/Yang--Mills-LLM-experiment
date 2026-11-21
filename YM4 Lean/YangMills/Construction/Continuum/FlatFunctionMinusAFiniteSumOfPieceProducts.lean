import YangMills.Construction.Continuum.FlatnessAndDecayOfTheProductsWithThePieces
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ConfigSpace
def FlatMinusPieceSumBound : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ f ∈ flatSchwartzSet n, ∀ k l : ℕ, ∀ F : Finset (ShellPieces.activeIndices n),
    decaySeminorm k l (f - ∑ p ∈ F, PieceProducts.pieceMul p.1.1 p.1.2 f) ≤
      ∑' p : {p : ShellPieces.activeIndices n // p ∉ F},
        decaySeminorm k l (PieceProducts.pieceMul p.1.1.1 p.1.1.2 f)
end YangMills.Construction.ConfigSpace
end
