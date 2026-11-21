import YangMills.Construction.Continuum.FlatnessAndDecayOfTheProductsWithThePieces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
open YangMills.Construction.PieceProducts YangMills.Construction.ShellPieces
def pieceMul_mem_closure_tensorSpan : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (j : ℕ) (z : LatticePt n), (j, z) ∈ activeIndices n →
    ∀ f ∈ flatSchwartzSet n, ∀ (k l : ℕ) (ε : ℝ), 0 < ε →
      ∃ g ∈ Submodule.span ℂ (tensorProd '' smoothRealTupleSet n),
        decaySeminorm k l (pieceMul j z f - g) < ENNReal.ofReal ε
end YangMills.Construction.ConfigSpace
end
