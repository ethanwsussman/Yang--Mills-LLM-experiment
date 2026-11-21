import YangMills.Construction.CellOfTheFlow.MirrorCopiesOfAGrid
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps TorusFields WeightedResponses
def chessboardEstimateStatement : Prop :=
  ∀ (β : ℝ) (m : ℕ) [NeZero m] (G : CellGrid), 0 < β → G.Compatible m → Odd G.side →
    (∀ (i : Fin 4 → ℤ) (F : TorusField m → ℝ), i ∈ G.indices m → Measurable F → (∃ M, ∀ W, |F W| ≤ M) →
      DependsOnlyOn (G.cell m i) F → 0 ≤ copyProductMean G β i (G.indices m) F) ∧
    ∀ (A : Finset (Fin 4 → ℤ)) (F : (Fin 4 → ℤ) → TorusField m → ℝ), A ⊆ G.indices m →
      (∀ i ∈ A, Measurable (F i) ∧ (∃ M, ∀ W, |F i W| ≤ M) ∧ (∀ W, 0 ≤ F i W) ∧
        DependsOnlyOn (G.cell m i) (F i)) →
      ∫ W, ∏ i ∈ A, F i W ∂(wilsonLaw β m) ≤ ∏ i ∈ A, chessboardNorm G β i (F i)
end YangMills.Construction.CellWindows
end
