import YangMills.Construction.HullsInEveryVolume.GridsOfAMirror
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ChessboardGrids
def chessboardEstimateStatement : Prop :=
  ∀ (L M N : ℕ) [NeZero N] (β : ℝ) (g : ChessboardGrids.MirrorGrid), Odd L → 2 ^ 16 ≤ L → 2 ≤ M → 0 < β →
    N = 2 * L ^ M → ChessboardGrids.IsGridOfTorus g L M →
    (∀ F : (Fin 4 → ℕ) → TorusFields.TorusField N → ℝ,
      (∀ c ∈ g.cellIndices N, ChessboardGrids.IsCellFunction g N c (F c)) →
      ∫ W, ∏ c ∈ g.cellIndices N, F c W ∂(WeightedResponses.wilsonLaw β N) ≤
        ∏ c ∈ g.cellIndices N, g.chessboardNormAt β N c (F c)) ∧
    ∀ c ∈ g.cellIndices N, (∀ F : TorusFields.TorusField N → ℝ, ChessboardGrids.IsCellFunction g N c F →
        g.chessboardNormAt β N c F ≤ ⨆ W, F W) ∧
      g.chessboardNormAt β N c (fun _ => 1) = 1
end YangMills.Construction.ChessboardGrids
end
