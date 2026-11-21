import YangMills.Construction.HullsInEveryVolume.GridsOfAMirror
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ChessboardGrids
def evenTranslatesBoundStatement : Prop :=
  ∀ (L M N : ℕ) [NeZero N] (β : ℝ) (g : ChessboardGrids.MirrorGrid), Odd L → 2 ^ 16 ≤ L → 0 < β →
    N = 2 * L ^ M → ChessboardGrids.IsGridOfTorus g L M →
    2 * g.side ≤ N → ∀ F : TorusFields.TorusField N → ℝ, ChessboardGrids.IsCellFunction g N 0 F →
      g.chessboardNorm β N F ^ (g.cellIndices N).card ≤
        ∫ W, ∏ e ∈ g.evenTranslations N,
          F (TorusFields.translate (TorusFields.siteOfInt fun i => 2 * (g.side : ℤ) * (e i : ℤ)) W) ^ 16
          ∂(WeightedResponses.wilsonLaw β N)
end YangMills.Construction.ChessboardGrids
end
