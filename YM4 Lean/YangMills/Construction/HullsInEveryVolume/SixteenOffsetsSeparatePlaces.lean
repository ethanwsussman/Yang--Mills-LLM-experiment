import YangMills.Construction.HullsInEveryVolume.GridsOfAMirror
import YangMills.Construction.HullsInEveryVolume.HullDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ChessboardGrids
def offsetSeparationStatement : Prop :=
  HullTrees.EventuallyInParameters fun Tb _ y => ∀ (g β : ℝ) (K m : ℕ)
    (T : WeightedResponses.StageTower (Tb.stepParameters y)) (u n : ℕ) [NeZero n],
    HullTrees.HullChainAtLevel Tb y g β K m T u n →
    2 * ChessboardGrids.leastPowerAbove (Tb.stepParameters y).side (40 * HullTrees.stageRange T u) ≤ n →
    ∀ S : Finset (TorusFields.TorusSite n), HullTrees.Separated (30 * HullTrees.stageRange T u) S →
      ∃ (g : ChessboardGrids.MirrorGrid) (I : Finset (TorusFields.TorusSite n)),
        g.side = ChessboardGrids.leastPowerAbove (Tb.stepParameters y).side (40 * HullTrees.stageRange T u) ∧ I ⊆ S ∧
        (S.card : ℝ) ≤ 16 * (2 * ((Tb.stepParameters y).side : ℝ)) ^ 4 * (I.card : ℝ) ∧
        ∃ c : TorusFields.TorusSite n → Fin 4 → ℕ,
          (∀ z ∈ I, c z ∈ g.cellIndices n ∧
            HullTrees.box z (10 * HullTrees.stageRange T u) ⊆ g.cellSites n (c z)) ∧
          ∀ z ∈ I, ∀ z' ∈ I, z ≠ z' → c z ≠ c z'
end YangMills.Construction.ChessboardGrids
end
