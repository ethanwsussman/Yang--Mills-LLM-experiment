import YangMills.Construction.HullsInEveryVolume.NoisesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullsInEveryVolume
open TorusFields WeightedResponses RenormalizationStepParameters TorusLumps HullTrees ChainNoise ChessboardGrids
def unitProbabilityNormBoundStatement : Prop :=
  EventuallyInParameters fun Tb _ y => ∀ (g β : ℝ) (K m : ℕ) (T : StageTower (Tb.stepParameters y)) (u n : ℕ) [NeZero n],
    HullChainAtLevel Tb y g β K m T u n →
    ∀ rule : NoiseRule (Tb.stepParameters y), rule.IsAdmissible T → ∀ g : MirrorGrid,
      g.side = leastPowerAbove (Tb.stepParameters y).side (40 * stageRange T u) →
      2 * g.side ≤ n → ∀ (z : TorusSite n) (c : Fin 4 → ℕ), c ∈ g.cellIndices n →
        HullTrees.box z (7 * stageRange T u) ⊆ g.cellSites n c →
        (g.atDepth (Tb.stepParameters y).side u).chessboardNormAt β (fineSide (Tb.stepParameters y).side u n) c
            (noiseExpectation (Tb.stepParameters y) u n (unitIndicator rule T u n z)) ≤
          Real.exp (-(unitDecayRate Tb * stageCoupling T u / 32))
end YangMills.Construction.HullsInEveryVolume
end
