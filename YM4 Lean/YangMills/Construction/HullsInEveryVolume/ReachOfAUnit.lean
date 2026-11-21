import YangMills.Construction.HullsInEveryVolume.NoisesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
open TorusFields RenormalizationStepParameters WeightedResponses ChainNoise ChessboardGrids
def unitIndicatorLocal : Prop :=
  EventuallyInParameters fun Tb _ y => ∀ (g β : ℝ) (K m : ℕ) (T : StageTower (Tb.stepParameters y)) (u n : ℕ) [NeZero n],
    HullChainAtLevel Tb y g β K m T u n →
    ∀ rule : NoiseRule (Tb.stepParameters y), rule.IsAdmissible T → ∀ z : TorusSite n,
      DependsAbove (Tb.stepParameters y) u n (box z (7 * stageRange T u)) (unitIndicator rule T u n z) ∧
      ∀ (G : MirrorGrid) (c : Fin 4 → ℕ), box z (7 * stageRange T u) ⊆ G.cellSites n c →
        IsCellObservable (Tb.stepParameters y) G u n c (unitIndicator rule T u n z)
end YangMills.Construction.HullTrees
end
