import YangMills.Construction.HullsInEveryVolume.NoisesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
open TorusFields RenormalizationStepParameters WeightedResponses ChainNoise ChessboardGrids
def localHullMomentBound : Prop :=
  ∃ CE : ParameterAssignment → ℝ, EventuallyInParameters fun Tb Kr y => ∀ (g β : ℝ) (K m : ℕ)
    (T : StageTower (Tb.stepParameters y)) (u n : ℕ) [NeZero n], HullChainAtLevel Tb y g β K m T u n →
    ∀ rule : NoiseRule (Tb.stepParameters y), rule.IsAdmissible T → ∀ (z : TorusSite n) (D : ℝ) (k : ℕ), 0 < D → 1 ≤ k →
      (∀ G : MirrorGrid, G.side = leastPowerAbove (Tb.stepParameters y).side ⌈16 * D + 40 * (stageRange T u : ℝ)⌉₊ →
        2 * G.side ≤ n → ∀ c : Fin 4 → ℕ, c ∈ G.cellIndices n →
          box z (⌊2 * D⌋₊ + 6 * stageRange T u) ⊆ G.cellSites n c → ∀ M₀ : ℝ, 0 < M₀ →
          (G.atDepth (Tb.stepParameters y).side u).chessboardNormAt β (fineSide (Tb.stepParameters y).side u n) c
              (noiseExpectation (Tb.stepParameters y) u n fun p => min (localScore rule T Kr.s₁ u n z D k p) M₀) ≤
            16 ^ k * (k.factorial : ℝ) * Real.exp (CE Tb * Real.log (stageCoupling T u) * (G.side : ℝ) ^ 4)) ∧
      ∫ w, localScoreMoment T Kr.s₁ u n z D k w ∂(markedSampleLaw T β u n) ≤
        16 ^ k * (k.factorial : ℝ) * Real.exp (CE Tb * Real.log (stageCoupling T u) *
          (((Tb.stepParameters y).side : ℝ) * (16 * D + 40 * (stageRange T u : ℝ))) ^ 4)
end YangMills.Construction.HullTrees
end
