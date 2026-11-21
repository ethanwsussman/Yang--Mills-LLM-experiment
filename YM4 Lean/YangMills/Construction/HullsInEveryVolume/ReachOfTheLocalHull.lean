import YangMills.Construction.HullsInEveryVolume.NoisesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullsInEveryVolume
open TorusFields WeightedResponses RenormalizationStepParameters TorusLumps HullTrees ChainNoise
def localHullLocalityStatement : Prop :=
  EventuallyInParameters fun Tb Kr y => ∀ (g β : ℝ) (K m : ℕ) (T : StageTower (Tb.stepParameters y)) (u n : ℕ) [NeZero n],
    HullChainAtLevel Tb y g β K m T u n →
    ∀ rule : NoiseRule (Tb.stepParameters y), rule.IsAdmissible T → ∀ (z : TorusSite n) (D : ℝ) (k : ℕ), 0 < D → 1 ≤ k →
      DependsAbove (Tb.stepParameters y) u n (HullTrees.box z (⌊2 * D⌋₊ + 6 * stageRange T u))
        (localScore rule T Kr.s₁ u n z D k) ∧
      ∀ (h : Fin 4 → ℤ) (p : TorusField (fineSide (Tb.stepParameters y).side u n) × ChainNoise.ChainNoise (Tb.stepParameters y) u n),
        localScore rule T Kr.s₁ u n z D k
            (pairTranslate (Tb.stepParameters y) u n (fun i => ((Tb.stepParameters y).side : ℤ) * h i) p) =
          localScore rule T Kr.s₁ u n (z + siteOfInt fun i => ((Tb.stepParameters y).side : ℤ) * h i) D k p
end YangMills.Construction.HullsInEveryVolume
end
