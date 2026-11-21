import YangMills.Construction.HullsInEveryVolume.NoisesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
def hullTranslationStatement : Prop :=
  HullTrees.EventuallyInParameters fun T _ y => ∀ (g β : ℝ) (K m : ℕ)
    (S : WeightedResponses.StageTower (T.stepParameters y)) (u n : ℕ) [NeZero n],
    HullTrees.HullChainAtLevel T y g β K m S u n →
    ∀ rule : ChainNoise.NoiseRule (T.stepParameters y), rule.IsAdmissible S →
      ∀ (z : TorusFields.TorusSite n) (w : Fin 4 → ℤ)
      (p : TorusFields.TorusField (WeightedResponses.fineSide (T.stepParameters y).side u n) ×
        ChainNoise.ChainNoise (T.stepParameters y) u n),
      z ∈ HullTrees.hullSet S u n (rule.chain S u n
          (ChainNoise.pairTranslate (T.stepParameters y) u n
            (fun i => ((T.stepParameters y).side : ℤ) * w i) p).1
          (ChainNoise.pairTranslate (T.stepParameters y) u n
            (fun i => ((T.stepParameters y).side : ℤ) * w i) p).2) ↔
        z + TorusFields.siteOfInt (fun i => ((T.stepParameters y).side : ℤ) * w i) ∈
          HullTrees.hullSet S u n (rule.chain S u n p.1 p.2)
end YangMills.Construction.MomentLaw
end
