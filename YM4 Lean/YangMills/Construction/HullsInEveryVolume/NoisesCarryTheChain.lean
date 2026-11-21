import YangMills.Construction.HullsInEveryVolume.NoisesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction.ChainNoise
def noiseRepresentationStatement : Prop :=
  HullTrees.EventuallyInParameters fun Tb _ y => ∀ (g β : ℝ) (K m : ℕ)
    (T : WeightedResponses.StageTower (Tb.stepParameters y)), HullTrees.HullChain Tb y g β K m T →
    (∃ rule : ChainNoise.NoiseRule (Tb.stepParameters y), rule.IsAdmissible T) ∧
    ∀ rule : ChainNoise.NoiseRule (Tb.stepParameters y), rule.IsAdmissible T →
      ∀ (u n : ℕ) [NeZero n], HullTrees.HullChainAtLevel Tb y g β K m T u n →
      ((WeightedResponses.wilsonLaw β (WeightedResponses.fineSide (Tb.stepParameters y).side u n)).prod
          (ChainNoise.chainNoiseLaw (Tb.stepParameters y) u n)).map
          (fun p => rule.chain T u n p.1 p.2) = WeightedResponses.markedSampleLaw T β u n
end YangMills.Construction.ChainNoise
end
