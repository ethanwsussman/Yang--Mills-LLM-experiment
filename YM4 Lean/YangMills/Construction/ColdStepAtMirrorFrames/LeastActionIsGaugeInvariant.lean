import YangMills.Construction.ColdChainAtEveryLevel.ChartsChainsAndShares
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
def MinimalActionGaugeInvariant : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (S : Finset F.Cell) (k : ℕ), k ≤ F.top → 0 < F.blockSide →
    ∀ (γ : F.Site k → UnitQuaternion) (W : F.GaugeField k),
      minimalAction a S k (gaugeTransform γ W) = minimalAction a S k W
end YangMills.Construction.ColdStepAtMirrorFrames
end
