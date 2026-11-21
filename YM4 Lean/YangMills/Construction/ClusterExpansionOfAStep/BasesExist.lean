import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
def BaseChoicesNonempty : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side → ∀ (n : ℕ) [NeZero n]
    (W : (stepBlockFrame ℓ.side n).GaugeField 0), (baseChoices ℓ W).Nonempty
end YangMills.Construction.TorusLumps
end
