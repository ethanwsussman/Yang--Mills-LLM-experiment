import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
def AveragedKernelIntegralOne : Prop :=
  ∀ (p : StepParameters), p.Admissible → 11 * 2 ^ 12 * p.baseDepth < p.side → ∀ (x : ℝ) (n : ℕ) [NeZero n]
    (W : (stepBlockFrame p.side n).GaugeField 0),
    ∫ V : TorusField n, averagedKernel p x W (readAtLevel (stepBlockFrame p.side n) 1 V) ∂(fieldHaar n) = 1
end YangMills.Construction.TorusLumps
end
