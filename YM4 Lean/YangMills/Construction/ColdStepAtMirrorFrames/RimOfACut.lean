import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def CutoffFactorIsRadialCutoff : Prop :=
  ∀ (ρ : ℝ) (p : ℝ → ℝ), 0 < ρ → IsCutoff ρ p → IsRadialCutoff ρ fun u => cutoffFactor ρ p (max u 0)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
