import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ColdStepAtMirrorFrames
namespace Estimates
def CutoffWeightContDiff : Prop :=
  ∀ (ρ : ℝ) (p : ℝ → ℝ), 0 < ρ → IsCutoff ρ p →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun u => cutoffFactor ρ p (max u 0)
end Estimates
end YangMills.Construction
end
