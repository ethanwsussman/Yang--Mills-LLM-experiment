import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SummableBounds
open ColdStepAtMirrorFrames
def joinAtLoweredConstantsStatement : Prop :=
  ∀ (P R Q : StepParameters → Prop) (G : ℝ → ℝ) (K : StepParameters → ℝ),
    EventuallyInParameters P → EventuallyInParameters R →
    (∀ (T : StepParameters) (c c' : ℝ), 1 ≤ c → 1 ≤ c' → Odd T.L → 1 ≤ T.n₀ → 1 ≤ T.E → 0 < T.η₃ →
      T.η₃ ≤ 1 → G c ≤ T.Cs → K { T with Cs := c, n₀ := 0, CE := 0, coupling := 0 } ≤ T.CE →
      P { T with Cs := c, CE := c' } → R { T with Cs := c, CE := c' } → Q T) →
    EventuallyInParameters Q
end YangMills.Construction.SummableBounds
end
