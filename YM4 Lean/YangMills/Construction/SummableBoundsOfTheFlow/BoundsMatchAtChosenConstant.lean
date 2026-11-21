import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace SummableBounds
open ColdStepAtMirrorFrames
def joinAtLoweredSmallnessConstantStatement : Prop :=
  ∀ (P R Q : StepParameters → Prop) (G : StepParameters → ℝ → ℝ),
    EventuallyInParameters P → EventuallyInParameters R →
    (∀ (T : StepParameters) (c : ℝ), 1 ≤ c → Odd T.L → 1 ≤ T.n₀ → 1 ≤ T.coupling → 1 ≤ T.E → 0 < T.η₃ →
      T.η₃ ≤ 1 → 0 < T.κ → 0 < T.σ → T.chainParams.Admissible T.a T.L → IsCutoff (T.σ / 64) T.p →
      G { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 } c ≤ T.Cs →
      P { T with Cs := c } → R { T with Cs := c } → Q T) →
    EventuallyInParameters Q
end SummableBounds
end YangMills.Construction
end
