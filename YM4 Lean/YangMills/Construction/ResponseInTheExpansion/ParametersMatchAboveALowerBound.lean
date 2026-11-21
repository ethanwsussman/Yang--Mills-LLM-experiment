import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open ColdStepAtMirrorFrames
namespace ParameterAssignments
def EventuallyOfJoinWithCouplingFloor : Prop :=
  ∀ (P R Q : StepParameters → Prop) (G : ℝ → ℝ) (K Yf : StepParameters → ℝ),
    EventuallyInParameters P → EventuallyInParameters R →
    (∀ (T : StepParameters) (c c' : ℝ), 1 ≤ c → 1 ≤ c' → Odd T.L → 1 ≤ T.n₀ → 1 ≤ T.E → 0 < T.η₃ →
      T.η₃ ≤ 1 → G c ≤ T.Cs → K { T with Cs := c, n₀ := 0, CE := 0, coupling := 0 } ≤ T.CE →
      Yf { T with Cs := c, coupling := 0 } ≤ T.coupling → P { T with Cs := c, CE := c' } →
      R { T with Cs := c, CE := c' } → Q T) →
    EventuallyInParameters Q
end ParameterAssignments
end YangMills.Construction
