import YangMills.Construction.ResponseInTheExpansion.ColdPartAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation WeightedResponses
namespace ResponseInTheExpansion
def ExpectationBoundedAt (T : ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top)
    (g : StepVariable (finiteCells F) → ℝ) (M : ℝ),
    IsAdmissibleAt T t x f F V →
    (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) → |g η| ≤ M) →
    |(coldHalfLawAt T x f).expectation V g| ≤ M
def expectationBoundedStatement : Prop := EventuallyInParameters ExpectationBoundedAt
end ResponseInTheExpansion
end YangMills.Construction
end
