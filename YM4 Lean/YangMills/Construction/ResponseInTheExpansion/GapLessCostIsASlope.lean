import YangMills.Construction.ResponseInTheExpansion.RadialPartIsMajorised
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages ColdStepAtMirrorFrames WeightedResponses Interpolation
def GapMinusSlopeIsRadialAt (T : ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell)
    (η : StepVariable (finiteCells F)),
    IsAdmissibleAt T t x f F V → (∀ b, ‖η b‖ < T.ballRadius) →
    (coldHalfLawAt T x f).gapTerm Y η V - (coldHalfLawAt T x f).slopeTerm Y η V =
      2 * (coldHalfLawAt T x f).linearBlockPart Y η V - (coldHalfLawAt T x f).exponentRadialPart Y η V
def GapMinusSlopeIsRadial : Prop := EventuallyInParameters GapMinusSlopeIsRadialAt
end YangMills.Construction.ResponseInTheExpansion
end
