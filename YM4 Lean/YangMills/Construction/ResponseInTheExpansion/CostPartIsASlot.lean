import YangMills.Construction.ResponseInTheExpansion.DilationOfTheColdLaw
import YangMills.Construction.ResponseInTheExpansion.MeanOfASlotOfOrderTwo
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace WeightedResponses
def SlopeTermIsRemainderAt (T : StepParameters) (Cq : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell),
    IsAdmissibleAt T t x f F V → IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    IsSecondOrderRemainder T x f Cq C (C * x ^ (-(1 / 2) : ℝ)) Y ((coldHalfLawAt T x f).slopeTerm Y) V
def slopeTermRemainderStatement : Prop :=
  ∃ (Cq : StepParameters → ℕ → ℝ) (C : StepParameters → ℝ), (∀ T q, 0 ≤ Cq T q) ∧ (∀ T, 0 < C T) ∧
    EventuallyInParameters fun T =>
      SlopeTermIsRemainderAt T (Cq (parametersBeforeSide T)) (C (parametersBeforeSide T))
end WeightedResponses
end YangMills.Construction
end
