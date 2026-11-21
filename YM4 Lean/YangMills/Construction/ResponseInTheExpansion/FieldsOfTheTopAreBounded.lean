import YangMills.Construction.ResponseInTheExpansion.ExponentIsLocal
import YangMills.Construction.ResponseInTheExpansion.KernelsAboveTheFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace WeightedResponses
def TopVariationBoundedOnParameters : Prop :=
  ∃ Z : StepParameters → ℝ, (∀ T, 0 ≤ Z T) ∧ EventuallyInParameters fun T =>
    ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top), IsAdmissibleAt T t x f F V →
      TopVariationBounded (coldHalfLawAt T x f) (Z (parametersBeforeSide T)) V
end WeightedResponses
end YangMills.Construction
end
