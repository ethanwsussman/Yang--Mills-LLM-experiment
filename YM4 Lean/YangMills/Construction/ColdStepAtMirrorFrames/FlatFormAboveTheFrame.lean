import YangMills.Construction.ColdStepAtMirrorFrames.StepDensityAndItsFrame
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open BlockAverages
def FlatLimitAboveFrame (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    HasBoundedFlatLimitForm T.L t (expansionAtFrameFamily T true x f) 0 ∧
    HasBoundedFlatLimitForm T.L t (expansionAtFrameFamily T false x f)
      (T.CE * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x)))
def flatLimitAboveFrameStatement : Prop := EventuallyInParameters FlatLimitAboveFrame
end YangMills.Construction.ColdStepAtMirrorFrames
end
