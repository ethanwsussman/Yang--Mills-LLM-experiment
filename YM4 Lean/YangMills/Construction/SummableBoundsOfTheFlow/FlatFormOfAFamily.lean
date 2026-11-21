import YangMills.Construction.ColdStepAtMirrorFrames.StepDensityAndItsFrame
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Interpolation
open BlockAverages ColdStepAtMirrorFrames
def FlatLimitOfFamilyAt (P : StepParameters) : Prop :=
  ∀ (t : ℕ) (x ε : ℝ) (h : LocalFamily), P.coupling ≤ x → 0 < ε →
    IsRegularFamily P.L t P.n₀ P.σ P.decayRate ε (ε / P.η₃) h →
    HasBoundedFlatLimitForm P.L t (expansionAtFrameFamily P true x h) 0 ∧
    HasBoundedFlatLimitForm P.L t (expansionAtFrameFamily P false x h)
      (P.CE * ε * Real.exp (-(P.chainParams.δ₂ / 4 * frameRadius x)))
def flatLimitOfFamilyStatement : Prop := EventuallyInParameters FlatLimitOfFamilyAt
end YangMills.Construction.Interpolation
end
