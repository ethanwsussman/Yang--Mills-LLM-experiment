import YangMills.Construction.ColdStepAtMirrorFrames.StepDensityAndItsFrame
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
open BlockAverages
def StepDensityIsLocal (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    IsLocalOnTori T.L t T.n₀ (9 / 8 * T.σ) (centredFamily (stepDensityFamily T x f)) fun r =>
      2⁻¹ ^ 4 * T.E / torusDecayFactor T.L T.decayRate r
def stepDensityIsLocalStatement : Prop := EventuallyInParameters StepDensityIsLocal
end ColdStepAtMirrorFrames
end YangMills.Construction
end
