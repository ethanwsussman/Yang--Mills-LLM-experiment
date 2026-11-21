import YangMills.Construction.ColdStepAtMirrorFrames.StepDensityAndItsFrame
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
def StepDensityDerivBoundsAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    DerivDecay T.L t T.n₀ (5 / 4 * T.σ) (stepDensityFamily T x f) (fun k n =>
      2⁻¹ ^ 6 * (if k = 3 then T.energyRatio else T.E) / torusDecayFactor T.L T.decayRate n +
        T.CE * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 * n))) ∧
    IsLocalOnTori T.L t T.n₀ (9 / 8 * T.σ) (centredFamily (stepDensityFamily T x f)) fun r =>
      2⁻¹ ^ 4 * T.E / torusDecayFactor T.L T.decayRate r
def stepDensityDerivBoundsStatement : Prop := EventuallyInParameters StepDensityDerivBoundsAt
end ColdStepAtMirrorFrames
end YangMills.Construction
end
