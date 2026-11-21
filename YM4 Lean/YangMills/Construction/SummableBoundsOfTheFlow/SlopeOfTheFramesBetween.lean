import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
def interpolatedSlopeSmallOnTorus : Prop :=
  EventuallyInParameters fun T => ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ),
    IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
    InterpolatedSlopeSmall s T.a T.chainParams.ρA T.chainParams.δ₂ T.Ct (frameGapBound T (frameRadius x)) x
      (frameRadius x) V
end Interpolation
end YangMills.Construction
end
