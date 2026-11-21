import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Interpolation
open ColdStepAtMirrorFrames BlockAverages
def interpolatedExponentBoundsStatement : Prop :=
  EventuallyInParameters fun T => ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x →
    ∀ (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ),
    IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
    InterpolatedExponentBounds s T.a T.chainParams.ρA T.ballRadius x T.κ T.Cs (frameRadius x) V
end Interpolation
end YangMills.Construction
end
