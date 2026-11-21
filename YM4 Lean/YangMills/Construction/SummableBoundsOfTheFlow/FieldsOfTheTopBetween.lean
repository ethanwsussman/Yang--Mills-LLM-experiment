import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
def topVariationAlongFields : Prop :=
  EventuallyInParameters fun T => ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ),
    IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
    TopVariationRepresentation s T.a T.chainParams.ρA T.ballRadius T.κ T.Cs (frameRadius x) V
end Interpolation
end YangMills.Construction
end
