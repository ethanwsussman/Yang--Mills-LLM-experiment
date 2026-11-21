import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
structure InterpolatedFramesControlledAt (T : StepParameters) (t : ℕ) (x : ℝ) : Prop where
  single : ∀ (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ), IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
    InterpolatedFrameNearMinimizer s T.a T.chainParams.ρA T.chainParams.δ₂ (frameGapBound T (frameRadius x))
      T.σ (frameRadius x) V ∧
    InterpolatedFrameSmall s T.a T.chainParams.ρA T.chainParams.δ₂ T.Ct T.σ (frameRadius x) V
  pair : ∀ (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell)
    (Y' : F'.Cell) (r : ℕ) (s : ℝ), IsCubicTopTorus T.L t T.n₀ F → IsCubicTopTorus T.L t T.n₀ F' →
    IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r → 0 ≤ s → s ≤ 1 →
    InterpolatedFrameLocal s T.a T.chainParams.ρA T.chainParams.δ₂ T.chainParams.K T.Ct T.σ (frameRadius x)
      V V' Y Y' r
def interpolatedFramesControlled : Prop :=
  EventuallyInParameters fun T => ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFramesControlledAt T t x
end Interpolation
end YangMills.Construction
end
