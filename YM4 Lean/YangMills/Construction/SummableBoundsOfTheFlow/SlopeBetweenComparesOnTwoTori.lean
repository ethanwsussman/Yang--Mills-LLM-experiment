import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
def interpolatedSlopeLocalOnTwoTori : Prop :=
  EventuallyInParameters fun T => ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x →
    ∀ (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) (s : ℝ),
      IsCubicTopTorus T.L t T.n₀ F → IsCubicTopTorus T.L t T.n₀ F' → IsSmallCurvature (5 / 4 * T.σ) V →
      IsSmallCurvature (5 / 4 * T.σ) V' → AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r → 0 ≤ s →
      s ≤ 1 → InterpolatedSlopeLocal s T.a T.chainParams.ρA T.κ T.Ct x (frameRadius x) V V' Y Y' r
end Interpolation
end YangMills.Construction
end
