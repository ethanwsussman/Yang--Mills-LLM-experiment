import YangMills.Construction.ColdStepAtMirrorFrames.TransportOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
def TransportAtScale (T : StepParameters) (ε : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (h : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate ε (ε / T.η₃) h → IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → ∀ star,
      ExpansionTransportBounds star T.a T.chainParams.ρA T.ballRadius T.decayRate ε (ε / T.η₃) T.L
        T.blockIndex (frameRadius x) h V ∧
      ∀ (F' : BlockFrame) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ),
        IsCubicTopTorus T.L t T.n₀ F' → IsSmallCurvature (5 / 4 * T.σ) V' →
        AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
        ExpansionLocalAboveFrame star T.a T.chainParams.ρA T.decayRate ε T.L (frameRadius x) h V V' Y Y' r
def transportScalingStatement : Prop :=
  ∀ T : StepParameters, 0 < T.E → 0 < T.η₃ → expansionTransportAt T → ∀ ε : ℝ, 0 < ε → TransportAtScale T ε
end Interpolation
end YangMills.Construction
end
