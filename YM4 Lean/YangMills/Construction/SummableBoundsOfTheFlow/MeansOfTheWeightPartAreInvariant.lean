import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.ComparisonBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusComparison
namespace Interpolation
def remainderMeansInvariantAt (P : StepParameters) : Prop :=
  ∀ (t : ℕ) (x s τ : ℝ) (F : BlockFrame) (V : F.GaugeField F.top), P.coupling ≤ x → 0 ≤ s → s ≤ 1 →
    IsCubicTopTorus P.L t P.n₀ F → IsSmallCurvature (5 / 4 * P.σ) V →
    (∀ (Y : F.Cell) (g : F.Cell → UnitQuaternion),
      cutoffMean P.ballRadius P.p
          (weightLawExponent s P.a P.chainParams.ρA P.chainParams.lam x (frameRadius x) τ (gaugeTransform g V))
          (cellExponentRemainder s P.a P.chainParams.ρA P.chainParams.lam x (frameRadius x) Y (gaugeTransform g V)) =
        cutoffMean P.ballRadius P.p
          (weightLawExponent s P.a P.chainParams.ρA P.chainParams.lam x (frameRadius x) τ V)
          (cellExponentRemainder s P.a P.chainParams.ρA P.chainParams.lam x (frameRadius x) Y V)) ∧
    ∀ Y h : F.Cell,
      cutoffMean P.ballRadius P.p
          (weightLawExponent s P.a P.chainParams.ρA P.chainParams.lam x (frameRadius x) τ (translateField h V))
          (cellExponentRemainder s P.a P.chainParams.ρA P.chainParams.lam x (frameRadius x) (Y + h)
            (translateField h V)) =
        cutoffMean P.ballRadius P.p
          (weightLawExponent s P.a P.chainParams.ρA P.chainParams.lam x (frameRadius x) τ V)
          (cellExponentRemainder s P.a P.chainParams.ρA P.chainParams.lam x (frameRadius x) Y V)
def remainderMeansInvariant : Prop := EventuallyInParameters remainderMeansInvariantAt
end Interpolation
end YangMills.Construction
end
