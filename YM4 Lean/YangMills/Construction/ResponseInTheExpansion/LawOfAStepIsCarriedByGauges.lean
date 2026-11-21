import YangMills.Construction.ColdStepAtMirrorFrames.DensityHypothesesAtParameters
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionUnderAGaugeOfTheTopForm
import YangMills.Construction.ResponseInTheExpansion.FramesMoveWithTheTop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace ResponseInTheExpansion
def GaugeInvarianceOfStepLawAt (T : StepParameters) : Prop :=
  T.ForAllSteps fun t x f => ∀ F, IsCubicTopTorus T.L t T.n₀ F → ∀ V : F.GaugeField F.top,
    IsSmallCurvature (5 / 4 * T.σ) V →
    ∀ (γ : F.Cell → UnitQuaternion) (H : StepVariable (finiteCells F) → ℝ),
      cutoffMean T.ballRadius T.p (stepExponent false T.a T.chainParams.ρA x (frameRadius x) f 1 (gaugeTransform γ V)) H =
        cutoffMean T.ballRadius T.p (stepExponent false T.a T.chainParams.ρA x (frameRadius x) f 1 V)
          fun η => H (adjointStepVariable γ η)
def stepLawGaugeInvariantStatement : Prop :=
  ∀ T : StepParameters, Odd T.L → 2 ≤ T.n₀ → 0 < T.σ → FramesEquivariantAt T → GaugeInvarianceOfStepLawAt T
end ResponseInTheExpansion
end YangMills.Construction
end
