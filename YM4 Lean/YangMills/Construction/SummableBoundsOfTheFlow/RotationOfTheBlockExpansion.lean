import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionUnderAGaugeOfTheTopForm
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.ColdStepAtMirrorFrames.ResponsesNearAFlatTop
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace BlockMeans
def interpolatedBlockExpansionGaugeCovariance : Prop :=
  EventuallyInParameters fun T => ∀ (x : ℝ) (t k : ℕ) (e : ℕ → ℝ) (f : LocalFamily) (F : BlockFrame)
    (V : F.GaugeField F.top) (s : ℝ)
    (η : StepVariable (finiteCells F)) (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (γ : F.Cell → UnitQuaternion), T.coupling ≤ x → HasBoundedDerivatives T.L t T.n₀ T.σ T.decayRate k e f →
    IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 → (∀ b, ‖η b‖ ≤ T.ballRadius) →
    IsSmallCurvature (5 / 4 * T.σ) (gaugeTransform γ V) ∧
    (∀ R : ℕ, (∀ i, 2 * R + 2 < F.extent i) →
      IsNearUniformAbout (5 / 4 * T.σ) R (gaugeTransform (axialGaugeHolonomy V Y) V) Y) ∧
    bondDeriv (interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) f Y η) V c X =
      bondDeriv (interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) f Y (adjointStepVariable γ η))
        (gaugeTransform γ V) c
        fun l => adjointAction (γ (c l).1) (X l)
end BlockMeans
end YangMills.Construction
end
