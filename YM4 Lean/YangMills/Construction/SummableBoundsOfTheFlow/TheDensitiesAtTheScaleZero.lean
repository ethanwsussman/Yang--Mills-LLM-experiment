import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.SmoothObservablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ScaledVariables
open BlockAverages ColdStepAtMirrorFrames
def DensitiesAtScaleZero : Prop :=
  EventuallyOrdered fun T =>
    ∀ (t : ℕ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell), IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V →
      (-∫ τ in (0 : ℝ)..1, observableGaussianMean T.a T.ρA T.lam f (.interpolated τ)
          (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) V) =
        ReferenceDensity.stepDensity T.a T.ρA T.lam Y V ∧
      (∫ ν in (0 : ℝ)..1, observableGaussianMean T.a T.ρA T.lam f (.tilted ν)
          (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ) V) =
        cellCentredExpansion true T.a T.ρA 0 f Y 0 V
end YangMills.Construction.ScaledVariables
end
