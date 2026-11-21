import YangMills.Construction.ColdStepAtMirrorFrames.DensityHypothesesAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def InteractionDensityEstimatesAt (T : StepParameters) : Prop :=
  T.ForAllSteps fun t x f => ∀ F, IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
    IsSmallCurvature (5 / 4 * T.σ) V →
    |T.interactionFamily x f F Y V| ≤ T.Cs ∧
      (∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
        AreUnitVectors X →
        |bondDeriv (T.interactionFamily x f F Y) V c X| ≤ T.Cs * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))) ∧
      IntervalIntegrable (fun v => cutoffMean T.ballRadius T.p
        (fun η => v * stepExponent false T.a T.chainParams.ρA x (frameRadius x) f 0 V η +
          (1 - v) * totalQuadratic T.chainParams.lam x η)
        (fun η => cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y V η -
          cellQuadratic T.chainParams.lam x Y η)) MeasureTheory.volume 0 1
def interactionDensityOnTorusStatement : Prop := EventuallyInParameters InteractionDensityEstimatesAt
end YangMills.Construction.ColdStepAtMirrorFrames
end
