import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.ObservableOfTheFrameGap
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames FamilyNorms
namespace Interpolation
def gapObservableThirdOrderBoundAt (T : StepParameters) : Prop :=
  ∀ N : ℕ, ∃ CN : ℝ, ∀ (t : ℕ) (x s : ℝ) (φ : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell)
    (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions),
    T.coupling ≤ x → 0 ≤ s → s ≤ 1 →
    IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ →
    IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → AreUnitVectors X →
    (∀ i, 4 * frameRadius x + 5 < F.extent i) →
    ∑ y' ∈ sitesOfCells (finiteCells F) F.depth,
      |ballCovariance (cutoffFactor T.ballRadius T.p)
        (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V)
        (blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Y V)
        (fun η => bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) φ y' η) V c X)| ≤
      CN * (x ^ N)⁻¹ * (T.Cs * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x))) *
        Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c))
def gapObservableThirdOrderBound : Prop := EventuallyInParameters gapObservableThirdOrderBoundAt
end Interpolation
end YangMills.Construction
end
