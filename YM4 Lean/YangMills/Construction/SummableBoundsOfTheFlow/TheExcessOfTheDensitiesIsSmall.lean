import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity
namespace StepDensities
def densityExcess (T : ColdStepAtMirrorFrames.StepParameters) (t : ℕ) (x : ℝ) (F : BlockFrame) (Y : F.Cell)
    (V : F.GaugeField F.top) : ℝ :=
  (interactionDensity true T.a T.ρA T.ballRadius T.lam x 0 T.p (T.localReference t) Y V -
      ReferenceDensity.stepDensity T.a T.ρA T.lam Y V) +
    (expansionDensity true T.a T.ρA T.ballRadius x 0 T.p (T.localReference t) Y V -
      cellCentredExpansion true T.a T.ρA 0 (T.localReference t) Y 0 V)
def densityExcessSmallStatement : Prop :=
  EventuallyOrdered fun T => T.AdmitsReference → ∃ y C : ℝ, 0 < y ∧ 0 < C ∧ ∀ (t : ℕ) (x : ℝ), y ≤ x →
    ∀ (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V →
      ContDiffThreeAlongBonds (densityExcess T t x F Y) V ∧
      ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 → AreUnitVectors X →
        |bondDeriv (densityExcess T t x F Y) V c X| ≤
          C * x⁻¹ * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))
end StepDensities
end YangMills.Construction
end
