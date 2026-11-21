import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.TransportAtSixDerivatives
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReferenceDensity
open BlockAverages ColdStepAtMirrorFrames
def HessianDecay : Prop :=
  ∃ D : ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ, (∀ T k, 0 < D T k) ∧
    EventuallyInParameters fun T => ∀ (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (i j : ChartCoord F) (k : ℕ)
      (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → AreUnitVectors X →
      (∀ m : ℕ, ContDiffAt ℝ (m : WithTop ℕ∞) (fun σ' : Fin k → ℝ =>
        chartedHessian T.a T.ρA (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X σ') V) 0 i j) 0) ∧
      |bondDeriv (fun V' => chartedHessian T.a T.ρA V' 0 i j) V c X| ≤
        D (Interpolation.rateParameters T) k * Real.exp (-(T.chainParams.δ₂ *
          Interpolation.cellSetDiameter ({enclosingCell i.1.1.1, enclosingCell j.1.1.1} ∪ Interpolation.topBondCells c)))
end YangMills.Construction.ReferenceDensity
end
