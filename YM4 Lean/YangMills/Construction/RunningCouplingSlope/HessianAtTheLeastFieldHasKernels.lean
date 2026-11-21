import YangMills.Construction.RunningCouplingSlope.ColdnessTheChainReaches
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames Interpolation ReferenceDensity ColdChain
def hessianDerivBoundStatement : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ D : ℕ → ℝ, (∀ k, 0 < D k) ∧
      ∀ (F : BlockFrame) (s : ℝ) (V : F.GaugeField F.top) (i j : ChartCoord F) (k : ℕ)
        (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), IsBlockTorus L F →
        IsReachableColdness c L s → IsSmallCurvature s V → AreUnitVectors X →
        (∀ m : ℕ, ContDiffAt ℝ (m : WithTop ℕ∞) (fun σ' : Fin k → ℝ =>
          chartedHessian a c.ρA (leftTranslate (ColdStepAtMirrorFrames.bondSpread e X σ') V) 0 i j) 0) ∧
        |bondDeriv (fun V' => chartedHessian a c.ρA V' 0 i j) V e X| ≤
          D k * Real.exp (-(c.δ₁ / 4 *
            cellSetDiameter ({enclosingCell i.1.1.1, enclosingCell j.1.1.1} ∪ topBondCells e)))
end YangMills.Construction.RunningCouplingSlope
end
