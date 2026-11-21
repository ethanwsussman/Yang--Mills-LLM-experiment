import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.RunningCouplingSlope.ColdnessTheChainReaches
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfSumsAndProductsAtATop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames Interpolation IteratedDerivative ColdChain
def contourLogDerivBoundStatement : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ D : ℕ → ℝ, (∀ k, 0 < D k) ∧
      ∀ (F : BlockFrame) (s : ℝ) (V : F.GaugeField F.top) (c₀ : F.Site F.top × Fin 4) (k : ℕ)
        (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), IsBlockTorus L F →
        IsReachableColdness c L s → IsSmallCurvature s V → 1 ≤ k → AreUnitVectors X →
        ContDiffAlongBonds k
          (fun V' => Real.log ‖BlockAverages.contourAverage (fieldAboveFrame true a c.ρA 0 V' 0) c₀‖) V e X ∧
        |bondDeriv (fun V' => Real.log ‖BlockAverages.contourAverage (fieldAboveFrame true a c.ρA 0 V' 0) c₀‖)
            V e X| ≤
          D k * Real.exp (-(c.δ₁ / 2 * cellSetDiameter ({c₀.1} ∪ topBondCells e)))
end YangMills.Construction.RunningCouplingSlope
end
