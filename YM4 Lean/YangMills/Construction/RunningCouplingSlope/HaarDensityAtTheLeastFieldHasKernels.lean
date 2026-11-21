import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.RunningCouplingSlope.ColdnessTheChainReaches
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfSumsAndProductsAtATop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames Interpolation IteratedDerivative ColdChain
def haarLogRatioDerivBoundStatement : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ D : ℕ → ℝ, (∀ k, 0 < D k) ∧
      ∀ (F : BlockFrame) (s : ℝ) (V : F.GaugeField F.top) (b₀ : ↥(chordBonds (finiteCells F))) (k : ℕ)
        (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), IsBlockTorus L F →
        IsReachableColdness c L s → IsSmallCurvature s V → 1 ≤ k → AreUnitVectors X →
        ContDiffAlongBonds k (fun V' => haarLogRatio (coordsAboveFrame true a c.ρA 0 V' 0 b₀.1.1 b₀.1.2)) V e X ∧
        |bondDeriv (fun V' => haarLogRatio (coordsAboveFrame true a c.ρA 0 V' 0 b₀.1.1 b₀.1.2)) V e X| ≤
          D k * Real.exp (-(c.δ₁ / 2 * cellSetDiameter ({enclosingCell b₀.1.1} ∪ topBondCells e)))
end YangMills.Construction.RunningCouplingSlope
end
