import YangMills.Construction.RunningCouplingSlope.ColdnessTheChainReaches
import YangMills.Construction.SummableBoundsOfTheFlow.TheResolventOfTheHessianHasKernels
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.ColdChain
namespace YangMills.Construction.RunningCouplingSlope
def MinimizerResolventDecay : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ (r : ℝ) (C : ℕ → ℝ), 0 < r ∧ (∀ k, 0 < C k) ∧
      (∀ (F : BlockFrame) (s : ℝ) (V : F.GaugeField F.top) (τ : ℝ), IsBlockTorus L F → IsReachableColdness c L s →
        IsSmallCurvature s V → 0 ≤ τ → τ ≤ 1 →
        (τ • ReferenceDensity.chartedHessian a c.ρA V 0 + (1 - τ) • c.lam •
          (1 : Matrix (ReferenceDensity.ChartCoord F) (ReferenceDensity.ChartCoord F) ℝ)).det ≠ 0) ∧
      ∀ (F : BlockFrame) (s : ℝ) (V : F.GaugeField F.top) (τ : ℝ) (i j : ReferenceDensity.ChartCoord F) (k : ℕ)
        (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), IsBlockTorus L F →
        IsReachableColdness c L s → IsSmallCurvature s V → 0 ≤ τ → τ ≤ 1 → k ≤ 6 → AreUnitVectors X →
        ContDiffAt ℝ 6 (fun σ' : Fin k → ℝ =>
          ReferenceDensity.hessianResolvent a c.ρA c.lam τ (leftTranslate (ColdStepAtMirrorFrames.bondSpread e X σ') V) i j) 0 ∧
        |bondDeriv (fun V' => ReferenceDensity.hessianResolvent a c.ρA c.lam τ V' i j) V e X| ≤
          C k * Real.exp (-(r * cellSetDiameter ({enclosingCell i.1.1.1, enclosingCell j.1.1.1} ∪ topBondCells e)))
end YangMills.Construction.RunningCouplingSlope
end
