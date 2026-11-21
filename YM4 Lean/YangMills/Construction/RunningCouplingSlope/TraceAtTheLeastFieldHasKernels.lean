import YangMills.Construction.RunningCouplingSlope.ColdnessTheChainReaches
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfSumsAndProductsAtATop
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def TraceKernelBounds : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdStepAtMirrorFrames.ColdChainParameters),
    1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ (F : BlockAverages.BlockFrame) (s : ℝ) (V : F.GaugeField F.top) (Y : F.Cell) (k : ℕ)
        (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → BlockAverages.imaginaryQuaternions),
        ColdStepAtMirrorFrames.IsBlockTorus L F → ColdChain.IsReachableColdness c L s →
        ColdStepAtMirrorFrames.IsSmallCurvature s V → k ≤ 6 → BlockAverages.AreUnitVectors X →
        IteratedDerivative.ContDiffAlongBonds k
          (fun V' => ∫ τ in (0 : ℝ)..1, ReferenceDensity.hessianCellShare a c.ρA c.lam Y V' τ) V e X ∧
        |ColdStepAtMirrorFrames.bondDeriv
          (fun V' => ∫ τ in (0 : ℝ)..1, ReferenceDensity.hessianCellShare a c.ρA c.lam Y V' τ) V e X| ≤
          C * Real.exp (-(r * Interpolation.cellSetDiameter ({Y} ∪ Interpolation.topBondCells e)))
end YangMills.Construction.RunningCouplingSlope
end
