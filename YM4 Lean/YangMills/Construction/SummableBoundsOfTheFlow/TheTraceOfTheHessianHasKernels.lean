import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfSumsAndProductsAtATop
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReferenceDensity
def HessianTraceDecay : Prop :=
  ColdStepAtMirrorFrames.EventuallyOrdered fun T => ∃ C : ℝ, ∀ (t : ℕ) (F : BlockAverages.BlockFrame)
    (V : F.GaugeField F.top) (Y : F.Cell) (k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → BlockAverages.imaginaryQuaternions),
    ColdStepAtMirrorFrames.IsCubicTopTorus T.L t T.n₀ F →
    ColdStepAtMirrorFrames.IsSmallCurvature (5 / 4 * T.σ) V → k ≤ 6 → BlockAverages.AreUnitVectors X →
    IteratedDerivative.ContDiffAlongBonds k (fun V' => ∫ τ in (0 : ℝ)..1, hessianCellShare T.a T.ρA T.lam Y V' τ) V c X ∧
    |ColdStepAtMirrorFrames.bondDeriv (fun V' => ∫ τ in (0 : ℝ)..1, hessianCellShare T.a T.ρA T.lam Y V' τ) V c X| ≤
      C * Real.exp (-(2 ^ 7 * T.κ * Interpolation.cellSetDiameter ({Y} ∪ Interpolation.topBondCells c)))
end YangMills.Construction.ReferenceDensity
end
