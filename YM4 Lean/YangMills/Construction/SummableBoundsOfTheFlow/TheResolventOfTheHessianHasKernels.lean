import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReferenceDensity
open BlockAverages ColdStepAtMirrorFrames
variable {F : BlockFrame}
def hessianResolvent (a ρ lam τ : ℝ) (V : F.GaugeField F.top) : Matrix (ChartCoord F) (ChartCoord F) ℝ :=
  (τ • chartedHessian a ρ V 0 + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ))⁻¹
def ResolventDecay : Prop :=
  EventuallyOrdered fun T => ∃ C : ℕ → ℝ, ∀ (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (τ : ℝ)
    (i j : ChartCoord F) (k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ τ → τ ≤ 1 → k ≤ 6 → AreUnitVectors X →
    ContDiffAt ℝ 6 (fun σ' : Fin k → ℝ =>
      hessianResolvent T.a T.ρA T.lam τ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X σ') V) i j) 0 ∧
    |bondDeriv (fun V' => hessianResolvent T.a T.ρA T.lam τ V' i j) V c X| ≤
      C k * Real.exp (-(2 ^ 8 * T.κ *
        Interpolation.cellSetDiameter ({enclosingCell i.1.1.1, enclosingCell j.1.1.1} ∪ Interpolation.topBondCells c)))
end YangMills.Construction.ReferenceDensity
end
