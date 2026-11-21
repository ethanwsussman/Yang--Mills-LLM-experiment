import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.SmoothObservablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.StepDensities
open BlockAverages ColdStepAtMirrorFrames ScaledVariables
variable {F : BlockFrame}
structure ScaledMeanDerivBounds (T : StepParameters) (C K l₁ : ℝ) (f : LocalFamily) (law : StepLaw) (Y : F.Cell)
    (V : F.GaugeField F.top) (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) : Prop where
  contDiffAt : k ≤ 3 → ∀ l : ℝ, 0 < l → l ≤ l₁ → ContDiffAt ℝ (if k = 3 then 2 else 3)
    (fun l' => bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l') V c X) l
  iteratedDeriv_le : ∀ (i : ℕ) (l : ℝ), IsControlledOrder k i → 0 < l → l ≤ l₁ →
    |iteratedDeriv i (fun l' => bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l') V c X) l| ≤
      C * K * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))
  tendsto_gaussianMean : k ≤ 3 → Filter.Tendsto
    (fun l => bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l) V c X)
    (𝓝[>] 0) (𝓝 (bondDeriv (observableGaussianMean T.a T.ρA T.lam f law Ob) V c X))
  tendsto_deriv_zero : k ≤ 3 → Filter.Tendsto
    (deriv fun l => bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l) V c X)
    (𝓝[>] 0) (𝓝 0)
  tendsto_secondDeriv : k ≤ 2 → Filter.Tendsto
    (iteratedDeriv 2 fun l => bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l) V c X)
    (𝓝[>] 0) (𝓝 (2 * bondDeriv (observableSecondOrderCoeff T.a T.ρA T.lam f law Ob) V c X))
def scaledMeanDerivStatement : Prop :=
  EventuallyOrdered fun T => ∀ e : ℕ → ℝ, ∃ l₀ C : ℝ, 0 < l₀ ∧ 0 < C ∧ ∀ l₁ : ℝ, 0 < l₁ → l₁ ≤ l₀ →
    ∀ (t : ℕ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell) (law : StepLaw) (K : ℝ)
      (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions), T.IsBoundedFamilyOrderSix e t f → IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → StepLaw.IsUnitWeight law → 0 ≤ K →
      IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius (2 * l₁) K Y Ob → AreUnitVectors X →
      ScaledMeanDerivBounds T C K l₁ f law Y V Ob c X
end YangMills.Construction.StepDensities
end
