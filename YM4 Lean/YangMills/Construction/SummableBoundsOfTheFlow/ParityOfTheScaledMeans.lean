import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.SmoothObservablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
open scoped Topology
namespace ScaledVariables
variable {F : BlockFrame}
structure ParityExpansionBounds (T : ColdStepAtMirrorFrames.StepParameters) (C K l₁ : ℝ) (f : LocalFamily)
    (law : StepLaw) (Y : F.Cell) (V : F.GaugeField F.top)
    (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) : Prop where
  iteratedDeriv_le : ∀ (i : ℕ) (l : ℝ), IsControlledOrder k i → 0 < l → l ≤ l₁ →
    |iteratedDeriv i (fun l' =>
        bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l') V c X) l| ≤
      C * K * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))
  tendsto_gaussianMean : k ≤ 3 → Filter.Tendsto
    (fun l => bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l) V c X)
    (𝓝[>] 0) (𝓝 (bondDeriv (observableGaussianMean T.a T.ρA T.lam f law Ob) V c X))
  tendsto_deriv_zero : k ≤ 3 → Filter.Tendsto
    (deriv fun l => bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l) V c X)
    (𝓝[>] 0) (𝓝 0)
  sub_gaussianMean_le : k ≤ 3 → ∀ l : ℝ, 0 < l → l ≤ l₁ →
    |bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l) V c X -
        bondDeriv (observableGaussianMean T.a T.ρA T.lam f law Ob) V c X| ≤
      C * K * l ^ 2 * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))
  secondOrderCoeff_le : k ≤ 2 →
    |bondDeriv (observableSecondOrderCoeff T.a T.ρA T.lam f law Ob) V c X| ≤
      C * K * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))
  secondOrderExpansion_le : k ≤ 2 → ∀ l : ℝ, 0 < l → l ≤ l₁ →
    |bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l) V c X -
        bondDeriv (observableGaussianMean T.a T.ρA T.lam f law Ob) V c X -
        bondDeriv (observableSecondOrderCoeff T.a T.ρA T.lam f law Ob) V c X * l ^ 2| ≤
      C * K * l ^ 3 * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))
def scaledMeanParity : Prop :=
  EventuallyOrdered fun T => ∀ e : ℕ → ℝ, ∃ l₀ C : ℝ, 0 < l₀ ∧ 0 < C ∧ ∀ l₁ : ℝ, 0 < l₁ → l₁ ≤ l₀ →
    ∀ (t : ℕ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell) (law : StepLaw) (K : ℝ)
      (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (k : ℕ)
      (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      T.IsBoundedFamilyOrderSix e t f → IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → law.IsUnitWeight → 0 ≤ K →
      IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius (2 * l₁) K Y Ob → AreUnitVectors X →
      ParityExpansionBounds T C K l₁ f law Y V Ob c X
end ScaledVariables
end YangMills.Construction
end
