import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.SmoothObservablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepDensities
open BlockAverages ColdStepAtMirrorFrames ScaledVariables MeasureTheory
variable {F : BlockFrame}
structure DerivUnderWeightIntegral (M : ℝ → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) : Prop where
  contDiff : ContDiffThreeAlongBonds (fun V' => ∫ θ in (0 : ℝ)..1, M θ V') V
  integrable : IntervalIntegrable (fun θ => bondDeriv (M θ) V c X) volume 0 1
  deriv_integral_eq : bondDeriv (fun V' => ∫ θ in (0 : ℝ)..1, M θ V') V c X =
    ∫ θ in (0 : ℝ)..1, bondDeriv (M θ) V c X
def meansDifferentiableInWeightStatement : Prop :=
  EventuallyOrdered fun T => ∀ e : ℕ → ℝ, ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l₁ : ℝ, 0 < l₁ → l₁ ≤ l₀ →
    ∀ (t : ℕ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell) (kind : ℝ → StepLaw)
      (K : ℝ) (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (k : ℕ)
      (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), T.IsBoundedFamilyOrderSix e t f →
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
      (kind = StepLaw.tilted ∨ kind = StepLaw.interpolated) → 0 ≤ K →
      IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius l₁ K Y Ob → AreUnitVectors X →
      (k ≤ 3 → (∀ l : ℝ, 0 < l → l ≤ l₁ → DerivUnderWeightIntegral
          (fun θ => observableMean T.a T.ρA T.ballRadius T.lam T.p f (kind θ) Ob l) V c X) ∧
        DerivUnderWeightIntegral (fun θ => observableGaussianMean T.a T.ρA T.lam f (kind θ) Ob) V c X) ∧
      (k ≤ 2 → DerivUnderWeightIntegral
        (fun θ => observableSecondOrderCoeff T.a T.ρA T.lam f (kind θ) Ob) V c X)
end YangMills.Construction.StepDensities
end
