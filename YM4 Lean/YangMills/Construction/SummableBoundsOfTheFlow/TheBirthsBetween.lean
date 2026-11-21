import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.ComparisonBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusComparison
namespace Interpolation
def interpolatedBirth (s a ρA ρ lam x : ℝ) (m : ℕ) (p : ℝ → ℝ) : TopLevelFamily :=
  fun _ Y V => -∫ τ in (0 : ℝ)..1, cutoffMean ρ p (weightLawExponent s a ρA lam x m τ V)
    (cellExponentRemainder s a ρA lam x m Y V)
def interpolatedBirthAt (P : StepParameters) (x s : ℝ) : TopLevelFamily :=
  interpolatedBirth s P.a P.chainParams.ρA P.ballRadius P.chainParams.lam x (frameRadius x) P.p
structure InterpolatedBirthBounds (P : StepParameters) (t : ℕ) (x s : ℝ) : Prop where
  integrable : ∀ F, IsCubicTopTorus P.L t P.n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
    IsSmallCurvature (5 / 4 * P.σ) V →
    IntervalIntegrable (fun τ => cutoffMean P.ballRadius P.p
      (weightLawExponent s P.a P.chainParams.ρA P.chainParams.lam x (frameRadius x) τ V)
      (cellExponentRemainder s P.a P.chainParams.ρA P.chainParams.lam x (frameRadius x) Y V))
      MeasureTheory.volume 0 1
  isLocalDensity : IsLocalDensity P.L t P.n₀ (5 / 4 * P.σ) (interpolatedBirthAt P x s)
  abs_le : ∀ F, IsCubicTopTorus P.L t P.n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
    IsSmallCurvature (5 / 4 * P.σ) V → |interpolatedBirthAt P x s F Y V| ≤ P.Cs
  decay : DerivDecay P.L t P.n₀ (5 / 4 * P.σ) (interpolatedBirthAt P x s)
    fun _ n => P.Cs * Real.exp (-(P.κ / 2 ^ 6 * n))
  isLocalOnTori : IsLocalOnTori P.L t P.n₀ (9 / 8 * P.σ) (interpolatedBirthAt P x s)
    fun r => P.Cs * Real.exp (-(P.κ / 2 ^ 9 * r))
def interpolatedBirthBoundsStatement : Prop :=
  EventuallyInParameters fun P => ∀ (t : ℕ) (x s : ℝ), P.coupling ≤ x → 0 ≤ s → s ≤ 1 →
    InterpolatedBirthBounds P t x s
end Interpolation
end YangMills.Construction
end
