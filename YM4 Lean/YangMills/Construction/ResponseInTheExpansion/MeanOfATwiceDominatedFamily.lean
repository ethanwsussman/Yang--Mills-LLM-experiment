import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMean
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.LinearResponse
open ColdStepAtMirrorFrames
def GibbsMeanSecondDerivative : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (k : ℕ)
    (B : Set (Fin k → ℝ)) (K : ℝ) (A H : (Fin k → ℝ) → Ω → ℝ), IsOpen B → μ ≠ 0 →
    IsDominatedSmoothFamily μ 2 B K A → IsDominatedSmoothFamily μ 2 B K H →
    ContDiffOn ℝ 2 (fun τ => gibbsMean μ (A τ) (H τ)) B ∧
      ∀ τ ∈ B, ∀ u v : Fin k → ℝ,
        iteratedFDeriv ℝ 1 (fun τ => gibbsMean μ (A τ) (H τ)) τ ![u] =
          gibbsMean μ (A τ) (paramIteratedDeriv H ![u] τ) -
            gibbsCovariance μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ) ∧
        iteratedFDeriv ℝ 2 (fun τ => gibbsMean μ (A τ) (H τ)) τ ![v, u] =
          gibbsMean μ (A τ) (paramIteratedDeriv H ![v, u] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![u] τ) (paramIteratedDeriv A ![v] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![v] τ) (paramIteratedDeriv A ![u] τ) -
            gibbsCovariance μ (A τ) (H τ) (paramIteratedDeriv A ![v, u] τ) +
            gibbsCumulantThree μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ) (paramIteratedDeriv A ![v] τ)
end YangMills.Construction.LinearResponse
end
