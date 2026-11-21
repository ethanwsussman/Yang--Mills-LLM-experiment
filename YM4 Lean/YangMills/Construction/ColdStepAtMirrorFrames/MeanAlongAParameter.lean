import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMean
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
def IntervalIntegralGibbsMeanDifferentiation : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (k : ℕ)
    (U : Set (Fin k → ℝ)) (C : ℝ) (A H : ℝ → (Fin k → ℝ) → Ω → ℝ), IsOpen U → μ ≠ 0 →
    (∀ v ∈ Set.Icc (0 : ℝ) 1, IsDominatedSmoothFamily μ 3 U C (A v)) →
    (∀ v ∈ Set.Icc (0 : ℝ) 1, IsDominatedSmoothFamily μ 3 U C (H v)) →
    (∀ τ ∈ U, ∀ᵐ ω ∂μ, ContinuousOn (fun v => A v τ ω) (Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn (fun v => H v τ ω) (Set.Icc (0 : ℝ) 1)) →
    ContDiffOn ℝ 3 (fun τ => ∫ v in (0 : ℝ)..1, gibbsMean μ (A v τ) (H v τ)) U ∧
      ∀ τ ∈ U, ∀ j, j ≤ 3 → ∀ w : Fin j → Fin k → ℝ,
        iteratedFDeriv ℝ j (fun τ => ∫ v in (0 : ℝ)..1, gibbsMean μ (A v τ) (H v τ)) τ w =
          ∫ v in (0 : ℝ)..1, iteratedFDeriv ℝ j (fun τ => gibbsMean μ (A v τ) (H v τ)) τ w
end YangMills.Construction.ColdStepAtMirrorFrames
end
