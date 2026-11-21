import YangMills.Construction.ColdStepAtMirrorFrames.BirthsAlongTwoSegments
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction
namespace GibbsInterpolation
def interpolatedGibbsMean {ι : Type} {k : ℕ} (μ : Measure (BondField ι))
    (A R H : (Fin k → ℝ) × BondField ι → ℝ) (v : ℝ) (τ : Fin k → ℝ) : ℝ :=
  gibbsMean μ (fun η => A (τ, η) - v * R (τ, η)) fun η => H (τ, η)
def InterpolatedGibbsMeanSmooth : Prop :=
  ∀ (ι : Type) [Fintype ι] (k : ℕ) (ρ : ℝ) (μ : Measure (BondField ι)) [IsFiniteMeasure μ]
    (A R H : (Fin k → ℝ) × BondField ι → ℝ), μ ≠ 0 → (∀ᵐ η ∂μ, ∀ b, ‖η b‖ ≤ ρ) →
    (∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ 3 A (0, η) ∧ ContDiffAt ℝ 3 R (0, η) ∧ ContDiffAt ℝ 3 H (0, η)) →
    (∀ v ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 (interpolatedGibbsMean μ A R H v) 0) ∧
      ContDiffAt ℝ 3 (fun τ => ∫ v in (0 : ℝ)..1, interpolatedGibbsMean μ A R H v τ) 0 ∧
      ∀ j, j ≤ 3 → ∀ w : Fin j → Fin k → ℝ,
        ContinuousOn (fun v => iteratedFDeriv ℝ j (interpolatedGibbsMean μ A R H v) 0 w) (Set.Icc (0 : ℝ) 1) ∧
        iteratedFDeriv ℝ j (fun τ => ∫ v in (0 : ℝ)..1, interpolatedGibbsMean μ A R H v τ) 0 w =
          ∫ v in (0 : ℝ)..1, iteratedFDeriv ℝ j (interpolatedGibbsMean μ A R H v) 0 w
end GibbsInterpolation
end YangMills.Construction
end
