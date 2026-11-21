import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMean
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.TiltedMeans
open ColdStepAtMirrorFrames
variable {Ω : Type} [MeasurableSpace Ω] {k : ℕ}
def tiltedMean (ν μ : Measure Ω) (A f : Ω → ℝ) : ℝ :=
  (∫ ω, f ω * Real.exp (- A ω) ∂ν) / ∫ ω, Real.exp (- A ω) ∂μ
def tiltedCov (ν μ : Measure Ω) (A f g : Ω → ℝ) : ℝ :=
  tiltedMean ν μ A (fun ω => f ω * g ω) - tiltedMean ν μ A f * gibbsMean μ A g
def tiltedCumulantThree (ν μ : Measure Ω) (A f g h : Ω → ℝ) : ℝ :=
  tiltedMean ν μ A (fun ω => f ω * g ω * h ω) -
    tiltedMean ν μ A (fun ω => f ω * g ω) * gibbsMean μ A h -
    tiltedMean ν μ A (fun ω => f ω * h ω) * gibbsMean μ A g -
    gibbsMean μ A (fun ω => g ω * h ω) * tiltedMean ν μ A f +
    2 * (tiltedMean ν μ A f * gibbsMean μ A g * gibbsMean μ A h)
def tiltedCumulantFour (ν μ : Measure Ω) (A f g h l : Ω → ℝ) : ℝ :=
  tiltedMean ν μ A (fun ω => f ω * g ω * h ω * l ω) -
    tiltedMean ν μ A (fun ω => f ω * g ω * h ω) * gibbsMean μ A l -
    tiltedMean ν μ A (fun ω => f ω * g ω * l ω) * gibbsMean μ A h -
    tiltedMean ν μ A (fun ω => f ω * h ω * l ω) * gibbsMean μ A g -
    gibbsMean μ A (fun ω => g ω * h ω * l ω) * tiltedMean ν μ A f -
    tiltedMean ν μ A (fun ω => f ω * g ω) * gibbsMean μ A (fun ω => h ω * l ω) -
    tiltedMean ν μ A (fun ω => f ω * h ω) * gibbsMean μ A (fun ω => g ω * l ω) -
    tiltedMean ν μ A (fun ω => f ω * l ω) * gibbsMean μ A (fun ω => g ω * h ω) +
    2 * (tiltedMean ν μ A (fun ω => f ω * g ω) * gibbsMean μ A h * gibbsMean μ A l +
      tiltedMean ν μ A (fun ω => f ω * h ω) * gibbsMean μ A g * gibbsMean μ A l +
      tiltedMean ν μ A (fun ω => f ω * l ω) * gibbsMean μ A g * gibbsMean μ A h +
      gibbsMean μ A (fun ω => g ω * h ω) * tiltedMean ν μ A f * gibbsMean μ A l +
      gibbsMean μ A (fun ω => g ω * l ω) * tiltedMean ν μ A f * gibbsMean μ A h +
      gibbsMean μ A (fun ω => h ω * l ω) * tiltedMean ν μ A f * gibbsMean μ A g) -
    6 * (tiltedMean ν μ A f * gibbsMean μ A g * gibbsMean μ A h * gibbsMean μ A l)
def TiltedMeanDifferentiation : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ν μ : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure μ] (k : ℕ)
    (U : Set (Fin k → ℝ)) (C : ℝ) (A H : (Fin k → ℝ) → Ω → ℝ), IsOpen U → μ ≠ 0 → ν ≪ μ →
    IsDominatedSmoothFamily μ 3 U C A → IsDominatedSmoothFamily μ 3 U C H →
    ContDiffOn ℝ 3 (fun τ => tiltedMean ν μ (A τ) (H τ)) U ∧
      ∀ τ ∈ U, ∀ u v w : Fin k → ℝ,
        iteratedFDeriv ℝ 1 (fun τ => tiltedMean ν μ (A τ) (H τ)) τ ![u] =
          tiltedMean ν μ (A τ) (paramIteratedDeriv H ![u] τ) -
            tiltedCov ν μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ) ∧
        iteratedFDeriv ℝ 2 (fun τ => tiltedMean ν μ (A τ) (H τ)) τ ![v, u] =
          tiltedMean ν μ (A τ) (paramIteratedDeriv H ![v, u] τ) -
            tiltedCov ν μ (A τ) (paramIteratedDeriv H ![u] τ) (paramIteratedDeriv A ![v] τ) -
            tiltedCov ν μ (A τ) (paramIteratedDeriv H ![v] τ) (paramIteratedDeriv A ![u] τ) -
            tiltedCov ν μ (A τ) (H τ) (paramIteratedDeriv A ![v, u] τ) +
            tiltedCumulantThree ν μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ)
              (paramIteratedDeriv A ![v] τ) ∧
        iteratedFDeriv ℝ 3 (fun τ => tiltedMean ν μ (A τ) (H τ)) τ ![w, v, u] =
          tiltedMean ν μ (A τ) (paramIteratedDeriv H ![w, v, u] τ) -
            tiltedCov ν μ (A τ) (paramIteratedDeriv H ![v, u] τ) (paramIteratedDeriv A ![w] τ) -
            tiltedCov ν μ (A τ) (paramIteratedDeriv H ![w, u] τ) (paramIteratedDeriv A ![v] τ) -
            tiltedCov ν μ (A τ) (paramIteratedDeriv H ![w, v] τ) (paramIteratedDeriv A ![u] τ) -
            tiltedCov ν μ (A τ) (paramIteratedDeriv H ![u] τ) (paramIteratedDeriv A ![w, v] τ) -
            tiltedCov ν μ (A τ) (paramIteratedDeriv H ![v] τ) (paramIteratedDeriv A ![w, u] τ) -
            tiltedCov ν μ (A τ) (paramIteratedDeriv H ![w] τ) (paramIteratedDeriv A ![v, u] τ) +
            tiltedCumulantThree ν μ (A τ) (paramIteratedDeriv H ![u] τ) (paramIteratedDeriv A ![v] τ)
              (paramIteratedDeriv A ![w] τ) +
            tiltedCumulantThree ν μ (A τ) (paramIteratedDeriv H ![v] τ) (paramIteratedDeriv A ![u] τ)
              (paramIteratedDeriv A ![w] τ) +
            tiltedCumulantThree ν μ (A τ) (paramIteratedDeriv H ![w] τ) (paramIteratedDeriv A ![u] τ)
              (paramIteratedDeriv A ![v] τ) -
            tiltedCov ν μ (A τ) (H τ) (paramIteratedDeriv A ![w, v, u] τ) +
            tiltedCumulantThree ν μ (A τ) (H τ) (paramIteratedDeriv A ![v, u] τ)
              (paramIteratedDeriv A ![w] τ) +
            tiltedCumulantThree ν μ (A τ) (H τ) (paramIteratedDeriv A ![w, u] τ)
              (paramIteratedDeriv A ![v] τ) +
            tiltedCumulantThree ν μ (A τ) (H τ) (paramIteratedDeriv A ![w, v] τ)
              (paramIteratedDeriv A ![u] τ) -
            tiltedCumulantFour ν μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ)
              (paramIteratedDeriv A ![v] τ) (paramIteratedDeriv A ![w] τ)
end YangMills.Construction.TiltedMeans
end
