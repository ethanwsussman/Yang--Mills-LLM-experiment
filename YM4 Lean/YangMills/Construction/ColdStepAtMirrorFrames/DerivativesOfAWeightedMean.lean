import YangMills.Construction.ColdStepAtMirrorFrames.BirthsAlongTwoSegments
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {Ω : Type} [MeasurableSpace Ω] {k : ℕ}
structure IsDominatedSmoothFamily (μ : Measure Ω) (n : ℕ) (B : Set (Fin k → ℝ)) (K : ℝ)
    (G : (Fin k → ℝ) → Ω → ℝ) : Prop where
  aestronglyMeasurable : ∀ τ ∈ B, AEStronglyMeasurable (G τ) μ
  contDiffOn : ∀ᵐ ω ∂μ, ContDiffOn ℝ n (fun τ => G τ ω) B
  norm_iteratedFDeriv_le : ∀ᵐ ω ∂μ, ∀ j, j ≤ n → ∀ τ ∈ B, ‖iteratedFDeriv ℝ j (fun τ => G τ ω) τ‖ ≤ K
def paramIteratedDeriv {j : ℕ} (G : (Fin k → ℝ) → Ω → ℝ) (v : Fin j → Fin k → ℝ) :
    (Fin k → ℝ) → Ω → ℝ :=
  fun τ ω => iteratedFDeriv ℝ j (fun τ' => G τ' ω) τ v
def gibbsCovariance (μ : Measure Ω) (A f g : Ω → ℝ) : ℝ :=
  gibbsMean μ A (fun ω => f ω * g ω) - gibbsMean μ A f * gibbsMean μ A g
def gibbsCumulantThree (μ : Measure Ω) (A f g h : Ω → ℝ) : ℝ :=
  gibbsMean μ A (fun ω => f ω * g ω * h ω) -
    gibbsMean μ A (fun ω => f ω * g ω) * gibbsMean μ A h -
    gibbsMean μ A (fun ω => f ω * h ω) * gibbsMean μ A g -
    gibbsMean μ A (fun ω => g ω * h ω) * gibbsMean μ A f +
    2 * (gibbsMean μ A f * gibbsMean μ A g * gibbsMean μ A h)
def gibbsCumulantFour (μ : Measure Ω) (A f g h l : Ω → ℝ) : ℝ :=
  gibbsMean μ A (fun ω => f ω * g ω * h ω * l ω) -
    gibbsMean μ A (fun ω => f ω * g ω * h ω) * gibbsMean μ A l -
    gibbsMean μ A (fun ω => f ω * g ω * l ω) * gibbsMean μ A h -
    gibbsMean μ A (fun ω => f ω * h ω * l ω) * gibbsMean μ A g -
    gibbsMean μ A (fun ω => g ω * h ω * l ω) * gibbsMean μ A f -
    gibbsMean μ A (fun ω => f ω * g ω) * gibbsMean μ A (fun ω => h ω * l ω) -
    gibbsMean μ A (fun ω => f ω * h ω) * gibbsMean μ A (fun ω => g ω * l ω) -
    gibbsMean μ A (fun ω => f ω * l ω) * gibbsMean μ A (fun ω => g ω * h ω) +
    2 * (gibbsMean μ A (fun ω => f ω * g ω) * gibbsMean μ A h * gibbsMean μ A l +
      gibbsMean μ A (fun ω => f ω * h ω) * gibbsMean μ A g * gibbsMean μ A l +
      gibbsMean μ A (fun ω => f ω * l ω) * gibbsMean μ A g * gibbsMean μ A h +
      gibbsMean μ A (fun ω => g ω * h ω) * gibbsMean μ A f * gibbsMean μ A l +
      gibbsMean μ A (fun ω => g ω * l ω) * gibbsMean μ A f * gibbsMean μ A h +
      gibbsMean μ A (fun ω => h ω * l ω) * gibbsMean μ A f * gibbsMean μ A g) -
    6 * (gibbsMean μ A f * gibbsMean μ A g * gibbsMean μ A h * gibbsMean μ A l)
def DifferentiationUnderIntegral : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (k n : ℕ)
    (B : Set (Fin k → ℝ)) (K : ℝ) (G : (Fin k → ℝ) → Ω → ℝ), IsOpen B →
    IsDominatedSmoothFamily μ n B K G →
    ContDiffOn ℝ n (fun τ => ∫ ω, G τ ω ∂μ) B ∧
      ∀ τ ∈ B, ∀ j, j ≤ n → ∀ v : Fin j → Fin k → ℝ,
        iteratedFDeriv ℝ j (fun τ => ∫ ω, G τ ω ∂μ) τ v = ∫ ω, paramIteratedDeriv G v τ ω ∂μ
def GibbsMeanThirdOrderExpansion : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (k : ℕ)
    (B : Set (Fin k → ℝ)) (K : ℝ) (A H : (Fin k → ℝ) → Ω → ℝ), IsOpen B → μ ≠ 0 →
    IsDominatedSmoothFamily μ 3 B K A → IsDominatedSmoothFamily μ 3 B K H →
    ContDiffOn ℝ 3 (fun τ => gibbsMean μ (A τ) (H τ)) B ∧
      ∀ τ ∈ B, ∀ u v w : Fin k → ℝ,
        iteratedFDeriv ℝ 1 (fun τ => gibbsMean μ (A τ) (H τ)) τ ![u] =
          gibbsMean μ (A τ) (paramIteratedDeriv H ![u] τ) -
            gibbsCovariance μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ) ∧
        iteratedFDeriv ℝ 2 (fun τ => gibbsMean μ (A τ) (H τ)) τ ![v, u] =
          gibbsMean μ (A τ) (paramIteratedDeriv H ![v, u] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![u] τ) (paramIteratedDeriv A ![v] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![v] τ) (paramIteratedDeriv A ![u] τ) -
            gibbsCovariance μ (A τ) (H τ) (paramIteratedDeriv A ![v, u] τ) +
            gibbsCumulantThree μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ) (paramIteratedDeriv A ![v] τ) ∧
        iteratedFDeriv ℝ 3 (fun τ => gibbsMean μ (A τ) (H τ)) τ ![w, v, u] =
          gibbsMean μ (A τ) (paramIteratedDeriv H ![w, v, u] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![v, u] τ) (paramIteratedDeriv A ![w] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![w, u] τ) (paramIteratedDeriv A ![v] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![w, v] τ) (paramIteratedDeriv A ![u] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![u] τ) (paramIteratedDeriv A ![w, v] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![v] τ) (paramIteratedDeriv A ![w, u] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![w] τ) (paramIteratedDeriv A ![v, u] τ) +
            gibbsCumulantThree μ (A τ) (paramIteratedDeriv H ![u] τ) (paramIteratedDeriv A ![v] τ)
              (paramIteratedDeriv A ![w] τ) +
            gibbsCumulantThree μ (A τ) (paramIteratedDeriv H ![v] τ) (paramIteratedDeriv A ![u] τ)
              (paramIteratedDeriv A ![w] τ) +
            gibbsCumulantThree μ (A τ) (paramIteratedDeriv H ![w] τ) (paramIteratedDeriv A ![u] τ)
              (paramIteratedDeriv A ![v] τ) -
            gibbsCovariance μ (A τ) (H τ) (paramIteratedDeriv A ![w, v, u] τ) +
            gibbsCumulantThree μ (A τ) (H τ) (paramIteratedDeriv A ![v, u] τ) (paramIteratedDeriv A ![w] τ) +
            gibbsCumulantThree μ (A τ) (H τ) (paramIteratedDeriv A ![w, u] τ) (paramIteratedDeriv A ![v] τ) +
            gibbsCumulantThree μ (A τ) (H τ) (paramIteratedDeriv A ![w, v] τ) (paramIteratedDeriv A ![u] τ) -
            gibbsCumulantFour μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ) (paramIteratedDeriv A ![v] τ)
              (paramIteratedDeriv A ![w] τ)
def GibbsMeanDifferentiation : Prop :=
  DifferentiationUnderIntegral ∧ GibbsMeanThirdOrderExpansion
end YangMills.Construction.ColdStepAtMirrorFrames
end
