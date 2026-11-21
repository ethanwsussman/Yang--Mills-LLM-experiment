import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMean
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.Estimates
variable {F : BlockFrame}
def JointlyContDiffOnBalls (ρ : ℝ) (V : F.GaugeField F.top)
    (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) : Prop :=
  ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)),
    (∀ b, ‖η b‖ ≤ ρ) →
    ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) (0, η)
def gibbsMeanAt (μ : Measure (StepVariable (finiteCells F)))
    (A G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) : ℝ :=
  gibbsMean μ (fun η => A η V) fun η => G η V
def fieldDeriv {k : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)) : ℝ :=
  bondDeriv (G η) V c X
def fieldDerivOne {k : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (i : Fin k) : StepVariable (finiteCells F) → ℝ :=
  fieldDeriv G V (fun _ : Fin 1 => c i) fun _ => X i
def fieldDerivTwo {k : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (i j : Fin k) : StepVariable (finiteCells F) → ℝ :=
  fieldDeriv G V ![c i, c j] ![X i, X j]
structure GibbsMeanExpansions (μ : Measure (StepVariable (finiteCells F))) (V : F.GaugeField F.top)
    (A H : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) : Prop where
  deriv_one : ∀ (c : Fin 1 → F.Site F.top × Fin 4) (X : Fin 1 → imaginaryQuaternions),
    bondDeriv (gibbsMeanAt μ A H) V c X = gibbsMean μ (fun η => A η V) (fieldDeriv H V c X) -
      gibbsCovariance μ (fun η => A η V) (fun η => H η V) (fieldDeriv A V c X)
  deriv_two : ∀ (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions),
    bondDeriv (gibbsMeanAt μ A H) V c X = gibbsMean μ (fun η => A η V) (fieldDeriv H V c X) -
      gibbsCovariance μ (fun η => A η V) (fieldDerivOne H V c X 1) (fieldDerivOne A V c X 0) -
      gibbsCovariance μ (fun η => A η V) (fieldDerivOne H V c X 0) (fieldDerivOne A V c X 1) -
      gibbsCovariance μ (fun η => A η V) (fun η => H η V) (fieldDeriv A V c X) +
      gibbsCumulantThree μ (fun η => A η V) (fun η => H η V) (fieldDerivOne A V c X 1)
        (fieldDerivOne A V c X 0)
  deriv_three : ∀ (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions),
    bondDeriv (gibbsMeanAt μ A H) V c X = gibbsMean μ (fun η => A η V) (fieldDeriv H V c X) -
      gibbsCovariance μ (fun η => A η V) (fieldDerivTwo H V c X 1 2) (fieldDerivOne A V c X 0) -
      gibbsCovariance μ (fun η => A η V) (fieldDerivTwo H V c X 0 2) (fieldDerivOne A V c X 1) -
      gibbsCovariance μ (fun η => A η V) (fieldDerivTwo H V c X 0 1) (fieldDerivOne A V c X 2) -
      gibbsCovariance μ (fun η => A η V) (fieldDerivOne H V c X 2) (fieldDerivTwo A V c X 0 1) -
      gibbsCovariance μ (fun η => A η V) (fieldDerivOne H V c X 1) (fieldDerivTwo A V c X 0 2) -
      gibbsCovariance μ (fun η => A η V) (fieldDerivOne H V c X 0) (fieldDerivTwo A V c X 1 2) +
      gibbsCumulantThree μ (fun η => A η V) (fieldDerivOne H V c X 2) (fieldDerivOne A V c X 1)
        (fieldDerivOne A V c X 0) +
      gibbsCumulantThree μ (fun η => A η V) (fieldDerivOne H V c X 1) (fieldDerivOne A V c X 2)
        (fieldDerivOne A V c X 0) +
      gibbsCumulantThree μ (fun η => A η V) (fieldDerivOne H V c X 0) (fieldDerivOne A V c X 2)
        (fieldDerivOne A V c X 1) -
      gibbsCovariance μ (fun η => A η V) (fun η => H η V) (fieldDeriv A V c X) +
      gibbsCumulantThree μ (fun η => A η V) (fun η => H η V) (fieldDerivTwo A V c X 1 2)
        (fieldDerivOne A V c X 0) +
      gibbsCumulantThree μ (fun η => A η V) (fun η => H η V) (fieldDerivTwo A V c X 0 2)
        (fieldDerivOne A V c X 1) +
      gibbsCumulantThree μ (fun η => A η V) (fun η => H η V) (fieldDerivTwo A V c X 0 1)
        (fieldDerivOne A V c X 2) -
      gibbsCumulantFour μ (fun η => A η V) (fun η => H η V) (fieldDerivOne A V c X 2)
        (fieldDerivOne A V c X 1) (fieldDerivOne A V c X 0)
def GibbsMeanExpansionInField : Prop :=
  ∀ (F : BlockFrame) (ρ : ℝ) (μ : Measure (StepVariable (finiteCells F))) (V : F.GaugeField F.top)
    (A H : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ), IsFiniteMeasure μ → μ ≠ 0 →
    (∀ᵐ η ∂μ, ∀ b, ‖η b‖ ≤ ρ) → JointlyContDiffOnBalls ρ V A → JointlyContDiffOnBalls ρ V H →
    ContDiffThreeAlongBonds (gibbsMeanAt μ A H) V ∧ GibbsMeanExpansions μ V A H
end YangMills.Construction.Estimates
end
