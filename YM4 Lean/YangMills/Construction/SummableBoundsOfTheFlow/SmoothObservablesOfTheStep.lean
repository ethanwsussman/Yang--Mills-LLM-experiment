import YangMills.Construction.SummableBoundsOfTheFlow.ScaledVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
open scoped Topology
namespace ScaledVariables
variable {F : BlockFrame}
def localWeight (κ : ℝ) (Y : F.Cell) (ζ : StepVariable (finiteCells F)) : ℝ :=
  ∑ b : ↥(chordBonds (finiteCells F)),
    Real.exp (-(2 ^ 4 * κ * cellSupDist (enclosingCell b.1.1) Y)) * ‖ζ b‖
def IsControlledOrder (k i : ℕ) : Prop := (k ≤ 3 ∧ i ≤ 2) ∨ (k ≤ 2 ∧ i ≤ 3)
def scaleDeriv {k : ℕ} (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (i : ℕ) (ζ : StepVariable (finiteCells F)) (l : ℝ) : ℝ :=
  iteratedDeriv i (fun l' => bondDeriv (Ob l' ζ) V c X) l
def MemScaledBalls (ρ l : ℝ) (ζ : StepVariable (finiteCells F)) : Prop := ∀ b, l * ‖ζ b‖ < ρ
structure IsSmoothObservable (κ ρ l₁ K : ℝ) (Y : F.Cell) (V : F.GaugeField F.top)
    (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) : Prop where
  even : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)) (V' : F.GaugeField F.top),
    Ob (-l) (-ζ) V' = Ob l ζ V'
  contDiffAt : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), MemScaledBalls ρ |l| ζ →
    ContDiffAt ℝ 6 (fun q : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) =>
      Ob q.1.1 q.1.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.2) V)) ((l, ζ), 0)
  exists_smooth_extension : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    ∃ G : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) → ℝ,
      (∀ᶠ τ : Fin k → ℝ in 𝓝 0, ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l → l ≤ l₁ →
        MemScaledBalls ρ l ζ → G ((l, ζ), τ) = Ob l ζ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) ∧
      ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l → l ≤ l₁ → (∀ b, l * ‖ζ b‖ ≤ ρ) →
        ContDiffAt ℝ 6 G ((l, ζ), 0)
  deriv_le : ∀ (k i : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (l : ℝ)
    (ζ : StepVariable (finiteCells F)), IsControlledOrder k i → AreUnitVectors X → 0 < l → l ≤ l₁ →
    MemScaledBalls ρ l ζ →
    |scaleDeriv Ob V c X i ζ l| ≤
      K * (1 + localWeight κ Y ζ) ^ 7 * Real.exp (-(2 ^ 4 * κ * bondSpan Y c))
  partialDeriv_le : ∀ (k i : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (l : ℝ) (ζ : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
    IsControlledOrder k i → AreUnitVectors X → 0 < l → l ≤ l₁ → MemScaledBalls ρ l ζ → ‖e‖ = 1 →
    |bondPartialDeriv (fun ζ' => scaleDeriv Ob V c X i ζ' l) b ζ e| ≤
      K * (1 + localWeight κ Y ζ) ^ 7 *
        Real.exp (-(2 ^ 4 * κ * bondSpan Y (Fin.cons (enclosingCell b.1.1, 0) c :
          Fin (k + 1) → F.Site F.top × Fin 4)))
  continuousOn : ∀ (k i : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (R : ℝ),
    IsControlledOrder k i →
    ContinuousOn (fun q : ℝ × StepVariable (finiteCells F) => scaleDeriv Ob V c X i q.2 q.1)
      {q | 0 ≤ q.1 ∧ q.1 ≤ l₁ ∧ MemScaledBalls ρ q.1 q.2 ∧ ∀ b, ‖q.2 b‖ ≤ R}
def IsSmoothAtSmallCurvature (s κ ρ l₁ K : ℝ) (Y : F.Cell)
    (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) : Prop :=
  ∀ V' : F.GaugeField F.top, IsSmallCurvature s V' → IsSmoothObservable κ ρ l₁ K Y V' Ob
def StepLaw.IsUnitWeight : StepLaw → Prop
  | .tilted ν => 0 ≤ ν ∧ ν ≤ 1
  | .interpolated τ => 0 ≤ τ ∧ τ ≤ 1
def observableMean (a ρA ρ lam : ℝ) (p : ℝ → ℝ) (f : LocalFamily) (law : StepLaw)
    (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (l : ℝ) (V : F.GaugeField F.top) : ℝ :=
  rescaledMean a ρA ρ lam l p f law V fun ζ => Ob l ζ V
def observableGaussianMean (a ρ lam : ℝ) (f : LocalFamily) (law : StepLaw)
    (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) : ℝ :=
  gaussianMean a ρ lam f V law fun ζ => Ob 0 ζ V
def observableSecondOrderCoeff (a ρ lam : ℝ) (f : LocalFamily) (law : StepLaw)
    (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) : ℝ :=
  secondOrderCoeff a ρ lam f V law fun l ζ => Ob l ζ V
end ScaledVariables
end YangMills.Construction
end
