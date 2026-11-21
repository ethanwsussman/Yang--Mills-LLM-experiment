import YangMills.Construction.SummableBoundsOfTheFlow.SmoothObservablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace ScaledVariables
variable {F : BlockFrame}
structure IsTameOnScales (s ρ lo hi D : ℝ)
    (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) : Prop where
  contDiffAt : ∀ V' : F.GaugeField F.top, IsSmallCurvature s V' → ∀ (l : ℝ) (ζ : StepVariable (finiteCells F))
    (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), lo < l → l < hi →
    MemScaledBalls ρ l ζ →
    ContDiffAt ℝ 6 (fun q : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) =>
      Ob q.1.1 q.1.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.2) V')) ((l, ζ), 0)
  deriv_le : ∀ V' : F.GaugeField F.top, IsSmallCurvature s V' → ∀ (k i : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (l : ℝ) (ζ : StepVariable (finiteCells F)), IsControlledOrder k i →
    AreUnitVectors X → lo < l → l < hi →
    MemScaledBalls ρ l ζ → |scaleDeriv Ob V' c X i ζ l| ≤ D
def scaledCutoff (w : ℝ → ℝ) (l : ℝ) (ζ : StepVariable (finiteCells F)) : ℝ :=
  ∏ b : ↥(chordBonds (finiteCells F)), w (l * ‖ζ b‖)
def tiltedWeight (w : ℝ → ℝ) (q : StepVariable (finiteCells F) → ℝ)
    (A : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (l : ℝ) (V' : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) : ℝ :=
  scaledCutoff w l ζ * Real.exp (-q ζ) * Real.exp (A l ζ V')
def tiltedAverage (w : ℝ → ℝ) (q : StepVariable (finiteCells F) → ℝ)
    (A : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (l : ℝ) (V' : F.GaugeField F.top)
    (H : StepVariable (finiteCells F) → ℝ) : ℝ :=
  (∫ ζ, H ζ * tiltedWeight w q A l V' ζ) / ∫ ζ, tiltedWeight w q A l V' ζ
def tiltedMean (w : ℝ → ℝ) (q : StepVariable (finiteCells F) → ℝ)
    (A Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (l : ℝ)
    (V' : F.GaugeField F.top) : ℝ :=
  tiltedAverage w q A l V' fun ζ => Ob l ζ V'
def cumulantEntries (A Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (l : ℝ)
    (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (I : Finset (Fin k)) :
    Option (Finset (Fin k)) → StepVariable (finiteCells F) → ℝ
  | none => fun ζ => bondDeriv (Ob l ζ) V (c ∘ I.orderEmbOfFin rfl) (X ∘ I.orderEmbOfFin rfl)
  | some J => fun ζ => bondDeriv (A l ζ) V (c ∘ J.orderEmbOfFin rfl) (X ∘ J.orderEmbOfFin rfl)
end ScaledVariables
end YangMills.Construction
end
