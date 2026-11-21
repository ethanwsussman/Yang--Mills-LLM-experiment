import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.TameObservablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ScaledVariables
variable {F : BlockAverages.BlockFrame}
def remainderCoefficient : StepLaw → ℝ
  | .tilted _ => 1
  | .interpolated τ => τ
def expansionCoefficient : StepLaw → ℝ
  | .tilted ν => ν
  | .interpolated _ => 0
def lawExponent (a ρ lam : ℝ) (f : ColdStepAtMirrorFrames.LocalFamily) (law : StepLaw) (l : ℝ)
    (ζ : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells F))
    (V : F.GaugeField F.top) : ℝ :=
  (-remainderCoefficient law) *
      (∑ Y ∈ ColdStepAtMirrorFrames.finiteCells F, rescaledCellRemainder a ρ lam l Y V ζ) +
    expansionCoefficient law * ∑ Y ∈ ColdStepAtMirrorFrames.finiteCells F, rescaledCellExpansion a ρ f l Y V ζ
def gaussianPart (lam : ℝ)
    (ζ : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells F)) : ℝ :=
  lam / 2 * ∑ b : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F)), ‖ζ b‖ ^ 2
def cutoffWeight (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : ℝ :=
  ColdStepAtMirrorFrames.cutoffFactor ρ p (max u 0)
structure ScaledMeansTame (T : ColdStepAtMirrorFrames.StepParameters) (F : BlockAverages.BlockFrame)
    (f : ColdStepAtMirrorFrames.LocalFamily) (law : StepLaw) (l₁ : ℝ) : Prop where
  exponent_tame : ∀ lo : ℝ, 0 < lo → ∃ D : ℝ, 0 ≤ D ∧
    IsTameOnScales (5 / 4 * T.σ) T.ballRadius lo (2 * l₁) D (lawExponent (F := F) T.a T.ρA T.lam f law)
  observable_tame : ∀ (K : ℝ) (Y : F.Cell)
    (Ob : ℝ → ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells F) → F.GaugeField F.top → ℝ),
    0 ≤ K → IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius (2 * l₁) K Y Ob →
      ∀ lo : ℝ, 0 < lo → ∃ D : ℝ, 0 ≤ D ∧ IsTameOnScales (5 / 4 * T.σ) T.ballRadius lo (2 * l₁) D Ob
  mean_eq : ∀ (V : F.GaugeField F.top) (l : ℝ)
    (Ob : ℝ → ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells F) → F.GaugeField F.top → ℝ),
    ColdStepAtMirrorFrames.IsSmallCurvature (5 / 4 * T.σ) V → 0 < l → l ≤ 2 * l₁ →
    observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l V =
      tiltedMean (cutoffWeight T.ballRadius T.p) (gaussianPart T.lam) (lawExponent T.a T.ρA T.lam f law) Ob l V
def scaledMeansTameStatement : Prop :=
  ColdStepAtMirrorFrames.EventuallyOrdered fun T => ∀ e : ℕ → ℝ, ∃ l₀ : ℝ, 0 < l₀ ∧
    ∀ l₁ : ℝ, 0 < l₁ → l₁ ≤ l₀ →
    ∀ (t : ℕ) (f : ColdStepAtMirrorFrames.LocalFamily) (F : BlockAverages.BlockFrame) (law : StepLaw),
      T.IsBoundedFamilyOrderSix e t f →
      ColdStepAtMirrorFrames.IsCubicTopTorus T.L t T.n₀ F → ScaledMeansTame T F f law l₁
end YangMills.Construction.ScaledVariables
end
