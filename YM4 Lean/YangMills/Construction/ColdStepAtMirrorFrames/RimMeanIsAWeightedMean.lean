import YangMills.Construction.ColdStepAtMirrorFrames.BirthsAlongTwoSegments
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def cutoffLaw (F : BlockFrame) (ρ : ℝ) (p : ℝ → ℝ) : Measure (StepVariable (finiteCells F)) :=
  volume.withDensity fun η => ENNReal.ofReal (cutoffWeight ρ p η)
def CutoffMeanIsGibbsMean : Prop :=
  ∀ (F : BlockFrame) (ρ : ℝ) (p : ℝ → ℝ), 0 < ρ → IsCutoff ρ p →
    IsFiniteMeasure (cutoffLaw F ρ p) ∧ cutoffLaw F ρ p ≠ 0 ∧ (∀ᵐ η ∂cutoffLaw F ρ p, ∀ b, ‖η b‖ < ρ) ∧
      ∀ Ψ H : StepVariable (finiteCells F) → ℝ,
        cutoffMean ρ p Ψ H = gibbsMean (cutoffLaw F ρ p) Ψ H
end YangMills.Construction.ColdStepAtMirrorFrames
end
