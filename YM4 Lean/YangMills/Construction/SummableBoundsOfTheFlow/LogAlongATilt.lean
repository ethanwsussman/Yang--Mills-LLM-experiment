import YangMills.Construction.ColdStepAtMirrorFrames.DisplayOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.FromTheMirrorFramesToTheLeastField
import YangMills.Construction.SummableBoundsOfTheFlow.MeanInTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Estimates MeasureTheory
namespace Interpolation
variable {F : BlockFrame}
structure IsRegularSegment (a ρA ρ x M : ℝ) (m : ℕ) (p : ℝ → ℝ) (φ h : LocalFamily)
    (V : F.GaugeField F.top) : Prop where
  measurable_cutoffWeight : Measurable (cutoffWeight (F := F) ρ p)
  cutoffWeight_nonneg : ∀ η : StepVariable (finiteCells F), 0 ≤ cutoffWeight ρ p η
  cutoffWeight_eq_zero_of_not_mem : ∀ η : StepVariable (finiteCells F), η ∉ openBallProduct F ρ →
    cutoffWeight ρ p η = 0
  integrable_cutoffWeight : Integrable (cutoffWeight (F := F) ρ p)
  integral_cutoffWeight_pos : 0 < ∫ η : StepVariable (finiteCells F), cutoffWeight ρ p η
  bound_nonneg : 0 ≤ M
  continuousOn_stepExponent : ContinuousOn (stepExponent true a ρA x m φ 1 V) (openBallProduct F ρ)
  continuousOn_cellCentredExpansion : ∀ Y,
    ContinuousOn (fun η => cellCentredExpansion true a ρA m h Y η V) (openBallProduct F ρ)
  abs_stepExponent_le : ∀ η ∈ openBallProduct F ρ, |stepExponent true a ρA x m φ 1 V η| ≤ M
  abs_cellCentredExpansion_le : ∀ Y, ∀ η ∈ openBallProduct F ρ, |cellCentredExpansion true a ρA m h Y η V| ≤ M
def logIntegralAlongSegmentStatement : Prop :=
  ∀ (F : BlockFrame) (a ρA ρ x M : ℝ) (m m₁ : ℕ) (p : ℝ → ℝ) (φ h : LocalFamily) (V : F.GaugeField F.top),
    Odd F.blockSide → (∀ i, 2 ≤ F.extent i) → (¬ ∀ i, 4 * m₁ + 5 < F.extent i) →
    (∀ b ∈ chordBonds (finiteCells F), ‖stepFrame true a ρA m b V‖ + ρ < Real.pi) →
    IsRegularSegment a ρA ρ x M m p φ h V →
    Real.log (interpolatedStepIntegral 0 a ρA ρ x m p (φ + h) V) -
        Real.log (interpolatedStepIntegral 0 a ρA ρ x m p φ V) =
      ∑ Y ∈ finiteCells F, ∫ θ in (0 : ℝ)..1, conditionalExpansionMean true a ρA ρ x m p (φ + θ • h) h F Y V
end Interpolation
end YangMills.Construction
end
