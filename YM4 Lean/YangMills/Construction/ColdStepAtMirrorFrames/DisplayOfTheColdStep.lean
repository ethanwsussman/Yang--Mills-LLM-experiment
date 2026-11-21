import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def openBallProduct (F : BlockFrame) (ρ : ℝ) : Set (StepVariable (finiteCells F)) :=
  {η | ∀ b, ‖η b‖ < ρ}
structure IsRegularStep (a ρA ρ lam x M : ℝ) (m : ℕ) (p : ℝ → ℝ) (f : LocalFamily)
    (V : F.GaugeField F.top) : Prop where
  measurable_cutoffWeight : Measurable (cutoffWeight (F := F) ρ p)
  cutoffWeight_nonneg : ∀ η : StepVariable (finiteCells F), 0 ≤ cutoffWeight ρ p η
  cutoffWeight_eq_zero_of_not_mem : ∀ η : StepVariable (finiteCells F), η ∉ openBallProduct F ρ →
    cutoffWeight ρ p η = 0
  integrable_cutoffWeight : Integrable (cutoffWeight (F := F) ρ p)
  integral_cutoffWeight_pos : 0 < ∫ η : StepVariable (finiteCells F), cutoffWeight ρ p η
  bound_nonneg : 0 ≤ M
  continuousOn_cellExponent : ∀ Y, ContinuousOn (cellExponent false a ρA x m Y V) (openBallProduct F ρ)
  continuousOn_cellQuadratic : ∀ Y : F.Cell,
    ContinuousOn (cellQuadratic (F := F) lam x Y) (openBallProduct F ρ)
  continuousOn_cellCentredExpansion : ∀ Y,
    ContinuousOn (fun η => cellCentredExpansion false a ρA m f Y η V) (openBallProduct F ρ)
  abs_cellExponent_le : ∀ Y, ∀ η ∈ openBallProduct F ρ, |cellExponent false a ρA x m Y V η| ≤ M
  abs_cellQuadratic_le : ∀ Y : F.Cell, ∀ η ∈ openBallProduct F ρ,
    |cellQuadratic (F := F) lam x Y η| ≤ M
  abs_cellCentredExpansion_le : ∀ Y, ∀ η ∈ openBallProduct F ρ, |cellCentredExpansion false a ρA m f Y η V| ≤ M
  stepExponent_eq_sum : ∀ η ∈ openBallProduct F ρ, stepExponent false a ρA x m f 0 V η =
    ∑ Y ∈ finiteCells F, cellExponent false a ρA x m Y V η
def logStepIntegralDecomposition : Prop :=
  ∀ (F : BlockFrame) (a ρA ρ lam x M : ℝ) (m : ℕ) (p : ℝ → ℝ) (f : LocalFamily) (V : F.GaugeField F.top),
    0 ≤ a → Odd F.blockSide → (∀ i, 2 ≤ F.extent i) →
    (∀ b ∈ chordBonds (finiteCells F), ‖stepFrame false a ρA m b V‖ + ρ < Real.pi) →
    IsRegularStep a ρA ρ lam x M m p f V →
    Real.log (stepIntegral a ρA ρ x m p f (finiteCells F) V) =
      (∑ _c ∈ innerBonds (finiteCells F) F.top, haarGap (a * x)) +
        (∑ _b : ↥(chordBonds (finiteCells F)), Real.log (haarRadialDensity 0)) +
        Real.log (gaussianMass ρ lam x p F) - x * minimalAction a (finiteCells F) F.top V +
        ∑ Y ∈ finiteCells F, (interactionDensity false a ρA ρ lam x m p f Y V +
          expansionDensity false a ρA ρ x m p f Y V + frameDensity false a ρA x m Y V)
end YangMills.Construction.ColdStepAtMirrorFrames
end
