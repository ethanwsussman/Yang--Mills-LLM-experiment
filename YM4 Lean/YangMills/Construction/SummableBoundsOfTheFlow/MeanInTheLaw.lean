import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Estimates
variable {F : BlockFrame}
def conditionalExpansionMean (star : Bool) (a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (φ h : LocalFamily) :
    TopLevelFamily :=
  fun _ Y V => cutoffMean ρ p (stepExponent star a ρA x m φ 1 V) fun η => cellCentredExpansion star a ρA m h Y η V
def HasConditionalMean (star : Bool) (a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (φ h : LocalFamily) (Y : F.Cell)
    (V : F.GaugeField F.top) : Prop :=
  Integrable (fun η : StepVariable (finiteCells F) =>
      cutoffWeight ρ p η * Real.exp (- stepExponent star a ρA x m φ 1 V η)) ∧
    0 < ∫ η : StepVariable (finiteCells F),
      cutoffWeight ρ p η * Real.exp (- stepExponent star a ρA x m φ 1 V η) ∧
    Integrable (fun η : StepVariable (finiteCells F) => cellCentredExpansion star a ρA m h Y η V *
      (cutoffWeight ρ p η * Real.exp (- stepExponent star a ρA x m φ 1 V η)))
end Estimates
end YangMills.Construction
end
