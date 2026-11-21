import YangMills.Construction.SummableBoundsOfTheFlow.FloorOfTheScaledExponentsProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheExponentOfALawIsASumOfItsParts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace ScaledVariables
variable {F : BlockFrame}
private theorem mem_finiteCells_of_finite (h : Finite F.Cell) (Y : F.Cell) : Y ∈ finiteCells F := by apply _root_.YangMills.SharedProofs.p8277 <;> assumption
private theorem sum_cells_sum_chordBonds_ite (h : Finite F.Cell) (g : ↥(chordBonds (finiteCells F)) → ℝ) :
    ∑ Y ∈ finiteCells F, ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y then g b else 0) = ∑ b, g b := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq]
  simp [mem_finiteCells_of_finite h]
abbrev _root_.YangMills.SharedProofs.p35694 := @sum_cells_sum_chordBonds_ite
private theorem rescaledExponent_eq_sum (h : Finite F.Cell) (a ρ lam l ν : ℝ) (f : LocalFamily) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) :
    rescaledExponent a ρ f ν l V ζ = ∑ Y ∈ finiteCells F, rescaledCellRemainder a ρ lam l Y V ζ +
      lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2 - ν * ∑ Y ∈ finiteCells F, rescaledCellExpansion a ρ f l Y V ζ := by
  classical
  have hRemainder : ∑ Y ∈ finiteCells F, rescaledCellRemainder a ρ lam l Y V ζ = ∑ Y ∈ finiteCells F, rescaledCellTerm a ρ l Y V ζ -
      lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2 := by
    unfold rescaledCellRemainder
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_cells_sum_chordBonds_ite h]
  have hRow : ∑ Y ∈ finiteCells F, rescaledCellExpansion a ρ f l Y V ζ =
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion true a ρ 0 f y (l • ζ) V := by
    unfold rescaledCellExpansion cellCentredExpansion
    exact Finset.sum_fiberwise_of_maps_to (fun y _ => mem_finiteCells_of_finite h (enclosingCell y)) _
  rw [hRemainder, hRow]
  unfold rescaledExponent
  ring
theorem lawExponentDecomposition : lawExponentDecompositionStatement := by
  intro F a ρ lam l f law V ζ h
  cases law with
  | tilted ν =>
    simp only [rescaledLawExponent, remainderCoefficient, expansionCoefficient]
    rw [rescaledExponent_eq_sum h a ρ lam l ν f V ζ]
    ring
  | interpolated τ =>
    simp only [rescaledLawExponent, remainderCoefficient, expansionCoefficient]
    rw [rescaledExponent_eq_sum h a ρ lam l 0 f V ζ]
    ring
end ScaledVariables
end YangMills.Construction
end
