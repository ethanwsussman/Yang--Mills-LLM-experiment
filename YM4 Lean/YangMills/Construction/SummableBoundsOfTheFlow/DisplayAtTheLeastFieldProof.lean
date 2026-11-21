import YangMills.Construction.SummableBoundsOfTheFlow.DisplayAtTheLeastField
import YangMills.Construction.SummableBoundsOfTheFlow.LogAlongATiltProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.Interpolation
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
private theorem stepFrame_eq_of_not_large {m₁ : ℕ} (hm : ¬ ∀ i, 4 * m₁ + 5 < F.extent i) (a ρA : ℝ) (m : ℕ)
    (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) :
    stepFrame false a ρA m₁ b V = stepFrame true a ρA m b V := by
  simp [stepFrame, bondFrameCoord, hm]
private theorem coordsAboveFrame_eq_of_not_large {m₁ : ℕ} (hm : ¬ ∀ i, 4 * m₁ + 5 < F.extent i) (a ρA : ℝ) (m : ℕ)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    coordsAboveFrame false a ρA m₁ V η = coordsAboveFrame true a ρA m V η := by
  funext z i
  simp only [coordsAboveFrame, stepFrame_eq_of_not_large hm a ρA m (z, i) V]
private theorem fieldAboveFrame_eq_of_not_large {m₁ : ℕ} (hm : ¬ ∀ i, 4 * m₁ + 5 < F.extent i) (a ρA : ℝ) (m : ℕ)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    fieldAboveFrame false a ρA m₁ V η = fieldAboveFrame true a ρA m V η := by
  simp only [fieldAboveFrame, coordsAboveFrame_eq_of_not_large hm a ρA m V η]
private theorem centredExpansion_eq_of_not_large {m₁ : ℕ} (hm : ¬ ∀ i, 4 * m₁ + 5 < F.extent i) (a ρA : ℝ) (m : ℕ)
    (f : LocalFamily) (y : F.Site F.depth) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    centredExpansion false a ρA m₁ f y η V = centredExpansion true a ρA m f y η V := by
  simp only [centredExpansion, fieldAboveFrame_eq_of_not_large hm a ρA m V η]
private theorem cellCentredExpansion_eq_of_not_large {m₁ : ℕ} (hm : ¬ ∀ i, 4 * m₁ + 5 < F.extent i) (a ρA : ℝ) (m : ℕ)
    (f : LocalFamily) (Y : F.Cell) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    cellCentredExpansion false a ρA m₁ f Y η V = cellCentredExpansion true a ρA m f Y η V := by
  simp only [cellCentredExpansion, centredExpansion_eq_of_not_large hm a ρA m f _ V η]
private theorem stepExponent_eq_of_not_large {m₁ : ℕ} (hm : ¬ ∀ i, 4 * m₁ + 5 < F.extent i) (a ρA x : ℝ) (m : ℕ)
    (f : LocalFamily) (ν : ℝ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    stepExponent false a ρA x m₁ f ν V η = stepExponent true a ρA x m f ν V η := by
  simp only [stepExponent, coordsAboveFrame_eq_of_not_large hm a ρA m V,
    fieldAboveFrame_eq_of_not_large hm a ρA m V η, centredExpansion_eq_of_not_large hm a ρA m f _ V η]
private theorem cellExponent_eq_of_not_large {m₁ : ℕ} (hm : ¬ ∀ i, 4 * m₁ + 5 < F.extent i) (a ρA x : ℝ) (m : ℕ)
    (Y : F.Cell) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    cellExponent false a ρA x m₁ Y V η = cellExponent true a ρA x m Y V η := by
  simp only [cellExponent, coordsAboveFrame_eq_of_not_large hm a ρA m V,
    fieldAboveFrame_eq_of_not_large hm a ρA m V η]
private theorem interpolatedStepIntegral_zero_eq {m₁ : ℕ} (hm : ¬ ∀ i, 4 * m₁ + 5 < F.extent i) (a ρA ρ x : ℝ) (m : ℕ)
    (p : ℝ → ℝ) (f : LocalFamily) (V : F.GaugeField F.top) :
    interpolatedStepIntegral 0 a ρA ρ x m p f V = stepIntegral a ρA ρ x m₁ p f (finiteCells F) V := by apply _root_.YangMills.SharedProofs.p39075 <;> assumption
theorem logIntegralAtMinimizer (hd : logStepIntegralDecomposition) :
    logIntegralAtMinimizerStatement := by
  intro F a ρA ρ lam x M m m' m₁ p f V ha hodd hs hm hframe hreg
  have h := hd F a ρA ρ lam x M m₁ p f V ha hodd hs
    (fun b hb => by rw [stepFrame_eq_of_not_large hm a ρA m b V]; exact hframe b hb) hreg
  rw [interpolatedStepIntegral_zero_eq hm]
  rw [h]
  have hU : ∀ Y, interactionDensity false a ρA ρ lam x m₁ p f Y V =
      interactionDensity true a ρA ρ lam x m' p f Y V := by
    intro Y
    simp only [interactionDensity, stepExponent_eq_of_not_large hm a ρA x m' f 0 V,
      cellExponent_eq_of_not_large hm a ρA x m' Y V]
  have hS : ∀ Y, expansionDensity false a ρA ρ x m₁ p f Y V = expansionDensity true a ρA ρ x m' p f Y V := by
    intro Y
    have e : ∀ ν, stepExponent false a ρA x m₁ f ν V = stepExponent true a ρA x m' f ν V :=
      fun ν => funext (stepExponent_eq_of_not_large hm a ρA x m' f ν V)
    simp only [expansionDensity, e, cellCentredExpansion_eq_of_not_large hm a ρA m' f Y V]
  have hT : ∀ Y, frameDensity false a ρA x m₁ Y V = frameDensity true a ρA x m' Y V := by
    intro Y
    simp only [frameDensity, stepFrame_eq_of_not_large hm a ρA m' _ V]
  simp only [hU, hS, hT]
end YangMills.Construction.Interpolation
end
