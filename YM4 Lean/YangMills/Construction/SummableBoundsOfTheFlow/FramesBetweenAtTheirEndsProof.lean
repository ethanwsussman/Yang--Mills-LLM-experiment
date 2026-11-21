import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Interpolation
open BlockAverages ColdStepAtMirrorFrames
variable {F : BlockFrame}
private theorem interpolatedFrame_segmentEnd (e : Bool) (a A : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4)
    (V : F.GaugeField F.top) :
    interpolatedFrame (segmentEnd e) a A m b V = stepFrame e a A m b V := by
  cases e <;> simp [interpolatedFrame, segmentEnd]
private theorem interpolatedCoords_segmentEnd (e : Bool) (a A : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    interpolatedCoords (segmentEnd e) a A m V η = coordsAboveFrame e a A m V η := by
  funext z i
  simp only [interpolatedCoords, coordsAboveFrame, interpolatedFrame_segmentEnd]
private theorem interpolatedField_segmentEnd (e : Bool) (a A : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    interpolatedField (segmentEnd e) a A m V η = fieldAboveFrame e a A m V η := by
  simp only [interpolatedField, fieldAboveFrame, interpolatedCoords_segmentEnd]
private theorem interpolatedExpansion_segmentEnd (e : Bool) (a A : ℝ) (m : ℕ) (f : LocalFamily)
    (y : F.Site F.depth) (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    interpolatedExpansion (segmentEnd e) a A m f y η V = centredExpansion e a A m f y η V := by
  simp only [interpolatedExpansion, centredExpansion, interpolatedField_segmentEnd]
private theorem interpolatedExponent_segmentEnd (e : Bool) (a A x : ℝ) (m : ℕ) (f : LocalFamily)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    interpolatedExponent (segmentEnd e) a A x m V η = stepExponent e a A x m f 0 V η := by
  simp only [interpolatedExponent, stepExponent, interpolatedCoords_segmentEnd,
    interpolatedField_segmentEnd, zero_mul, sub_zero]
theorem interpolationAtEndpoints_holds : interpolationAtEndpoints := by
  intro F e a A lam x τ m V
  refine ⟨fun b => interpolatedFrame_segmentEnd e a A m b V, interpolatedCoords_segmentEnd e a A m V,
    interpolatedField_segmentEnd e a A m V,
    fun f y η => interpolatedExpansion_segmentEnd e a A m f y η V, ?_, ?_, ?_⟩
  · intro Y η
    simp only [interpolatedBlockExponent, cellExponent, interpolatedCoords_segmentEnd,
      interpolatedField_segmentEnd]
  · intro f η
    have h0 := interpolatedExponent_segmentEnd e a A x m f V η
    simp only [stepExponent, zero_mul, sub_zero] at h0
    simp only [familyLawExponent, stepExponent, one_mul, interpolatedExpansion_segmentEnd, h0]
  · intro f η
    simp only [weightLawExponent, interpolatedExponent_segmentEnd e a A x m f V η]
end YangMills.Construction.Interpolation
end
