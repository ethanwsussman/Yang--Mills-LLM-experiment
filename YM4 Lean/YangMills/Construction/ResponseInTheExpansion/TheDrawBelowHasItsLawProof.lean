import YangMills.Construction.ResponseInTheExpansion.LawOfTheDrawsBelowProof
import YangMills.Construction.ResponseInTheExpansion.TheDrawBelowHasItsLaw
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepSettings StepCosts BlockAverages ColdStepAtMirrorFrames
namespace ForgetLastStep
section Tower
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters}
variable (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean)
  (hf : ℓ.Admissible) (hfl : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side) (T : StageTower ℓ)
  (hcut : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (hmark : T.MarksMeasurable) (β : ℝ)
include hS hM hf hfl hcut hmark in
theorem isProbabilityMeasure_markedSampleLaw (s : ℕ) :
    ∀ (n : ℕ) [NeZero n], IsProbabilityMeasure (markedSampleLaw T β s n) := by apply _root_.YangMills.SharedProofs.p20096 <;> assumption
include hS hM hf hfl hcut hmark in
theorem measurePreserving_forgetLastStep (s n : ℕ) [NeZero n] :
    MeasurePreserving (fun u : MarkedSample ℓ (s + 1) n => u.1) (markedSampleLaw T β (s + 1) n)
      (markedSampleLaw T β s (n * ℓ.side)) := by apply _root_.YangMills.SharedProofs.p11229 <;> assumption
end Tower
end ForgetLastStep
open ForgetLastStep in
theorem forgetLastStepStatement_holds (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean) :
    forgetLastStepStatement :=
  fun _ hf hfl T hcut hmark β s n _ =>
    ⟨isProbabilityMeasure_markedSampleLaw hS hM hf hfl T hcut hmark β s n,
      measurePreserving_forgetLastStep hS hM hf hfl T hcut hmark β s n⟩
end YangMills.Construction.WeightedResponses
end
