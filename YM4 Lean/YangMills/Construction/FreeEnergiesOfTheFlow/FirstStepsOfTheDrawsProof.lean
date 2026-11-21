import YangMills.Construction.FreeEnergiesOfTheFlow.FirstStepsOfTheDraws
import YangMills.Construction.ResponseInTheExpansion.LawOfTheDrawsBelowProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.FreeEnergiesOfTheFlow
open TorusFields TorusLumps StepSettings StepCosts WeightedResponses BlockAverages LumpContours ColdStepAtMirrorFrames
section Tower
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters}
variable (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean)
  (hf : ℓ.Admissible) (hfl : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side) (T : StageTower ℓ)
  (hcut : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (hmark : T.MarksMeasurable) (β : ℝ)
include hS hM hf hfl hcut hmark in
private theorem markedSampleLaw_fst_preserving (s n : ℕ) [NeZero n] :
    MeasurePreserving (fun u : MarkedSample ℓ (s + 1) n => u.1) (markedSampleLaw T β (s + 1) n)
      (markedSampleLaw T β s (n * ℓ.side)) := by apply _root_.YangMills.SharedProofs.p11229 <;> assumption
end Tower
theorem markedSampleTruncationPreserving (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean) :
    MarkedSampleTruncationPreserving :=
  fun _ hf hfl T hcut hmark β s n _ => markedSampleLaw_fst_preserving hS hM hf hfl T hcut hmark β s n
end YangMills.Construction.FreeEnergiesOfTheFlow
end
