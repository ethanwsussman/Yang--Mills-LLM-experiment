import YangMills.Construction.CellOfTheFlow.TheNoiseDrawsTheChainProof
import YangMills.Construction.CellOfTheFlow.TheStepDrawHasItsWeight
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal Quaternion
namespace YangMills.Construction.CellWindows
open WeightedResponses StepSettings TorusLumps TorusFields StepCosts LumpContours TopLevelSites TorusContours
  BlockAverages
namespace OutcomeDensity
section Step
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem measurable_sample (S : StepSampler R) (hD : S.IsFaithful)
    (hc : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn) (hg : R.params.side ∣ n ∧ 64 ≤ n)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad) :
    Measurable fun p : TorusField (n * R.params.side) × StepNoise R.params n => S.sample p.1 p.2 := by apply _root_.YangMills.SharedProofs.p94641 <;> assumption
private theorem lintegral_sample_eq (S : StepSampler R) (hD : S.IsFaithful) (hBL : ClusterExpansionOfAStep.BaseLawIsProduct)
    (hc : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn) (hg : R.params.side ∣ n ∧ 64 ≤ n)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (W : TorusField (n * R.params.side)) (F : StepOutcome R.params n → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ξ, F (S.sample W ξ) ∂(stepNoiseMeasure R.params n) =
      ∫⁻ e, F e * ENNReal.ofReal (stepOutcomeDensity R W e) ∂(stepReferenceMeasure R.params n) := by apply _root_.YangMills.SharedProofs.p65995 <;> assumption
end Step
end OutcomeDensity
open OutcomeDensity in
theorem stepOutcomeDensityStatement_of_baseLawIsProduct (hBL : ClusterExpansionOfAStep.BaseLawIsProduct) :
    stepOutcomeDensityStatement :=
  fun R S hD hc n _ hL h64 hB =>
    ⟨measurable_sample S hD hc ⟨hL, h64⟩ hB, fun W F hF => lintegral_sample_eq S hD hBL hc ⟨hL, h64⟩ hB W F hF⟩
end YangMills.Construction.CellWindows
end
