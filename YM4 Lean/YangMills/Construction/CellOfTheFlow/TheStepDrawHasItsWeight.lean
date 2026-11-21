import YangMills.Construction.CellOfTheFlow.NoiseOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace YangMills.Construction.CellWindows
open TorusFields StepSettings WeightedResponses
def stepOutcomeDensityStatement : Prop :=
  ∀ (R : StepSetup) (S : StepSampler R), S.IsFaithful →
    ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn →
    ∀ (n : ℕ) [NeZero n], R.params.side ∣ n → 64 ≤ n →
      (∀ bad : Finset (TorusBond (n * R.params.side)),
        Measurable fun q : TorusField (n * R.params.side) × TorusField n => markLaw R q.1 q.2 bad) →
      Measurable (fun q : TorusField (n * R.params.side) × StepNoise R.params n => S.sample q.1 q.2) ∧
      ∀ (W : TorusField (n * R.params.side)) (G : StepOutcome R.params n → ℝ≥0∞), Measurable G →
        ∫⁻ ξ, G (S.sample W ξ) ∂(stepNoiseMeasure R.params n) =
          ∫⁻ o, G o * ENNReal.ofReal (stepOutcomeDensity R W o) ∂(stepReferenceMeasure R.params n)
end YangMills.Construction.CellWindows
end
