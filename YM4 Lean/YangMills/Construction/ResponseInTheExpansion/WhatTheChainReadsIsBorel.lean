import YangMills.Construction.ClusterExpansionOfAStep.CumulantsOfTheKernelsAtMovedBonds
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages LumpContours ColdStepAtMirrorFrames WeightedResponses TorusFields TorusLumps StepSettings
def chainMeasurabilityStatement : Prop :=
  (∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
    MeasurableSet {V : TorusField n | hotCoreSites R V = a}) ∧
  MeasurableQuaternion (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])) ∧
  ∀ (ℓ : TorusLumps.StepParameters), ℓ.Admissible → 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side →
    ∀ T : StageTower ℓ, IsCutoff (ℓ.threshold / 64) T.base.barrierFn →
    T.MarksMeasurable → ∀ (β : ℝ) (s n : ℕ) [NeZero n],
      IsProbabilityMeasure (markedSampleLaw T β s n) ∧
      (markedSampleLaw T β (s + 1) n).map (fun u : MarkedSample ℓ (s + 1) n => u.1) =
        markedSampleLaw T β s (n * ℓ.side)
end YangMills.Construction.ResponseInTheExpansion
end
