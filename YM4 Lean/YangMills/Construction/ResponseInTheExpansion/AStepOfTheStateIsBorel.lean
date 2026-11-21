import YangMills.Construction.ClusterExpansionOfAStep.StatesOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ResponseInTheExpansion
open YangMills.Construction.StepSettings YangMills.Construction.TorusFields YangMills.Construction.StepCosts YangMills.Construction.TorusLumps
def CoarseStateMeasurable : Prop :=
  ∀ (R : StepSetup) (n : ℕ) [NeZero n] (X : Type) [MeasurableSpace X]
    (fineField : X → TorusField n) (coarseField : X → TorusField (n * R.params.side))
    (lowerState : X → Σ Y : Finset (TorusSite (n * R.params.side)), (Y → R.labels.Ω))
    (bondChoice : X → Finset (TorusBond (n * R.params.side)))
    (baseChoice : X → BaseChoice R.params.side n),
    Measurable fineField → Measurable coarseField → Measurable lowerState →
    (∀ a, MeasurableSet {x | bondChoice x = a}) →
    (∀ a, MeasurableSet {x | baseChoice x = a}) →
    Measurable fun x => coarseStateOf R (hotCoreSites R (fineField x)) (coarseField x)
      (lowerState x).1 (lowerState x).2 (bondChoice x) (baseChoice x)
end ResponseInTheExpansion
end YangMills.Construction
end
