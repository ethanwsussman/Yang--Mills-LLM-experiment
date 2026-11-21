import YangMills.Construction.FreeEnergiesOfTheFlow.StateOfAStepIsBorelProof
import YangMills.Construction.ResponseInTheExpansion.AStepOfTheStateIsBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion.CoarseStateMeasurableProof
open StepSettings TorusLumps TorusFields StepCosts BlockAverages LumpContours
section Step
variable (R : StepSetup) {n : ℕ} [NeZero n]
private theorem measurable_coarseStateOf {X : Type} [MeasurableSpace X] {Vf : X → TorusField n}
    (hV : Measurable Vf)
    {Wf : X → TorusField (n * R.params.side)} (hW : Measurable Wf)
    {qf : X → Σ Y : Finset (TorusSite (n * R.params.side)), (Y → R.labels.Ω)} (hq : Measurable qf)
    {bf : X → Finset (TorusBond (n * R.params.side))} (hbad : ∀ a, MeasurableSet {x | bf x = a})
    {cf : X → BaseChoice R.params.side n} (hcf : ∀ a, MeasurableSet {x | cf x = a}) :
    Measurable fun x =>
      coarseStateOf R (hotCoreSites R (Vf x)) (Wf x) (qf x).1 (qf x).2 (bf x) (cf x) := by apply _root_.YangMills.SharedProofs.p10828 <;> assumption
end Step
theorem coarseStateMeasurable : ResponseInTheExpansion.CoarseStateMeasurable := by
  intro R n _ X _ Vf Wf qf bf cf hV hW hq hb hc
  exact measurable_coarseStateOf R hV hW hq hb hc
end YangMills.Construction.ResponseInTheExpansion.CoarseStateMeasurableProof
end
