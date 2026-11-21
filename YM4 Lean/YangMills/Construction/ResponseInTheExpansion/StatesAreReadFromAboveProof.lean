import YangMills.Construction.ResponseInTheExpansion.AStepOfTheStateIsBorel
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import YangMills.Construction.ResponseInTheExpansion.StatesAreReadFromAbove
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
variable {ℓ : TorusLumps.StepParameters}
private theorem upperSigma_le_markedSample (T : WeightedResponses.StageTower ℓ) (t : ℕ)
    (hst : ∀ (n : ℕ) [NeZero n], WeightedResponses.stageSigma T t n ≤ WeightedResponses.markedSampleMeasurableSpace ℓ t n) :
    ∀ (d n : ℕ) [NeZero n], upperSigma T t d n ≤ WeightedResponses.markedSampleMeasurableSpace ℓ (t + d) n
  | 0, n, _ => hst n
  | d + 1, n, _ =>
    sup_le_sup (MeasurableSpace.comap_mono (upperSigma_le_markedSample T t hst d (n * ℓ.side))) le_rfl
private theorem stageState_measurable_upperSigma (hS : CoarseStateMeasurable) (T : WeightedResponses.StageTower ℓ) (t : ℕ) :
    ∀ (d n : ℕ) [NeZero n], Measurable[upperSigma T t d n] (WeightedResponses.stageState T (t + d) n)
  | 0, n, _ => comap_measurable _
  | d + 1, n, _ => by
    have hq := stageState_measurable_upperSigma hS T t d (n * ℓ.side)
    let mX : MeasurableSpace (WeightedResponses.MarkedSample ℓ (t + d + 1) n) := upperSigma T t (d + 1) n
    have hfst : @Measurable _ _ mX (upperSigma T t d (n * ℓ.side))
        (fun u : WeightedResponses.MarkedSample ℓ (t + d + 1) n => u.1) :=
      (comap_measurable _).mono le_sup_left le_rfl
    have hsnd : @Measurable _ _ mX inferInstance (fun u : WeightedResponses.MarkedSample ℓ (t + d + 1) n => u.2) :=
      (comap_measurable _).mono le_sup_right le_rfl
    have h1 : Measurable fun u : WeightedResponses.MarkedSample ℓ (t + d + 1) n =>
        WeightedResponses.stageState T (t + d) (n * ℓ.side) u.1 :=
      hq.comp hfst
    have hV : Measurable fun u : WeightedResponses.MarkedSample ℓ (t + d + 1) n => u.2.2.1 :=
      measurable_fst.comp (measurable_snd.comp hsnd)
    have hb : ∀ a : Finset (TorusFields.TorusBond (n * ℓ.side)), MeasurableSet
        {u : WeightedResponses.MarkedSample ℓ (t + d + 1) n | (u.2.2.2 : Finset (TorusFields.TorusBond (n * ℓ.side))) = a} := by
      intro a
      have hm : Measurable fun u : WeightedResponses.MarkedSample ℓ (t + d + 1) n => u.2.2.2 :=
        measurable_snd.comp (measurable_snd.comp hsnd)
      have hs : MeasurableSet ({a} : Set (WeightedResponses.BondSet (n * ℓ.side))) := MeasurableSpace.measurableSet_top
      exact hm hs
    have hc : ∀ a : StepCosts.BaseChoice ℓ.side n, MeasurableSet
        {u : WeightedResponses.MarkedSample ℓ (t + d + 1) n | u.2.1 = a} := by
      intro a
      have hm : Measurable fun u : WeightedResponses.MarkedSample ℓ (t + d + 1) n => u.2.1 :=
        measurable_fst.comp hsnd
      have hs : MeasurableSet ({a} : Set (StepCosts.BaseChoice ℓ.side n)) := MeasurableSpace.measurableSet_top
      exact hm hs
    have h2 := hS (T.stage (t + d)).toStepSetup n (WeightedResponses.MarkedSample ℓ (t + d + 1) n)
      (fun u => u.2.2.1) (fun u => (WeightedResponses.stageState T (t + d) (n * ℓ.side) u.1).1)
      (fun u => (WeightedResponses.stageState T (t + d) (n * ℓ.side) u.1).2) (fun u => u.2.2.2) (fun u => u.2.1)
      hV (measurable_fst.comp h1) (measurable_snd.comp h1) hb hc
    exact hV.prodMk h2
theorem upperSigmaDeterminesStates (hB : StageStatesMeasurableStatement)
    (hS : CoarseStateMeasurable) : upperSigmaDeterminesStatesStatement := by
  intro ℓ hf T t d n _
  exact ⟨upperSigma_le_markedSample T t (fun m _ => (hB ℓ hf T t m).comap_le) d n,
    stageState_measurable_upperSigma hS T t d n⟩
end YangMills.Construction.ResponseInTheExpansion
end
