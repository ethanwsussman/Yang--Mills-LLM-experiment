import YangMills.Construction.FreeEnergiesOfTheFlow.StateOfAStepIsBorelProof
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.BlockAverages YangMills.Construction.StepSettings YangMills.Construction.StepCosts YangMills.Construction.TorusLumps YangMills.Construction.TorusFields YangMills.Construction.LumpContours YangMills.Construction.WeightedResponses
section Sigma
variable {X : Type} [MeasurableSpace X]
theorem measurable_of_measurableSet_fibres {D Z : Type} [Countable D] [MeasurableSpace Z] (f : X → D)
    (hf : ∀ d, MeasurableSet {x | f x = d}) (G : D → X → Z) (hG : ∀ d, Measurable (G d)) :
    Measurable fun x => G (f x) x := by apply _root_.YangMills.SharedProofs.p23008 <;> assumption
end Sigma
theorem measurableSet_torusHotSites_eq (ℓ : StepParameters) (n : ℕ) [NeZero n] (H : Finset (TorusSite n)) :
    MeasurableSet {V : TorusField n | torusHotSites ℓ V = H} := by apply _root_.YangMills.SharedProofs.p4955 <;> assumption
section Step
variable (R : StepSetup) {n : ℕ} [NeZero n]
theorem measurable_coarseStateOf {X : Type} [MeasurableSpace X] {Vf : X → TorusField n}
    (hV : Measurable Vf)
    {Wf : X → TorusField (n * R.params.side)} (hW : Measurable Wf)
    {qf : X → Σ Y : Finset (TorusSite (n * R.params.side)), (Y → R.labels.Ω)} (hq : Measurable qf)
    {bf : X → Finset (TorusBond (n * R.params.side))} (hbad : ∀ a, MeasurableSet {x | bf x = a})
    {cf : X → BaseChoice R.params.side n} (hcf : ∀ a, MeasurableSet {x | cf x = a}) :
    Measurable fun x =>
      coarseStateOf R (hotCoreSites R (Vf x)) (Wf x) (qf x).1 (qf x).2 (bf x) (cf x) := by apply _root_.YangMills.SharedProofs.p10828 <;> assumption
end Step
theorem stageStates_measurable : StageStatesMeasurableStatement := by
  classical
  intro ℓ hf T s
  induction s with
  | zero =>
    intro n _
    have hY : ∀ a, MeasurableSet
        {W : TorusField n | thickening (2 * clusterRange T.base.coupling) (torusHotSites ℓ W) = a} := by
      intro a
      have e : {W : TorusField n | thickening (2 * clusterRange T.base.coupling) (torusHotSites ℓ W) = a} =
          ⋃ H ∈ (Finset.univ.filter fun H : Finset (TorusSite n) =>
            thickening (2 * clusterRange T.base.coupling) H = a),
            {V | torusHotSites ℓ V = H} := by
        ext x
        simp
      rw [e]
      exact Finset.measurableSet_biUnion _ fun H _ => measurableSet_torusHotSites_eq ℓ n H
    have h := measurable_of_measurableSet_fibres
      (fun W : TorusField n => thickening (2 * clusterRange T.base.coupling) (torusHotSites ℓ W)) hY
      (fun a W => (⟨a, fun _ => T.basePoint⟩ : Σ Y : Finset (TorusSite n), (Y → T.base.labels.Ω)))
      (fun a => measurable_const)
    exact measurable_id.prodMk h
  | succ s ih =>
    intro n _
    have hq := ih (n * ℓ.side)
    have h1 : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
        stageState T s (n * ℓ.side) u.1 :=
      hq.comp measurable_fst
    have hV : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => u.2.2.1 :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    have hb : ∀ a : Finset (TorusBond (n * ℓ.side)), MeasurableSet
        {u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n |
          (u.2.2.2 : Finset (TorusBond (n * ℓ.side))) = a} := by
      intro a
      have hm : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => u.2.2.2 :=
        measurable_snd.comp (measurable_snd.comp measurable_snd)
      have hs : MeasurableSet ({a} : Set (BondSet (n * ℓ.side))) := MeasurableSpace.measurableSet_top
      exact hm hs
    have hc : ∀ a : BaseChoice ℓ.side n, MeasurableSet
        {u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n | u.2.1 = a} := by
      intro a
      have hm : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => u.2.1 :=
        measurable_fst.comp measurable_snd
      have hs : MeasurableSet ({a} : Set (BaseChoice ℓ.side n)) := MeasurableSpace.measurableSet_top
      exact hm hs
    have h2 := measurable_coarseStateOf (T.stage s).toStepSetup hV (measurable_fst.comp h1)
      (measurable_snd.comp h1) hb hc
    exact hV.prodMk h2
end YangMills.Construction.ResponseInTheExpansion
end
