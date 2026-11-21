import YangMills.Construction.FreeEnergiesOfTheFlow.StateOfAStepIsBorel
import YangMills.Construction.ResponseInTheExpansion.ElementsOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace FreeEnergiesOfTheFlow
open StepSettings TorusLumps TorusFields StepCosts WeightedResponses BlockAverages LumpContours
section SigmaMeasurability
variable {X : Type} [MeasurableSpace X]
private theorem measurable_sigmaMk_of {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    Measurable (Sigma.mk a : β a → Sigma β) :=
  measurable_iff_le_map.2 (iInf_le _ a)
private theorem measurable_sigma_of_forall {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] {γ : Type}
    [MeasurableSpace γ] {f : Sigma β → γ} (h : ∀ a, Measurable fun y : β a => f ⟨a, y⟩) : Measurable f :=
  fun _ ht => MeasurableSpace.measurableSet_iInf.2 fun a => h a ht
abbrev _root_.YangMills.SharedProofs.p3239 := @measurable_sigma_of_forall
private theorem measurableSet_sigma_fst_eq {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by
  refine MeasurableSpace.measurableSet_iInf.2 fun a' => ?_
  show MeasurableSet ((Sigma.mk a' : β a' → Sigma β) ⁻¹' {z | z.1 = a})
  by_cases h : a' = a
  · subst h
    have e : (Sigma.mk a' : β a' → Sigma β) ⁻¹' {z | z.1 = a'} = Set.univ := by
      ext y
      simp
    rw [e]
    exact MeasurableSet.univ
  · have e : (Sigma.mk a' : β a' → Sigma β) ⁻¹' {z | z.1 = a} = ∅ := by
      ext y
      simpa using h
    rw [e]
    exact MeasurableSet.empty
abbrev _root_.YangMills.SharedProofs.p1937 := @measurableSet_sigma_fst_eq
private theorem measurable_of_countable_fibres {D Z : Type} [Countable D] [MeasurableSpace Z] (f : X → D)
    (hf : ∀ d, MeasurableSet {x | f x = d}) (G : D → X → Z) (hG : ∀ d, Measurable (G d)) :
    Measurable fun x => G (f x) x := by
  intro s hs
  have e : (fun x => G (f x) x) ⁻¹' s = ⋃ d, {x | f x = d} ∩ (G d) ⁻¹' s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨f x, rfl, h⟩
    · rintro ⟨d, rfl, h⟩
      exact h
  rw [e]
  exact MeasurableSet.iUnion fun d => (hf d).inter (hG d hs)
abbrev _root_.YangMills.SharedProofs.p23008 := @measurable_of_countable_fibres
private theorem measurableSet_finset_filter_eq {α : Type} (s : Finset α) (c : α → X → Prop)
    (hc : ∀ p, MeasurableSet {x | c p x}) (inst : ∀ x, DecidablePred fun p => c p x) (A : Finset α) :
    MeasurableSet {x | s.filter (fun p => c p x) = A} := by
  classical
  by_cases hA : A ⊆ s
  · have e : {x | s.filter (fun p => c p x) = A} = ⋂ p ∈ s, {x | c p x ↔ p ∈ A} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h p hp
        rw [← h]
        simp [hp]
      · intro h
        ext p
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hp, hq⟩
          exact (h p hp).1 hq
        · intro hp
          exact ⟨hA hp, (h p (hA hp)).2 hp⟩
    rw [e]
    refine Finset.measurableSet_biInter s fun p _ => ?_
    by_cases hp : p ∈ A
    · have e2 : {x | c p x ↔ p ∈ A} = {x | c p x} := by
        ext x
        simp [hp]
      rw [e2]
      exact hc p
    · have e2 : {x | c p x ↔ p ∈ A} = {x | c p x}ᶜ := by
        ext x
        simp [hp]
      rw [e2]
      exact (hc p).compl
  · have e : {x | s.filter (fun p => c p x) = A} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hA (h ▸ Finset.filter_subset _ _)
    rw [e]
    exact MeasurableSet.empty
end SigmaMeasurability
section HotPlaquettes
variable {F : BlockFrame} {α : Type} [TopologicalSpace α]
private theorem continuous_pathHolonomy_of {j : ℕ} (X : α → F.GaugeField j) (hX : ∀ x i, Continuous fun a => X a x i)
    (x : F.Site j) (l : List PathStep) : Continuous fun a => pathHolonomy (X a) x l := by
  induction l generalizing x with
  | nil => exact continuous_const
  | cons st r ih =>
    simp only [pathHolonomy]
    refine Continuous.mul ?_ (ih _)
    rcases st with ⟨i, b⟩
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false]
      exact (hX _ _).inv
    · simp only [linkValue, if_true]
      exact hX _ _
private theorem continuous_plaquetteDefect_of {j : ℕ} (X : α → F.GaugeField j) (hX : ∀ x i, Continuous fun a => X a x i)
    (p : F.Site j × Fin 4 × Fin 4) : Continuous fun a => plaquetteDefect (X a) p := by
  unfold plaquetteDefect plaquetteHolonomy
  exact ((continuous_subtype_val.comp (continuous_pathHolonomy_of X hX _ _)).sub continuous_const).norm
end HotPlaquettes
private theorem measurableSet_torusHotSites_eq (ℓ : StepParameters) (n : ℕ) [NeZero n] (H : Finset (TorusSite n)) :
    MeasurableSet {V : TorusField n | torusHotSites ℓ V = H} := by
  classical
  set F := stepBlockFrame ℓ.side (n / ℓ.side) with hF
  set S := cutPlaquettes (levelSites F 0) with hS
  have hcl : ∀ p : F.Site 0 × Fin 4 × Fin 4,
      MeasurableSet {V : TorusField n | ℓ.threshold ≤ plaquetteDefect (readAtLevel F 0 V) p} := by
    intro p
    have hc : Continuous fun V : TorusField n => plaquetteDefect (readAtLevel F 0 V) p :=
      continuous_plaquetteDefect_of (fun V : TorusField n => readAtLevel F 0 V)
        (fun x i => (continuous_apply i).comp (continuous_apply _)) p
    exact (isClosed_le continuous_const hc).measurableSet
  have hfib := fun A : Finset (F.Site 0 × Fin 4 × Fin 4) =>
    measurableSet_finset_filter_eq S (fun p (V : TorusField n) => ℓ.threshold ≤ plaquetteDefect (readAtLevel F 0 V) p) hcl
      (fun _ _ => Classical.propDecidable _) A
  let Ψ : Finset (F.Site 0 × Fin 4 × Fin 4) → Finset (TorusSite n) := fun A =>
    ((A.biUnion fun p => (plaquetteCorners p).image (lumpOf ℓ.grid)).image
      (fun l : Finset (F.Site 0) => l.image (toTorusSite n))).biUnion id
  have hform : ∀ V : TorusField n, torusHotSites ℓ V =
      Ψ (S.filter fun p => ℓ.threshold ≤ plaquetteDefect (readAtLevel F 0 V) p) := fun V => rfl
  have e : {V : TorusField n | torusHotSites ℓ V = H} = ⋃ A ∈ S.powerset.filter (fun A => Ψ A = H),
      {V : TorusField n | S.filter (fun p => ℓ.threshold ≤ plaquetteDefect (readAtLevel F 0 V) p) = A} := by
    ext V
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_powerset, exists_prop]
    constructor
    · intro h
      exact ⟨_, ⟨Finset.filter_subset _ _, by rw [← hform V]; exact h⟩, rfl⟩
    · rintro ⟨A, ⟨_, h⟩, rfl⟩
      rw [hform V]
      exact h
  rw [e]
  exact Finset.measurableSet_biUnion _ fun A _ => by convert hfib A
abbrev _root_.YangMills.SharedProofs.p4955 := @measurableSet_torusHotSites_eq
section CoarseState
variable (R : StepSetup) {n : ℕ} [NeZero n]
open Classical in
private def labelAtSite {S B : Type} (z : S) (q : Σ Y : Finset S, (Y → B)) : WithNone B :=
  if h : z ∈ q.1 then Sum.inr (q.2 ⟨z, h⟩) else Sum.inl ()
private theorem measurable_labelAtSite {S B : Type} [MeasurableSpace B] (z : S) :
    Measurable (labelAtSite (B := B) z) := by
  classical
  refine measurable_sigma_of_forall fun a => ?_
  by_cases h : z ∈ a
  · have e : (fun y : a → B => labelAtSite z (⟨a, y⟩ : Σ Y : Finset S, (Y → B))) =
        fun y => Sum.inr (y ⟨z, h⟩) := by
      funext y
      simp [labelAtSite, h]
    rw [e]
    exact measurable_inr.comp (measurable_pi_apply _)
  · have e : (fun y : a → B => labelAtSite z (⟨a, y⟩ : Σ Y : Finset S, (Y → B))) =
        fun _ => Sum.inl () := by
      funext y
      simp [labelAtSite, h]
    rw [e]
    exact measurable_const
private abbrev DiscreteIndex (R : StepSetup) (n : ℕ) : Type :=
  Finset (TorusSite n) × Finset (TorusSite (n * R.params.side)) × Finset (TorusBond (n * R.params.side)) ×
    BaseChoice R.params.side n
open Classical in
private def markAtDiscreteIndex (d : DiscreteIndex R n) (W : TorusField (n * R.params.side))
    (q : Σ Y : Finset (TorusSite (n * R.params.side)), (Y → R.labels.Ω)) (y : TorusSite n) :
    BlockLabels R.labels.Ω R.params.side :=
  { isCore := decide (y ∈ d.1)
    badBond := fun c => decide ((blockSite y c.1, c.2) ∈ d.2.2.1)
    siteLabel := fun o => labelAtSite (blockSite y o) q
    basePoint := baseOffset R d.2.2.2 y
    linkValue := fun c => if parentBlock R.params.side
        (blockSite (L := R.params.side) y c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈
        storedBlocks R.params.side R.range d.2.2.1 d.2.1 d.1
      then Sum.inr (W (blockSite y c.1) c.2) else Sum.inl () }
open Classical in
private def coarseStateAtIndex (d : DiscreteIndex R n) (W : TorusField (n * R.params.side))
    (q : Σ Y : Finset (TorusSite (n * R.params.side)), (Y → R.labels.Ω)) : CoarseState R n :=
  ⟨coarseHull R.params.side R.range R.nextRange d.2.2.1 d.2.1 d.1, fun y =>
    if (y : TorusSite n) ∈ storedBlocks R.params.side R.range d.2.2.1 d.2.1 d.1 then
      Sum.inr (markAtDiscreteIndex R d W q y)
    else Sum.inl ()⟩
private theorem coarseStateOf_eq_atIndex (C : Finset (TorusSite n)) (W : TorusField (n * R.params.side))
    (q : Σ Y : Finset (TorusSite (n * R.params.side)), (Y → R.labels.Ω))
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    coarseStateOf R C W q.1 q.2 bad b = coarseStateAtIndex R (C, q.1, bad, b) W q := by
  classical
  unfold coarseStateOf coarseStateAtIndex
  refine congrArg (Sigma.mk _) (funext fun y => ?_)
  by_cases hy : (y : TorusSite n) ∈ storedBlocks R.params.side R.range bad q.1 C
  · simp only [if_pos hy]
    refine congrArg Sum.inr ?_
    unfold blockConfigAt markAtDiscreteIndex
    congr 1
    funext o
    by_cases ho : blockSite (L := R.params.side) (y : TorusSite n) o ∈ q.1
    · simp [labelAtSite, ho]
    · simp [labelAtSite, ho]
  · simp only [if_neg hy]
private theorem measurable_configAtDatum {X : Type} [MeasurableSpace X] (d : DiscreteIndex R n)
    {Wf : X → TorusField (n * R.params.side)} (hW : Measurable Wf)
    {qf : X → Σ Y : Finset (TorusSite (n * R.params.side)), (Y → R.labels.Ω)} (hq : Measurable qf)
    (y : TorusSite n) :
    Measurable fun x => markAtDiscreteIndex R d (Wf x) (qf x) y := by
  classical
  refine measurable_comap_iff.2 ?_
  refine measurable_const.prodMk (measurable_const.prodMk
    ((measurable_pi_lambda _ fun o => (measurable_labelAtSite _).comp hq).prodMk
      (measurable_const.prodMk (measurable_pi_lambda _ fun c => ?_))))
  show Measurable fun x => (markAtDiscreteIndex R d (Wf x) (qf x) y).linkValue c
  unfold markAtDiscreteIndex
  by_cases hc : parentBlock R.params.side
      (blockSite (L := R.params.side) y c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈
      storedBlocks R.params.side R.range d.2.2.1 d.2.1 d.1
  · simp only [if_pos hc]
    exact measurable_inr.comp ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp hW))
  · simp only [if_neg hc]
    exact measurable_const
private theorem measurable_coarseStateAtDatum {X : Type} [MeasurableSpace X] (d : DiscreteIndex R n)
    {Wf : X → TorusField (n * R.params.side)} (hW : Measurable Wf)
    {qf : X → Σ Y : Finset (TorusSite (n * R.params.side)), (Y → R.labels.Ω)} (hq : Measurable qf) :
    Measurable fun x => coarseStateAtIndex R d (Wf x) (qf x) := by
  classical
  refine (measurable_sigmaMk_of (β := fun Y : Finset (TorusSite n) => Y → CoarseLabel R.labels.Ω R.params.side)
    (coarseHull R.params.side R.range R.nextRange d.2.2.1 d.2.1 d.1)).comp
      (measurable_pi_lambda _ fun y => ?_)
  by_cases hy : (y : TorusSite n) ∈ storedBlocks R.params.side R.range d.2.2.1 d.2.1 d.1
  · simp only [if_pos hy]
    exact measurable_inr.comp (measurable_configAtDatum R d hW hq y)
  · simp only [if_neg hy]
    exact measurable_const
private theorem measurable_coarseStateOf_of {X : Type} [MeasurableSpace X] {Vf : X → TorusField n}
    (hV : Measurable Vf) {Wf : X → TorusField (n * R.params.side)} (hW : Measurable Wf)
    {qf : X → Σ Y : Finset (TorusSite (n * R.params.side)), (Y → R.labels.Ω)} (hq : Measurable qf)
    {bf : X → Finset (TorusBond (n * R.params.side))} (hbad : ∀ a, MeasurableSet {x | bf x = a})
    {cf : X → BaseChoice R.params.side n} (hcf : ∀ a, MeasurableSet {x | cf x = a}) :
    Measurable fun x =>
      coarseStateOf R (hotCoreSites R (Vf x)) (Wf x) (qf x).1 (qf x).2 (bf x) (cf x) := by
  classical
  have hC : ∀ a, MeasurableSet {x | hotCoreSites R (Vf x) = a} := by
    intro a
    have e : {x | hotCoreSites R (Vf x) = a} =
        ⋃ H ∈ (Finset.univ.filter fun H : Finset (TorusSite n) => thickening (2 * R.nextRange) H = a),
          Vf ⁻¹' {V | torusHotSites R.params V = H} := by
      ext x
      simp [hotCoreSites]
    rw [e]
    exact Finset.measurableSet_biUnion _ fun H _ => hV (measurableSet_torusHotSites_eq R.params n H)
  have hY : ∀ a, MeasurableSet {x | (qf x).1 = a} := fun a => hq (measurableSet_sigma_fst_eq a)
  have hd : ∀ d : DiscreteIndex R n, MeasurableSet
      {x | ((hotCoreSites R (Vf x), (qf x).1, bf x, cf x) : DiscreteIndex R n) = d} := by
    intro d
    have e : {x | ((hotCoreSites R (Vf x), (qf x).1, bf x, cf x) : DiscreteIndex R n) = d} =
        {x | hotCoreSites R (Vf x) = d.1} ∩ ({x | (qf x).1 = d.2.1} ∩
          ({x | bf x = d.2.2.1} ∩ {x | cf x = d.2.2.2})) := by
      ext x
      obtain ⟨d1, d2, d3, d4⟩ := d
      simp
    rw [e]
    exact (hC _).inter ((hY _).inter ((hbad _).inter (hcf _)))
  have h := measurable_of_countable_fibres
    (fun x => ((hotCoreSites R (Vf x), (qf x).1, bf x, cf x) : DiscreteIndex R n)) hd
    (fun d x => coarseStateAtIndex R d (Wf x) (qf x)) (fun d => measurable_coarseStateAtDatum R d hW hq)
  have e : (fun x => coarseStateOf R (hotCoreSites R (Vf x)) (Wf x) (qf x).1 (qf x).2 (bf x) (cf x)) =
      fun x => coarseStateAtIndex R (hotCoreSites R (Vf x), (qf x).1, bf x, cf x) (Wf x) (qf x) :=
    funext fun x => coarseStateOf_eq_atIndex R _ _ _ _ _
  rw [e]
  exact h
abbrev _root_.YangMills.SharedProofs.p10828 := @measurable_coarseStateOf_of
end CoarseState
theorem measurableNextStageState_holds : MeasurableNextStageState := by
  classical
  intro ℓ _ T s n _
  have hV : Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n => p.2.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hb : ∀ a : Finset (TorusBond (n * ℓ.side)), MeasurableSet
      {p : StageState T s (n * ℓ.side) × StepOutcome ℓ n |
        (p.2.2.2 : Finset (TorusBond (n * ℓ.side))) = a} := by
    intro a
    have hm : Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n => p.2.2.2 :=
      measurable_snd.comp (measurable_snd.comp measurable_snd)
    have hs : MeasurableSet ({a} : Set (BondSet (n * ℓ.side))) := MeasurableSpace.measurableSet_top
    exact hm hs
  have hc : ∀ a : BaseChoice ℓ.side n, MeasurableSet
      {p : StageState T s (n * ℓ.side) × StepOutcome ℓ n | p.2.1 = a} := by
    intro a
    have hm : Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n => p.2.1 :=
      measurable_fst.comp measurable_snd
    have hs : MeasurableSet ({a} : Set (BaseChoice ℓ.side n)) := MeasurableSpace.measurableSet_top
    exact hm hs
  have h2 := measurable_coarseStateOf_of (T.stage s).toStepSetup hV (measurable_fst.comp measurable_fst)
    (measurable_snd.comp measurable_fst) hb hc
  exact hV.prodMk h2
end FreeEnergiesOfTheFlow
end YangMills.Construction
end
