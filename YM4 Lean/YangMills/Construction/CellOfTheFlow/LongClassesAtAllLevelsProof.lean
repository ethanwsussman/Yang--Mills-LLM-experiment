import YangMills.Construction.CellOfTheFlow.BoundsGivenAStatePassUp
import YangMills.Construction.CellOfTheFlow.LongClassesAreRare
import YangMills.Construction.CellOfTheFlow.LongClassesAtAllLevels
import YangMills.Construction.FreeEnergiesOfTheFlow.StateOfAStepIsBorelProof
import YangMills.Construction.ResponseInTheExpansion.AStepOfTheStateIsBorel
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps TorusFields StepSettings WeightedResponses BlockAverages LumpContours RenormalizationStepParameters StepCosts
variable {ℓ : StepParameters}
private theorem measurableSet_sigma_fst_eq {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
private theorem measurableSet_of_three_maps {X A B C : Type} [MeasurableSpace X] [Countable A] [Countable B]
    [Countable C] (f : X → A) (g : X → B) (h : X → C) (hf : ∀ a, MeasurableSet {x | f x = a})
    (hg : ∀ b, MeasurableSet {x | g x = b}) (hh : ∀ c, MeasurableSet {x | h x = c}) (Q : A → B → C → Prop) :
    MeasurableSet {x | Q (f x) (g x) (h x)} := by
  have e : {x | Q (f x) (g x) (h x)} =
      ⋃ a, ⋃ b, ⋃ c, ⋃ (_ : Q a b c), {x | f x = a} ∩ ({x | g x = b} ∩ {x | h x = c}) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    constructor
    · intro hq
      exact ⟨_, _, _, hq, rfl, rfl, rfl⟩
    · rintro ⟨a, b, c, hq, rfl, rfl, rfl⟩
      exact hq
  rw [e]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun c =>
    MeasurableSet.iUnion fun _ => (hf a).inter ((hg b).inter (hh c))
private theorem measurableSet_filter_eq {X α : Type} [MeasurableSpace X] (s : Finset α) (c : α → X → Prop)
    (hc : ∀ p, MeasurableSet {x | c p x}) (inst : ∀ x, DecidablePred fun p => c p x) (A : Finset α) :
    MeasurableSet {x | s.filter (fun p => c p x) = A} := by
  classical
  by_cases hA : A ⊆ s
  · have e : {x | s.filter (fun p => c p x) = A} = ⋂ p ∈ s, {x | c p x ↔ p ∈ A} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
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
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hA (h ▸ Finset.filter_subset _ _)
    rw [e]
    exact MeasurableSet.empty
abbrev _root_.YangMills.SharedProofs.p36363 := @measurableSet_filter_eq
private theorem measurableSet_torusHotSites_eq (ℓ : StepParameters) (n : ℕ) [NeZero n] (H : Finset (TorusSite n)) :
    MeasurableSet {V : TorusField n | torusHotSites ℓ V = H} := by apply _root_.YangMills.SharedProofs.p4955 <;> assumption
private theorem measurableSet_hotCoreSites_eq (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)) :
    MeasurableSet {V : TorusField n | hotCoreSites R V = a} := by
  classical
  have e : {V : TorusField n | hotCoreSites R V = a} =
      ⋃ H ∈ (Finset.univ.filter fun H : Finset (TorusSite n) => thickening (2 * R.nextRange) H = a),
        {V | torusHotSites R.params V = H} := by
    ext x
    simp [hotCoreSites]
  rw [e]
  exact Finset.measurableSet_biUnion _ fun H _ => measurableSet_torusHotSites_eq R.params n H
abbrev _root_.YangMills.SharedProofs.p5873 := @measurableSet_hotCoreSites_eq
private theorem measurableSet_freeSupports (T : StageTower ℓ) (s n : ℕ) [NeZero n] {X : Type}
    [MeasurableSpace X] (Vf : X → TorusField n) (bf : X → Finset (TorusBond (n * ℓ.side)))
    (Yf : X → Finset (TorusSite (n * ℓ.side)))
    (hV : Measurable Vf) (hb : ∀ a, MeasurableSet {x | bf x = a}) (hY : ∀ a, MeasurableSet {x | Yf x = a})
    (Q : Finset (ClusterSupport ℓ.side n) → Prop) :
    MeasurableSet {x | Q (freeSupports (T.stage s).toStepSetup
      (hotCoreSites (T.stage s).toStepSetup (Vf x)) (bf x) (Yf x))} :=
  measurableSet_of_three_maps (fun x => hotCoreSites (T.stage s).toStepSetup (Vf x)) bf Yf
    (fun a => hV (measurableSet_hotCoreSites_eq (T.stage s).toStepSetup n a)) hb hY
    (fun a b c => Q (freeSupports (T.stage s).toStepSetup a b c))
private theorem hasLongSupport_succ_iff (T : StageTower ℓ) (K j s n : ℕ) [NeZero n] (u : MarkedSample ℓ (s + 1) n)
    (c : Finset (TorusSite n)) :
    HasLongSupport T K j (s + 1) n u c ↔
      (s = j ∧ ∃ θ ∈ freeSupportsAt T s n u, IsLongWithin ℓ.side (stageRange T s) (windowLength T K s) θ
        (sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T K s) c))) ∨
      HasLongSupport T K j s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c) :=
  Iff.rfl
private theorem not_hasLongSupport_of_le (T : StageTower ℓ) (K j s : ℕ) (hs : s ≤ j) :
    ∀ (n : ℕ) [NeZero n] (u : MarkedSample ℓ s n) (c : Finset (TorusSite n)), ¬ HasLongSupport T K j s n u c := by
  induction s with
  | zero =>
    intro n _ u c h
    exact h
  | succ s ih =>
    intro n _ u c h
    rcases (hasLongSupport_succ_iff T K j s n u c).1 h with ⟨h1, _⟩ | h
    · omega
    · exact ih (by omega) _ _ _ h
private theorem hasLongSupport_self_iff (T : StageTower ℓ) (K s n : ℕ) [NeZero n] (u : MarkedSample ℓ (s + 1) n)
    (c : Finset (TorusSite n)) :
    HasLongSupport T K s (s + 1) n u c ↔ ∃ θ ∈ freeSupportsAt T s n u,
      IsLongWithin ℓ.side (stageRange T s) (windowLength T K s) θ
        (sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T K s) c)) := by
  rw [hasLongSupport_succ_iff]
  constructor
  · rintro (⟨_, h⟩ | h)
    · exact h
    · exact absurd h (not_hasLongSupport_of_le T K s s le_rfl _ _ _)
  · intro h
    exact Or.inl ⟨rfl, h⟩
section Samples
variable (T : StageTower ℓ)
private theorem measurableSet_stageState_sites_eq (hq : ∀ (s n : ℕ) [NeZero n], Measurable (stageState T s n))
    (s n : ℕ) [NeZero n] (a : Finset (TorusSite n)) :
    MeasurableSet {u : MarkedSample ℓ s n | (stageState T s n u).2.1 = a} :=
  (measurable_snd.comp (hq s n)) (measurableSet_sigma_fst_eq a)
private theorem measurableSet_freeSupportsAt (hq : ∀ (s n : ℕ) [NeZero n], Measurable (stageState T s n))
    (s n : ℕ) [NeZero n] (Q : Finset (ClusterSupport ℓ.side n) → Prop) :
    MeasurableSet {v : MarkedSample ℓ (s + 1) n | Q (freeSupportsAt T s n v)} := by
  have hV : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => u.2.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hb : ∀ a : Finset (TorusBond (n * ℓ.side)), MeasurableSet
      {u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n | (u.2.2.2 : Finset (TorusBond (n * ℓ.side))) = a} := by
    intro a
    have hm : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => u.2.2.2 :=
      measurable_snd.comp (measurable_snd.comp measurable_snd)
    have hs : MeasurableSet ({a} : Set (BondSet (n * ℓ.side))) := MeasurableSpace.measurableSet_top
    exact hm hs
  have hY : ∀ a : Finset (TorusSite (n * ℓ.side)), MeasurableSet
      {u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n | (stageState T s (n * ℓ.side) u.1).2.1 = a} :=
    fun a => measurable_fst (measurableSet_stageState_sites_eq T hq s (n * ℓ.side) a)
  exact measurableSet_freeSupports T s n (fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => u.2.2.1)
    (fun u => u.2.2.2) (fun u => (stageState T s (n * ℓ.side) u.1).2.1) hV hb hY Q
private theorem measurableSet_hasLongSupport (hq : ∀ (s n : ℕ) [NeZero n], Measurable (stageState T s n))
    (K j s : ℕ) :
    ∀ (n : ℕ) [NeZero n] (c : Finset (TorusSite n)),
      MeasurableSet {u : MarkedSample ℓ s n | HasLongSupport T K j s n u c} := by
  induction s with
  | zero =>
    intro n _ c
    have e : {u : MarkedSample ℓ 0 n | HasLongSupport T K j 0 n u c} = ∅ := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact not_hasLongSupport_of_le T K j 0 (Nat.zero_le j) n u c
    rw [e]
    exact MeasurableSet.empty
  | succ s ih =>
    intro n _ c
    have e : {u : MarkedSample ℓ (s + 1) n | HasLongSupport T K j (s + 1) n u c} =
        {u | s = j ∧ ∃ θ ∈ freeSupportsAt T s n u, IsLongWithin ℓ.side (stageRange T s) (windowLength T K s) θ
            (sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T K s) c))} ∪
          (fun u : MarkedSample ℓ (s + 1) n => u.1) ⁻¹'
            {w : MarkedSample ℓ s (n * ℓ.side) | HasLongSupport T K j s (n * ℓ.side) w (sitesInBlocks ℓ.side c)} :=
      Set.ext fun u => hasLongSupport_succ_iff T K j s n u c
    rw [e]
    refine MeasurableSet.union ?_ ?_
    · exact measurableSet_freeSupportsAt T hq s n fun F => s = j ∧ ∃ θ ∈ F, IsLongWithin ℓ.side (stageRange T s)
        (windowLength T K s) θ (sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T K s) c))
    · have hm : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => u.1 := measurable_fst
      exact hm (ih (n * ℓ.side) (sitesInBlocks ℓ.side c))
private theorem measurableSet_coarseSigma_of_pair (s n : ℕ) [NeZero n]
    (B₀ : Set (StageState T s (n * ℓ.side) × StepOutcome ℓ n)) (hB : MeasurableSet B₀) :
    MeasurableSet[coarseSigma T s 1 n]
      {u : MarkedSample ℓ (s + 1) n | (stageState T s (n * ℓ.side) u.1, u.2) ∈ B₀} := by
  have hm : Measurable fun p : StageState T s (n * ℓ.side) × (Unit × StepOutcome ℓ n) => (p.1, p.2.2) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  exact ⟨_, hm hB, rfl⟩
private theorem measurable_coarseStep (hA : ResponseInTheExpansion.CoarseStateMeasurable) (s n : ℕ) [NeZero n] :
    Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n =>
      (⟨p.2.2.1, coarseStateOf (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup p.2.2.1)
        p.1.1 p.1.2.1 p.1.2.2 p.2.2.2 p.2.1⟩ : StageState T (s + 1) n) := by
  have hV : Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n => p.2.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hW : Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n => p.1.1 :=
    measurable_fst.comp measurable_fst
  have hQ : Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n => p.1.2 :=
    measurable_snd.comp measurable_fst
  have hb : ∀ a : Finset (TorusBond (n * ℓ.side)), MeasurableSet
      {p : StageState T s (n * ℓ.side) × StepOutcome ℓ n | (p.2.2.2 : Finset (TorusBond (n * ℓ.side))) = a} := by
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
  exact hV.prodMk (hA (T.stage s).toStepSetup n _ _ _ _ _ _ hV hW hQ hb hc)
private theorem measurableSet_state_inter_long (hA : ResponseInTheExpansion.CoarseStateMeasurable) (K s n : ℕ) [NeZero n]
    {ι : Type} (S : Finset ι) (C : ι → Finset (TorusSite n)) (A : Set (MarkedSample ℓ (s + 1) n))
    (hAm : MeasurableSet[stageSigma T (s + 1) n] A) :
    MeasurableSet[coarseSigma T s 1 n] (A ∩ {v | ∀ κ' ∈ S, HasLongSupport T K s (s + 1) n v (C κ')}) := by
  obtain ⟨A₀, hA₀, rfl⟩ := hAm
  have h1 := measurableSet_coarseSigma_of_pair T s n _ (measurable_coarseStep T hA s n hA₀)
  have hV : Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n => p.2.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hb : ∀ a : Finset (TorusBond (n * ℓ.side)), MeasurableSet
      {p : StageState T s (n * ℓ.side) × StepOutcome ℓ n | (p.2.2.2 : Finset (TorusBond (n * ℓ.side))) = a} := by
    intro a
    have hm : Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n => p.2.2.2 :=
      measurable_snd.comp (measurable_snd.comp measurable_snd)
    have hs : MeasurableSet ({a} : Set (BondSet (n * ℓ.side))) := MeasurableSpace.measurableSet_top
    exact hm hs
  have hY : ∀ a : Finset (TorusSite (n * ℓ.side)), MeasurableSet
      {p : StageState T s (n * ℓ.side) × StepOutcome ℓ n | p.1.2.1 = a} := fun a =>
    (measurable_snd.comp measurable_fst) (measurableSet_sigma_fst_eq a)
  have h2 := measurableSet_coarseSigma_of_pair T s n _ (measurableSet_freeSupports T s n
    (fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n => p.2.2.1) (fun p => p.2.2.2) (fun p => p.1.2.1)
    hV hb hY
    (fun F => ∀ κ' ∈ S, ∃ θ ∈ F, IsLongWithin ℓ.side (stageRange T s) (windowLength T K s) θ
      (sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T K s) (C κ')))))
  have e : {v : MarkedSample ℓ (s + 1) n | ∀ κ' ∈ S, HasLongSupport T K s (s + 1) n v (C κ')} =
      {u : MarkedSample ℓ (s + 1) n | (stageState T s (n * ℓ.side) u.1, u.2) ∈
        {p : StageState T s (n * ℓ.side) × StepOutcome ℓ n | ∀ κ' ∈ S, ∃ θ ∈ freeSupports (T.stage s).toStepSetup
          (hotCoreSites (T.stage s).toStepSetup p.2.2.1) p.2.2.2 p.1.2.1,
            IsLongWithin ℓ.side (stageRange T s) (windowLength T K s) θ
              (sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T K s) (C κ')))}} := by
    ext v
    exact forall₂_congr fun κ' _ => hasLongSupport_self_iff T K s n v (C κ')
  rw [e]
  exact MeasurableSet.inter h1 h2
variable (β : ℝ)
private theorem bound_prod_of_stages (hA : ResponseInTheExpansion.CoarseStateMeasurable)
    (hq : ∀ (s n : ℕ) [NeZero n], Measurable (stageState T s n)) (K : ℕ)
    (up : ∀ s, s < K → ∀ (n : ℕ) [NeZero n] (E : Set (MarkedSample ℓ s (fineSide ℓ.side 1 n))) (c : ENNReal),
      MeasurableSet E →
      (∀ A', MeasurableSet[stageSigma T s (fineSide ℓ.side 1 n)] A' →
        markedSampleLaw T β s (fineSide ℓ.side 1 n) (A' ∩ E) ≤ c * markedSampleLaw T β s (fineSide ℓ.side 1 n) A') →
      ∀ B, MeasurableSet[coarseSigma T s 1 n] B →
        markedSampleLaw T β (s + 1) n (B ∩ {u | ResponseInTheExpansion.sampleBelow ℓ s 1 n u ∈ E}) ≤
          c * markedSampleLaw T β (s + 1) n B)
    {ι : Type} (S : ℕ → Finset ι) (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (s : ℕ) :
    s ≤ K → ∀ (n : ℕ) [NeZero n] (C : ι → Finset (TorusSite n)),
      (∀ j d, j + 1 + d = s → ∀ A, MeasurableSet[stageSigma T (j + 1) (fineSide ℓ.side d n)] A →
        markedSampleLaw T β (j + 1) (fineSide ℓ.side d n)
            (A ∩ {v | ∀ κ' ∈ S j, HasLongSupport T K j (j + 1) _ v (cellBelow ℓ.side d n (C κ'))}) ≤
          ENNReal.ofReal (p j) * markedSampleLaw T β (j + 1) (fineSide ℓ.side d n) A) →
      ∀ A, MeasurableSet[stageSigma T s n] A →
        markedSampleLaw T β s n (A ∩ {u | ∀ j < s, ∀ κ' ∈ S j, HasLongSupport T K j s n u (C κ')}) ≤
          ENNReal.ofReal (∏ j ∈ Finset.range s, p j) * markedSampleLaw T β s n A := by
  induction s with
  | zero =>
    intro _ n _ C _ A _
    simp only [Finset.range_zero, Finset.prod_empty, ENNReal.ofReal_one, one_mul]
    exact measure_mono Set.inter_subset_left
  | succ s ih =>
    intro hs n _ C rare A hAm
    let E : Set (MarkedSample ℓ s (n * ℓ.side)) :=
      {w | ∀ j < s, ∀ κ' ∈ S j, HasLongSupport T K j s (n * ℓ.side) w (sitesInBlocks ℓ.side (C κ'))}
    have hE : MeasurableSet E := by
      have e : E = ⋂ j ∈ Finset.range s, ⋂ κ' ∈ S j,
          {w | HasLongSupport T K j s (n * ℓ.side) w (sitesInBlocks ℓ.side (C κ'))} := by
        ext w
        simp [E]
      rw [e]
      exact Finset.measurableSet_biInter _ fun j _ => Finset.measurableSet_biInter _ fun κ' _ =>
        measurableSet_hasLongSupport T hq K j s (n * ℓ.side) _
    have below := ih (by omega) (n * ℓ.side) (fun κ' => sitesInBlocks ℓ.side (C κ'))
      (fun j d h => rare j (d + 1) (by omega))
    have hB := measurableSet_state_inter_long T hA K s n (S s) C A hAm
    have hU := up s (by omega) n E _ hE below _ hB
    have hR : markedSampleLaw T β (s + 1) n (A ∩ {v | ∀ κ' ∈ S s, HasLongSupport T K s (s + 1) n v (C κ')}) ≤
        ENNReal.ofReal (p s) * markedSampleLaw T β (s + 1) n A := rare s 0 (by omega) A hAm
    have hsub : A ∩ {u | ∀ j < s + 1, ∀ κ' ∈ S j, HasLongSupport T K j (s + 1) n u (C κ')} ⊆
        (A ∩ {v | ∀ κ' ∈ S s, HasLongSupport T K s (s + 1) n v (C κ')}) ∩
          {u | ResponseInTheExpansion.sampleBelow ℓ s 1 n u ∈ E} := by
      rintro u ⟨hu, hl⟩
      refine ⟨⟨hu, fun κ' hκ => hl s (by omega) κ' hκ⟩, ?_⟩
      intro j hj κ' hκ
      rcases (hasLongSupport_succ_iff T K j s n u (C κ')).1 (hl j (by omega) κ' hκ) with ⟨h1, _⟩ | h
      · omega
      · exact h
    calc markedSampleLaw T β (s + 1) n
          (A ∩ {u | ∀ j < s + 1, ∀ κ' ∈ S j, HasLongSupport T K j (s + 1) n u (C κ')})
        ≤ markedSampleLaw T β (s + 1) n
            ((A ∩ {v | ∀ κ' ∈ S s, HasLongSupport T K s (s + 1) n v (C κ')}) ∩
              {u | ResponseInTheExpansion.sampleBelow ℓ s 1 n u ∈ E}) :=
          measure_mono hsub
      _ ≤ ENNReal.ofReal (∏ j ∈ Finset.range s, p j) *
            markedSampleLaw T β (s + 1) n (A ∩ {v | ∀ κ' ∈ S s, HasLongSupport T K s (s + 1) n v (C κ')}) := hU
      _ ≤ ENNReal.ofReal (∏ j ∈ Finset.range s, p j) *
            (ENNReal.ofReal (p s) * markedSampleLaw T β (s + 1) n A) := by
          gcongr
      _ = ENNReal.ofReal (∏ j ∈ Finset.range (s + 1), p j) * markedSampleLaw T β (s + 1) n A := by
          rw [Finset.prod_range_succ, ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => hp j), mul_assoc]
end Samples
private theorem isTowerOnParametersMeasurable_mono {Tb : ParameterAssignment} {y : ℝ} {T : StageTower (Tb.stepParameters y)}
    {β : ℝ} {k k' : ℕ} (h : IsTowerAtParametersMeasurable Tb y T β k) (hk : k' ≤ k) :
    IsTowerAtParametersMeasurable Tb y T β k' :=
  ⟨⟨h.onFamily.startsAtWilson, fun j hj => h.onFamily.coupling_eq j (by omega),
    fun j hj => h.onFamily.onFamily j (by omega)⟩, h.measurable⟩
theorem longSupportsAllStagesBound (h₁ : longSupportsConditionalBoundStatement)
    (h₂ : conditionalBoundLiftsStatement) (h₃ : ResponseInTheExpansion.CoarseStateMeasurable)
    (h₄ : ResponseInTheExpansion.StageStatesMeasurableStatement) :
    longSupportsAllStagesBoundStatement := by
  intro a ha
  obtain ⟨L₁, r₁, hr₁, H₁⟩ := h₁ a ha
  obtain ⟨L₂, r₂, hr₂, H₂⟩ := h₂ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hLodd hL Tb hTa hTL hDr hrt
  obtain ⟨y₁, G₁⟩ := H₁ L hLodd (le_trans (le_max_left _ _) hL) Tb hTa hTL hDr (le_trans hrt (min_le_left _ _))
  obtain ⟨y₂, G₂⟩ := H₂ L hLodd (le_trans (le_max_right _ _) hL) Tb hTa hTL hDr (le_trans hrt (min_le_right _ _))
  refine ⟨max (max y₁ y₂) Tb.floorMin, ?_⟩
  intro y hy hrow hwil
  have hy₁ : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hy₂ : y₂ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hadm : (Tb.stepParameters y).Admissible := hDr.fits y (le_trans (le_max_right _ _) hy)
  have P₁ := G₁ y hy₁ hrow hwil
  have P₂ := G₂ y hy₂ hrow hwil
  intro T β k hrun e G κ S hside hle hS A hA
  refine bound_prod_of_stages T β h₃ (fun s n _ => h₄ _ hadm T s n) k
    (fun s hs n _ E c hE hb B hB => P₂ T β s 1 (isTowerOnParametersMeasurable_mono hrun hs) n E c hE hb B hB) S
    (fun j => Real.exp (-(8 * Tb.gasRate * (T.stage j).coupling * (100 * ((k : ℝ) - j)) * (S j).card)))
    (fun j => (Real.exp_pos _).le) k le_rfl _ (fun κ' => G.cell (2 * (Tb.stepParameters y).side ^ e) κ') ?_ A hA
  intro j d hjd A' hA'
  subst hjd
  have hc : (((j + 1 + d : ℕ) : ℝ) - j) = (d : ℝ) + 1 := by
    push_cast
    ring
  have := P₁ T β j d hrun e G κ (S j) hside hle (hS j (by omega)) A' hA'
  rw [hc]
  exact this
end YangMills.Construction.CellWindows
end
