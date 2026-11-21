import YangMills.Construction.CellOfTheFlow.LongClassesAtAllLevelsProof
import YangMills.Construction.CellOfTheFlow.TheCellEventReadsItsCellProof
import YangMills.Construction.FreeEnergiesOfTheFlow.CompletedObservablesAreBoundedProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped unitInterval
namespace YangMills.Construction
open TorusFields StepSettings TorusLumps StepCosts RenormalizationStepParameters WeightedResponses BlockAverages LumpContours
namespace CellWindows
namespace SampleChainMeasurability
private theorem measurable_of_measurableSet_fiber {X D Z : Type} [MeasurableSpace X] [Countable D] [MeasurableSpace Z]
    (f : X → D) (hf : ∀ d, MeasurableSet {x | f x = d}) (G : D → X → Z) (hG : ∀ d, Measurable (G d)) :
    Measurable fun x => G (f x) x := by
  intro s hs
  have hpre : (fun x => G (f x) x) ⁻¹' s = ⋃ d, {x | f x = d} ∩ (G d) ⁻¹' s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨f x, rfl, h⟩
    · rintro ⟨d, rfl, h⟩
      exact h
  rw [hpre]
  exact MeasurableSet.iUnion fun d => (hf d).inter (hG d hs)
abbrev _root_.YangMills.SharedProofs.p26930 := @measurable_of_measurableSet_fiber
private theorem measurableSet_setOf_filter_eq {X α : Type} [MeasurableSpace X] (s : Finset α) (c : α → X → Prop)
    (hc : ∀ p, MeasurableSet {x | c p x}) (inst : ∀ x, DecidablePred fun p => c p x) (A : Finset α) :
    MeasurableSet {x | s.filter (fun p => c p x) = A} := by apply _root_.YangMills.SharedProofs.p36363 <;> assumption
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem sum_powerset_prod_ite_eq_one {α : Type} [DecidableEq α] (M : Finset α) (m : α → ℝ)
    (P : Finset α → α → Prop) [∀ t a, Decidable (P t a)] (hP : ∀ t a, P t a ↔ a ∈ t) :
    ∑ t ∈ M.powerset, ∏ b ∈ M, (if P t b then 1 - m b else m b) = 1 := by
  have h := Finset.prod_add (fun b => 1 - m b) m M
  simp only [sub_add_cancel, Finset.prod_const_one] at h
  refine (Finset.sum_congr rfl fun t ht => ?_).trans h.symm
  have hts : t ⊆ M := Finset.mem_powerset.mp ht
  rw [← Finset.prod_sdiff hts, mul_comm]
  congr 1
  · exact Finset.prod_congr rfl fun b hb => by simp [hP, hb]
  · refine Finset.prod_congr rfl fun b hb => ?_
    have : ¬ P t b := by rw [hP]; exact (Finset.mem_sdiff.mp hb).2
    simp [this]
private theorem bondMark_eq_sum_markLaw (hdvd : R.params.side ∣ n) (hn : 64 ≤ n) {C : Finset (TorusSite n)}
    {b : TorusBond (n * R.params.side)} (hb : b ∈ markedBonds R C) {V : TorusField n} (hV : hotCoreSites R V = C)
    (W : TorusField (n * R.params.side)) :
    bondMark R V W b = ∑ t ∈ ((markedBonds R C).erase b).powerset, markLaw R W V t := by
  classical
  have hterm : ∀ t ∈ ((markedBonds R C).erase b).powerset, markLaw R W V t =
      bondMark R V W b * ∏ b' ∈ (markedBonds R C).erase b,
        (if b' ∈ t then 1 - bondMark R V W b' else bondMark R V W b') := by
    intro t ht
    have hts : t ⊆ (markedBonds R C).erase b := Finset.mem_powerset.mp ht
    have hbt : b ∉ t := fun h => (Finset.mem_erase.mp (hts h)).1 rfl
    have hsub : t ⊆ markedBonds R C := hts.trans (Finset.erase_subset _ _)
    unfold markLaw
    rw [if_pos ⟨hdvd, hn⟩, hV, if_pos hsub]
    unfold markProduct
    rw [← Finset.mul_prod_erase _ _ hb]
    simp only [if_neg hbt]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    sum_powerset_prod_ite_eq_one _ (bondMark R V W) (fun t a => a ∈ t) (fun _ _ => Iff.rfl), mul_one]
abbrev _root_.YangMills.SharedProofs.p31262 := @bondMark_eq_sum_markLaw
private theorem measurableSet_hotCoreSites_eq (hadm : R.params.Admissible) (hdvd : R.params.side ∣ n)
    (C : Finset (TorusSite n)) : MeasurableSet {V : TorusField n | hotCoreSites R V = C} := by apply _root_.YangMills.SharedProofs.p8979 <;> assumption
private theorem measurable_markedBadBonds {X : Type} [MeasurableSpace X] (hadm : R.params.Admissible)
    (hdvd : R.params.side ∣ n) (hn : 64 ≤ n)
    (hlaw : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    {W : X → TorusField (n * R.params.side)} (hW : Measurable W) {V : X → TorusField n} (hV : Measurable V)
    {ξ : X → StepNoise R.params n} (hξ : Measurable ξ) :
    Measurable fun x => markedBadBonds R (W x) (V x) (ξ x) := by
  classical
  have : Countable (BondSet (n * R.params.side)) :=
    inferInstanceAs (Countable (Finset (TorusBond (n * R.params.side))))
  have hp : Measurable fun x => (W x, V x) := hW.prodMk hV
  have hs : ∀ t : Finset (TorusBond (n * R.params.side)), Measurable fun x => markLaw R (W x) (V x) t := fun t => by
    have h := (hlaw t).comp hp
    exact h
  have hξ2 : Measurable fun x => (ξ x).2.2 := measurable_snd.comp (measurable_snd.comp hξ)
  let G : Finset (TorusSite n) → X → BondSet (n * R.params.side) := fun C x =>
    (markedBonds R C).filter fun b =>
      (∑ t ∈ ((markedBonds R C).erase b).powerset, markLaw R (W x) (V x) t) < ((ξ x).2.2 b : ℝ)
  have hG : ∀ C, Measurable (G C) := by
    intro C
    refine measurable_to_countable' fun a => ?_
    have h1 : ∀ b, Measurable fun x =>
        ∑ t ∈ ((markedBonds R C).erase b).powerset, markLaw R (W x) (V x) t := fun b =>
      Finset.measurable_sum _ fun t _ => hs t
    have h2 : ∀ b, Measurable fun x => (((ξ x).2.2 b : I) : ℝ) := fun b =>
      measurable_subtype_coe.comp ((measurable_pi_apply b).comp hξ2)
    exact measurableSet_setOf_filter_eq (markedBonds R C)
      (fun b x => (∑ t ∈ ((markedBonds R C).erase b).powerset, markLaw R (W x) (V x) t) < (((ξ x).2.2 b : I) : ℝ))
      (fun b => measurableSet_lt (h1 b) (h2 b)) _ a
  have hfun : (fun x => markedBadBonds R (W x) (V x) (ξ x)) = fun x => G (hotCoreSites R (V x)) x := by
    funext x
    show (markedBonds R (hotCoreSites R (V x))).filter _ = (markedBonds R (hotCoreSites R (V x))).filter _
    refine Finset.filter_congr fun b hb => ?_
    rw [bondMark_eq_sum_markLaw hdvd hn hb rfl]
  rw [hfun]
  exact measurable_of_measurableSet_fiber (fun x => hotCoreSites R (V x))
    (fun C => hV (measurableSet_hotCoreSites_eq hadm hdvd C)) G hG
variable {S : StepSampler R}
private theorem measurable_sampledBases {X : Type} [MeasurableSpace X] (hS : S.IsFaithful)
    {W : X → TorusField (n * R.params.side)} (hW : Measurable W) {ξ : X → StepNoise R.params n} (hξ : Measurable ξ) :
    Measurable fun x => S.sampledBases (W x) (ξ x) := by
  classical
  refine measurable_to_countable' fun b => ?_
  have hpre : (fun x => S.sampledBases (W x) (ξ x)) ⁻¹' {b} =
      ⋂ y, {x | S.sampleBase n (W x) (toTorusSite n y) ((ξ x).1 (toTorusSite n y)) = b y} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact funext_iff
  rw [hpre]
  refine MeasurableSet.iInter fun y => ?_
  have hm : Measurable fun x => S.sampleBase n (W x) (toTorusSite n y) ((ξ x).1 (toTorusSite n y)) :=
    (hS.measurable_base n (toTorusSite n y)).comp
      (hW.prodMk ((measurable_pi_apply (toTorusSite n y)).comp (measurable_fst.comp hξ)))
  exact hm (measurableSet_singleton (b y))
private theorem measurable_sampledField {X : Type} [MeasurableSpace X] (hS : S.IsFaithful)
    {W : X → TorusField (n * R.params.side)} (hW : Measurable W) {B : X → BaseChoice R.params.side n}
    (hB : Measurable B) {ξ : X → StepNoise R.params n} (hξ : Measurable ξ) :
    Measurable fun x => S.sampledField (W x) (B x) (ξ x) := by
  refine measurable_pi_iff.2 fun z => measurable_pi_iff.2 fun i => ?_
  exact (hS.measurable_link n (z, i)).comp (hW.prodMk (hB.prodMk
    ((measurable_pi_apply (z, i)).comp (measurable_fst.comp (measurable_snd.comp hξ)))))
private theorem measurable_sample {X : Type} [MeasurableSpace X] (hadm : R.params.Admissible)
    (hdvd : R.params.side ∣ n) (hn : 64 ≤ n)
    (hlaw : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (hS : S.IsFaithful) {W : X → TorusField (n * R.params.side)} (hW : Measurable W)
    {ξ : X → StepNoise R.params n} (hξ : Measurable ξ) :
    Measurable fun x => S.sample (W x) (ξ x) := by
  have hB := measurable_sampledBases hS hW hξ
  have hV := measurable_sampledField hS hW hB hξ
  exact hB.prodMk (hV.prodMk (measurable_markedBadBonds hadm hdvd hn hlaw hW hV hξ))
private theorem measurable_topField (ℓ : StepParameters) (s n : ℕ) : Measurable (topField ℓ s n) := by apply _root_.YangMills.SharedProofs.p12845 <;> assumption
end SampleChainMeasurability
open SampleChainMeasurability in
theorem sampleChain_measurable : sampleChainMeasurableStatement := by
  intro ℓ hadm T S hlaw hS s
  induction s with
  | zero =>
    intro n _ _ _
    exact measurable_fst
  | succ s ih =>
    intro n _ hdvd hn
    have hside : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne _)
    have h1 : Measurable fun p : TorusField (fineSide ℓ.side (s + 1) n) × ChainNoise ℓ (s + 1) n =>
        sampleChain T S s (n * ℓ.side) p.1 p.2.1 :=
      (ih (n * ℓ.side) (Dvd.intro_left _ rfl) (hn.trans (Nat.le_mul_of_pos_right _ hside))).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have h2 : Measurable fun p : TorusField (fineSide ℓ.side (s + 1) n) × ChainNoise ℓ (s + 1) n =>
        (p.2.2 : StepNoise ℓ n) := measurable_snd.comp measurable_snd
    exact h1.prodMk (measurable_sample (R := (T.stage s).toStepSetup) hadm hdvd hn (fun bad => hlaw s n bad) (hS s)
      ((measurable_topField ℓ s (n * ℓ.side)).comp h1) h2)
end CellWindows
end YangMills.Construction
end
