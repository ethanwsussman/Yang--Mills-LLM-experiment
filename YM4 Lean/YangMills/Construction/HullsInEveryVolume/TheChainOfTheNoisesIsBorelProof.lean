import YangMills.Construction.CellOfTheFlow.TheDrawOfTheNoiseIsBorelProof
import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsAreTheGasProof
import YangMills.Construction.HullsInEveryVolume.TheChainOfTheNoisesIsBorel
import YangMills.Construction.ResponseInTheExpansion.WhatTheChainReadsIsBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullsInEveryVolume
open StepSettings TorusFields TorusLumps WeightedResponses ChainNoise ResponseInTheExpansion
namespace NoiseChain
private theorem measurable_of_countable_fibres {X D Z : Type} [MeasurableSpace X] [Countable D] [MeasurableSpace Z]
    (f : X → D) (hf : ∀ d, MeasurableSet {x | f x = d}) (G : D → X → Z) (hG : ∀ d, Measurable (G d)) :
    Measurable fun x => G (f x) x := by apply _root_.YangMills.SharedProofs.p26930 <;> assumption
private theorem measurableSet_filter_eq {X α : Type} [MeasurableSpace X] (s : Finset α) (c : α → X → Prop)
    (hc : ∀ b, MeasurableSet {x | c b x}) (inst : ∀ x, DecidablePred fun b => c b x) (A : Finset α) :
    MeasurableSet {x | s.filter (fun b => c b x) = A} := by apply _root_.YangMills.SharedProofs.p36363 <;> assumption
private theorem sum_powerset_prod_ite {α : Type} [DecidableEq α] (M : Finset α) (m : α → ℝ) :
    ∑ t ∈ M.powerset, ∏ b ∈ M, (if b ∈ t then 1 - m b else m b) = 1 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdGasIdentity.sum_powerset_prod_complement_eq_one <;> assumption
variable {n : ℕ} [NeZero n]
private theorem bondMark_eq_sum_markLaw {R : StepSetup} (hLn : R.params.side ∣ n) (n64 : 64 ≤ n)
    {C : Finset (TorusSite n)} {b : TorusBond (n * R.params.side)} (hb : b ∈ markedBonds R C)
    {V : TorusField n} (hV : hotCoreSites R V = C) (W : TorusField (n * R.params.side)) :
    bondMark R V W b = ∑ t ∈ ((markedBonds R C).erase b).powerset, markLaw R W V t := by
  classical
  have e : ∀ t ∈ ((markedBonds R C).erase b).powerset, markLaw R W V t =
      bondMark R V W b * ∏ b' ∈ (markedBonds R C).erase b,
        (if b' ∈ t then 1 - bondMark R V W b' else bondMark R V W b') := by
    intro t ht
    have hts : t ⊆ (markedBonds R C).erase b := Finset.mem_powerset.mp ht
    have hbt : b ∉ t := fun h => (Finset.mem_erase.mp (hts h)).1 rfl
    have hsub : t ⊆ markedBonds R C := hts.trans (Finset.erase_subset _ _)
    unfold markLaw
    rw [if_pos ⟨hLn, n64⟩, hV, if_pos hsub]
    unfold markProduct
    rw [← Finset.mul_prod_erase _ _ hb]
    simp only [if_neg hbt]
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, sum_powerset_prod_ite, mul_one]
variable {ℓ : StepParameters}
open Classical in
private def failedBonds (R : StepSetup) (W : TorusField (n * R.params.side)) (V : TorusField n)
    (U : TorusBond (n * R.params.side) → unitInterval) : BondSet (n * R.params.side) :=
  (markedBonds R (hotCoreSites R V)).filter fun b => ¬ ((U b : ℝ) < bondMark R V W b)
private theorem measurable_failedBonds {R : StepSetup}
    (hot : ∀ a : Finset (TorusSite n), MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (hco : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (hLn : R.params.side ∣ n) (n64 : 64 ≤ n) {X : Type} [MeasurableSpace X]
    {W : X → TorusField (n * R.params.side)} (hW : Measurable W)
    {V : X → TorusField n} (hV : Measurable V) {U : X → TorusBond (n * R.params.side) → unitInterval}
    (hU : Measurable U) :
    Measurable fun x => failedBonds R (W x) (V x) (U x) := by
  classical
  have hp : Measurable fun x => (W x, V x) := hW.prodMk hV
  have hs : ∀ t : Finset (TorusBond (n * R.params.side)), Measurable fun x => markLaw R (W x) (V x) t := fun t => by
    have h := (hco t).comp hp
    exact h
  have hUb : ∀ b, Measurable fun x => ((U x b : unitInterval) : ℝ) := fun b =>
    measurable_subtype_coe.comp ((measurable_pi_apply b).comp hU)
  let G : Finset (TorusSite n) → X → BondSet (n * R.params.side) := fun C x =>
    (markedBonds R C).filter fun b =>
      ¬ (((U x b : unitInterval) : ℝ) < ∑ t ∈ ((markedBonds R C).erase b).powerset, markLaw R (W x) (V x) t)
  have : Countable (BondSet (n * R.params.side)) :=
    inferInstanceAs (Countable (Finset (TorusBond (n * R.params.side))))
  have hG : ∀ C, Measurable (G C) := by
    intro C
    refine measurable_to_countable' fun a => ?_
    have h1 : ∀ b, Measurable fun x =>
        ∑ t ∈ ((markedBonds R C).erase b).powerset, markLaw R (W x) (V x) t := fun b =>
      Finset.measurable_fun_sum _ fun t _ => hs t
    exact measurableSet_filter_eq (markedBonds R C)
      (fun b x => ¬ (((U x b : unitInterval) : ℝ) <
        ∑ t ∈ ((markedBonds R C).erase b).powerset, markLaw R (W x) (V x) t))
      (fun b => (measurableSet_lt (hUb b) (h1 b)).compl) _ a
  have e : (fun x => failedBonds R (W x) (V x) (U x)) = fun x => G (hotCoreSites R (V x)) x := by
    funext x
    show (markedBonds R (hotCoreSites R (V x))).filter _ = (markedBonds R (hotCoreSites R (V x))).filter _
    refine Finset.filter_congr fun b hb => ?_
    rw [bondMark_eq_sum_markLaw hLn n64 hb rfl]
  rw [e]
  exact measurable_of_countable_fibres (fun x => hotCoreSites R (V x)) (fun C => hV (hot C)) G hG
private theorem measurable_baseOffsets (T : StageTower ℓ) (rule : NoiseRule ℓ) (hrule : rule.IsAdmissible T) (s : ℕ)
    {X : Type} [MeasurableSpace X] {W : X → TorusField (n * ℓ.side)} (hW : Measurable W)
    {ξ : X → TorusSite n → unitInterval} (hξ : Measurable ξ) :
    Measurable fun x => (fun y => rule.base s n (W x) y (ξ x y) : TorusSite n → BlockOffset ℓ.side) :=
  measurable_pi_iff.2 fun y =>
    (hrule.base_measurable s n y).comp (hW.prodMk ((measurable_pi_apply y).comp hξ))
private theorem measurable_linkValues (T : StageTower ℓ) (rule : NoiseRule ℓ) (hrule : rule.IsAdmissible T) (s : ℕ)
    {X : Type} [MeasurableSpace X] {W : X → TorusField (n * ℓ.side)} (hW : Measurable W)
    {o : X → TorusSite n → BlockOffset ℓ.side} (hof : ∀ d, MeasurableSet {x | o x = d})
    {ξ : X → TorusBond n → unitInterval} (hξ : Measurable ξ) :
    Measurable fun x => (fun y i => rule.value s n (W x) (o x) (y, i) (ξ x (y, i)) : TorusField n) := by
  refine measurable_pi_iff.2 fun y => measurable_pi_iff.2 fun i => ?_
  refine measurable_of_countable_fibres o hof (fun d x => rule.value s n (W x) d (y, i) (ξ x (y, i))) fun d => ?_
  exact (hrule.value_measurable s n d (y, i)).comp (hW.prodMk ((measurable_pi_apply (y, i)).comp hξ))
private theorem measurable_stepOutcome (hot : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (T : StageTower ℓ) (rule : NoiseRule ℓ) (hco : T.MarksMeasurable) (hrule : rule.IsAdmissible T) (s : ℕ)
    (hLn : ℓ.side ∣ n) (n64 : 64 ≤ n) {X : Type} [MeasurableSpace X] {W : X → TorusField (n * ℓ.side)}
    (hW : Measurable W) {ξ : X → StepNoise ℓ n} (hξ : Measurable ξ) :
    Measurable fun x => rule.stepOutcome T s n (W x) (ξ x) := by
  have ho := measurable_baseOffsets T rule hrule s hW (measurable_fst.comp hξ)
  have hof : ∀ d, MeasurableSet
      {x | (fun y => rule.base s n (W x) y ((ξ x).1 y) : TorusSite n → BlockOffset ℓ.side) = d} :=
    fun d => ho (measurableSet_singleton d)
  have hB : Measurable fun x => baseChoiceOfOffsets (fun y => rule.base s n (W x) y ((ξ x).1 y)) :=
    measurable_of_countable_fibres _ hof (fun d _ => baseChoiceOfOffsets d) fun _ => measurable_const
  have hV := measurable_linkValues T rule hrule s hW hof (measurable_fst.comp (measurable_snd.comp hξ))
  have hbad := measurable_failedBonds (R := (T.stage s).toStepSetup) (hot _ n) (fun bad => hco s n bad) hLn n64 hW hV
    (measurable_snd.comp (measurable_snd.comp hξ))
  exact hB.prodMk (hV.prodMk hbad)
private theorem measurable_topField (ℓ : StepParameters) (s n : ℕ) : Measurable (topField ℓ s n) := by apply _root_.YangMills.SharedProofs.p12845 <;> assumption
end NoiseChain
open NoiseChain in
theorem noiseChainMeasurable (hWh : chainMeasurabilityStatement) :
    noiseChainMeasurableStatement := by
  intro ℓ _ T rule hco hrule s
  induction s with
  | zero =>
    intro n _ _ _
    exact measurable_fst
  | succ s ih =>
    intro n _ hLn n64
    letI := instMeasurableSpaceChainNoise ℓ s (n * ℓ.side)
    have hLpos : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne _)
    have h1 : Measurable fun p : TorusField (fineSide ℓ.side (s + 1) n) × ChainNoise.ChainNoise ℓ (s + 1) n =>
        rule.chain T s (n * ℓ.side) p.1 p.2.1 :=
      (ih (n * ℓ.side) (Dvd.intro_left _ rfl) (n64.trans (Nat.le_mul_of_pos_right _ hLpos))).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have h2 : Measurable fun p : TorusField (fineSide ℓ.side (s + 1) n) × ChainNoise.ChainNoise ℓ (s + 1) n =>
        (p.2.2 : StepNoise ℓ n) := measurable_snd.comp measurable_snd
    exact h1.prodMk (measurable_stepOutcome hWh.1 T rule hco hrule s hLn n64
      ((measurable_topField ℓ s (n * ℓ.side)).comp h1) h2)
end YangMills.Construction.HullsInEveryVolume
end
