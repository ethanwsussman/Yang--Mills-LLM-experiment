import YangMills.Construction.CellOfTheFlow.ACellIsRareProof
import YangMills.Construction.CellOfTheFlow.AFalseSiteHoldsALongClass
import YangMills.Construction.CellOfTheFlow.HullsThatMeetCellsAreRare
import YangMills.Construction.CellOfTheFlow.LongClassesAtAllLevels
import YangMills.Construction.CellOfTheFlow.PricesOfLongClassesAddUp
import YangMills.Construction.CellOfTheFlow.TranslationsCarryTheMeansOfACell
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped unitInterval
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps WeightedResponses RenormalizationStepParameters StepReturn StepSettings
private def IsMixingMap {X : Type*} [MeasurableSpace X] (μ : Measure X) (m : X → X → X) : Prop :=
  Measurable (fun p : X × X => m p.1 p.2) ∧ Measure.map (fun p : X × X => m p.1 p.2) (μ.prod μ) = μ
private lemma prod_prod_apply_interleave {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] {A : Set (X × X)} {B : Set (Y × Y)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (μ.prod ν).prod (μ.prod ν) {p | (p.1.1, p.2.1) ∈ A ∧ (p.1.2, p.2.2) ∈ B} =
      μ.prod μ A * ν.prod ν B := by
  have hset : MeasurableSet {p : (X × Y) × (X × Y) | (p.1.1, p.2.1) ∈ A ∧ (p.1.2, p.2.2) ∈ B} :=
    ((by fun_prop : Measurable fun p : (X × Y) × (X × Y) => (p.1.1, p.2.1)) hA).inter
      ((by fun_prop : Measurable fun p : (X × Y) × (X × Y) => (p.1.2, p.2.2)) hB)
  rw [Measure.prod_apply hset, Measure.prod_apply hA, Measure.prod_apply hB]
  have hsec : ∀ x : X × Y,
      (Prod.mk x ⁻¹' {p : (X × Y) × (X × Y) | (p.1.1, p.2.1) ∈ A ∧ (p.1.2, p.2.2) ∈ B}) =
        (Prod.mk x.1 ⁻¹' A) ×ˢ (Prod.mk x.2 ⁻¹' B) := by
    intro x; ext y; simp [Set.mem_prod]
  simp_rw [hsec, Measure.prod_prod]
  have hmA : Measurable fun x : X => μ (Prod.mk x ⁻¹' A) := measurable_measure_prodMk_left hA
  have hmB : Measurable fun x : Y => ν (Prod.mk x ⁻¹' B) := measurable_measure_prodMk_left hB
  have hm' : Measurable (fun x : X × Y => μ (Prod.mk x.1 ⁻¹' A) * ν (Prod.mk x.2 ⁻¹' B)) :=
    (hmA.comp measurable_fst).mul (hmB.comp measurable_snd)
  rw [lintegral_prod _ hm'.aemeasurable]
  simp_rw [lintegral_const_mul _ hmB]
  rw [lintegral_mul_const _ hmA]
private lemma IsMixingMap.prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {m₁ : X → X → X} {m₂ : Y → Y → Y}
    (h₁ : IsMixingMap μ m₁) (h₂ : IsMixingMap ν m₂) :
    IsMixingMap (μ.prod ν) (fun a b => (m₁ a.1 b.1, m₂ a.2 b.2)) := by
  have hm : Measurable (fun p : (X × Y) × (X × Y) => (m₁ p.1.1 p.2.1, m₂ p.1.2 p.2.2)) :=
    (h₁.1.comp (by fun_prop : Measurable fun p : (X × Y) × (X × Y) => (p.1.1, p.2.1))).prodMk
      (h₂.1.comp (by fun_prop : Measurable fun p : (X × Y) × (X × Y) => (p.1.2, p.2.2)))
  refine ⟨hm, ?_⟩
  symm
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [Measure.map_apply hm (hs.prod ht)]
  have hpre : (fun p : (X × Y) × (X × Y) => (m₁ p.1.1 p.2.1, m₂ p.1.2 p.2.2)) ⁻¹' (s ×ˢ t) =
      {p | (p.1.1, p.2.1) ∈ (fun q : X × X => m₁ q.1 q.2) ⁻¹' s ∧
        (p.1.2, p.2.2) ∈ (fun q : Y × Y => m₂ q.1 q.2) ⁻¹' t} := rfl
  rw [hpre, prod_prod_apply_interleave μ ν (h₁.1 hs) (h₂.1 ht), ← Measure.map_apply h₁.1 hs,
    ← Measure.map_apply h₂.1 ht, h₁.2, h₂.2]
private lemma isMixingMap_pi_ite {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] :
    IsMixingMap (Measure.pi fun _ : ι => (volume : Measure I)) (fun f g i => if P i then f i else g i) := by
  have hm : Measurable (fun p : (ι → I) × (ι → I) => fun i => if P i then p.1 i else p.2 i) := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases h : P i
    · simp only [if_pos h]; exact (measurable_pi_apply i).comp measurable_fst
    · simp only [if_neg h]; exact (measurable_pi_apply i).comp measurable_snd
  refine ⟨hm, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → I) × (ι → I) => fun i => if P i then p.1 i else p.2 i) ⁻¹' (Set.pi Set.univ s) =
      (Set.pi Set.univ fun i => if P i then s i else Set.univ) ×ˢ
        (Set.pi Set.univ fun i => if P i then Set.univ else s i) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : P i
        · simpa [hi] using h i
        · simp [hi]
      · by_cases hi : P i
        · simp [hi]
        · simpa [hi] using h i
    · rintro ⟨h₁, h₂⟩ i
      by_cases hi : P i
      · simpa [hi] using h₁ i
      · simpa [hi] using h₂ i
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : P i <;> simp [hi]
private lemma isProbabilityMeasure_stepNoiseMeasure (ℓ : StepParameters) (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (stepNoiseMeasure ℓ n) := by
  unfold stepNoiseMeasure; infer_instance
private lemma isProbabilityMeasure_chainNoiseMeasure (ℓ : StepParameters) (s : ℕ) :
    ∀ (n : ℕ) [NeZero n], IsProbabilityMeasure (chainNoiseMeasure ℓ s n) := by
  induction s with
  | zero => intro n _; unfold chainNoiseMeasure; exact Measure.dirac.isProbabilityMeasure
  | succ s ih =>
    intro n _
    have := ih (n * ℓ.side)
    have := isProbabilityMeasure_stepNoiseMeasure ℓ n
    let _ := instMeasurableSpaceChainNoise ℓ s (n * ℓ.side)
    exact show IsProbabilityMeasure ((chainNoiseMeasure ℓ s (n * ℓ.side)).prod (stepNoiseMeasure ℓ n)) from inferInstance
abbrev _root_.YangMills.SharedProofs.p9681 := @isProbabilityMeasure_chainNoiseMeasure
open Classical in
private def mixStepNoise (ℓ : StepParameters) {n : ℕ} [NeZero n] (c : Finset (TorusSite n))
    (a b : StepNoise ℓ n) : StepNoise ℓ n :=
  (fun y => if y ∈ c then a.1 y else b.1 y,
    fun d => if d.1 ∈ c then a.2.1 d else b.2.1 d,
    fun d => if d.1 ∈ sitesInBlocks ℓ.side c then a.2.2 d else b.2.2 d)
private def mixChainNoise (ℓ : StepParameters) : (s n : ℕ) → [NeZero n] → Finset (TorusSite n) →
    ChainNoise ℓ s n → ChainNoise ℓ s n → ChainNoise ℓ s n
  | 0, _, _, _, _, _ => ()
  | s + 1, n, _, c, ξ, η =>
    (mixChainNoise ℓ s (n * ℓ.side) (sitesInBlocks ℓ.side c) ξ.1 η.1, mixStepNoise ℓ c ξ.2 η.2)
private lemma isMixingMap_mixStepNoise (ℓ : StepParameters) {n : ℕ} [NeZero n] (c : Finset (TorusSite n)) :
    IsMixingMap (stepNoiseMeasure ℓ n) (mixStepNoise ℓ c) := by
  exact (isMixingMap_pi_ite fun y : TorusSite n => y ∈ c).prod
    ((isMixingMap_pi_ite fun d : TorusBond n => d.1 ∈ c).prod
      (isMixingMap_pi_ite fun d : TorusBond (n * ℓ.side) => d.1 ∈ sitesInBlocks ℓ.side c))
private lemma isMixingMap_mixChainNoise (ℓ : StepParameters) (s : ℕ) :
    ∀ (n : ℕ) [NeZero n] (c : Finset (TorusSite n)),
    IsMixingMap (chainNoiseMeasure ℓ s n) (mixChainNoise ℓ s n c) := by
  induction s with
  | zero =>
    intro n _ c
    refine ⟨measurable_const, ?_⟩
    have := isProbabilityMeasure_chainNoiseMeasure ℓ 0 n
    have h : IsProbabilityMeasure ((chainNoiseMeasure ℓ 0 n).prod (chainNoiseMeasure ℓ 0 n)) := inferInstance
    change Measure.map (fun _ => ()) _ = _
    rw [Measure.map_const, measure_univ, one_smul]
    rfl
  | succ s ih =>
    intro n _ c
    let _ := instMeasurableSpaceChainNoise ℓ s (n * ℓ.side)
    have := isProbabilityMeasure_chainNoiseMeasure ℓ s (n * ℓ.side)
    have := isProbabilityMeasure_stepNoiseMeasure ℓ n
    exact (ih (n * ℓ.side) (sitesInBlocks ℓ.side c)).prod (isMixingMap_mixStepNoise ℓ c)
private lemma noiseAgreesOn_refl (ℓ : StepParameters) (s : ℕ) :
    ∀ (n : ℕ) [NeZero n] (c : Finset (TorusSite n)) (ξ : ChainNoise ℓ s n), NoiseAgreesOn ℓ s n c ξ ξ := by
  induction s with
  | zero => intro n _ c ξ; trivial
  | succ s ih =>
    intro n _ c ξ
    exact ⟨ih _ _ _, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
private lemma mixChainNoise_agrees_left (ℓ : StepParameters) (s : ℕ) :
    ∀ (n : ℕ) [NeZero n] (c : Finset (TorusSite n)) (ξ η : ChainNoise ℓ s n),
    NoiseAgreesOn ℓ s n c (mixChainNoise ℓ s n c ξ η) ξ := by
  induction s with
  | zero => intro n _ c ξ η; trivial
  | succ s ih =>
    intro n _ c ξ η
    refine ⟨ih _ _ _ _, fun y hy => ?_, fun b hb _ => ?_, fun b hb _ => ?_⟩
    · simp [mixChainNoise, mixStepNoise, hy]
    · simp [mixChainNoise, mixStepNoise, hb]
    · simp [mixChainNoise, mixStepNoise, hb]
private lemma sitesInBlocks_disjoint {n L : ℕ} [NeZero n] [NeZero L] {c c' : Finset (TorusSite n)}
    (h : Disjoint c c') : Disjoint (sitesInBlocks L c) (sitesInBlocks L c') := by
  rw [Finset.disjoint_left] at h ⊢
  intro x hx hx'
  simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  exact h hx hx'
private lemma mixChainNoise_agrees_right (ℓ : StepParameters) (s : ℕ) :
    ∀ (n : ℕ) [NeZero n] (c c' : Finset (TorusSite n)),
    Disjoint c c' → ∀ ξ η : ChainNoise ℓ s n, NoiseAgreesOn ℓ s n c' (mixChainNoise ℓ s n c ξ η) η := by
  induction s with
  | zero => intro n _ c c' _ ξ η; trivial
  | succ s ih =>
    intro n _ c c' hd ξ η
    refine ⟨ih _ _ _ (sitesInBlocks_disjoint hd) _ _, fun y hy => ?_, fun b hb _ => ?_, fun b hb _ => ?_⟩
    · simp [mixChainNoise, mixStepNoise, Finset.disjoint_right.mp hd hy]
    · simp [mixChainNoise, mixStepNoise, Finset.disjoint_right.mp hd hb]
    · simp [mixChainNoise, mixStepNoise, Finset.disjoint_right.mp (sitesInBlocks_disjoint (L := ℓ.side) hd) hb]
private lemma chainNoiseMeasure_inter_eq_mul (ℓ : StepParameters) (s n : ℕ) [NeZero n] {c : Finset (TorusSite n)}
    {E E' : Set (ChainNoise ℓ s n)} (hE : MeasurableSet E) (hE' : MeasurableSet E')
    (hr : ∀ ξ η, mixChainNoise ℓ s n c ξ η ∈ E ↔ ξ ∈ E) (hr' : ∀ ξ η, mixChainNoise ℓ s n c ξ η ∈ E' ↔ η ∈ E') :
    chainNoiseMeasure ℓ s n (E ∩ E') = chainNoiseMeasure ℓ s n E * chainNoiseMeasure ℓ s n E' := by
  have hm := isMixingMap_mixChainNoise ℓ s n c
  have := isProbabilityMeasure_chainNoiseMeasure ℓ s n
  conv_lhs => rw [← hm.2]
  rw [Measure.map_apply hm.1 (hE.inter hE')]
  have hpre : (fun p : ChainNoise ℓ s n × ChainNoise ℓ s n => mixChainNoise ℓ s n c p.1 p.2) ⁻¹' (E ∩ E') =
      E ×ˢ E' := by
    ext p
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, hr, hr']
  rw [hpre, Measure.prod_prod]
private lemma chainNoiseMeasure_biInter_eq_prod (ℓ : StepParameters) (s n : ℕ) [NeZero n] {ι : Type*}
    [DecidableEq ι] (A : Finset ι)
    (c : ι → Finset (TorusSite n)) (E : ι → Set (ChainNoise ℓ s n)) (hm : ∀ i ∈ A, MeasurableSet (E i))
    (hd : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (c i) (c j))
    (hr : ∀ i ∈ A, ∀ ξ ξ', NoiseAgreesOn ℓ s n (c i) ξ ξ' → (ξ ∈ E i ↔ ξ' ∈ E i)) :
    chainNoiseMeasure ℓ s n {ξ | ∀ i ∈ A, ξ ∈ E i} = ∏ i ∈ A, chainNoiseMeasure ℓ s n (E i) := by
  have := isProbabilityMeasure_chainNoiseMeasure ℓ s n
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    have hmA : MeasurableSet {ξ | ∀ i ∈ A, ξ ∈ E i} := by
      have : {ξ | ∀ i ∈ A, ξ ∈ E i} = ⋂ i ∈ A, E i := by ext ξ; simp
      rw [this]
      exact Finset.measurableSet_biInter _ fun i hi => hm i (Finset.mem_insert_of_mem hi)
    have hset : {ξ | ∀ i ∈ insert a A, ξ ∈ E i} = E a ∩ {ξ | ∀ i ∈ A, ξ ∈ E i} := by
      ext ξ; simp
    rw [hset, Finset.prod_insert ha, ← ih (fun i hi => hm i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      (fun i hi => hr i (Finset.mem_insert_of_mem hi))]
    refine chainNoiseMeasure_inter_eq_mul ℓ s n (c := c a) (hm a (Finset.mem_insert_self a A)) hmA ?_ ?_
    · intro ξ η
      exact (hr a (Finset.mem_insert_self a A) _ _ (mixChainNoise_agrees_left ℓ s n (c a) ξ η))
    · intro ξ η
      refine forall₂_congr fun i hi => ?_
      have hne : a ≠ i := fun h => ha (h ▸ hi)
      exact hr i (Finset.mem_insert_of_mem hi) _ _
        (mixChainNoise_agrees_right ℓ s n (c a) (c i)
          (hd a (Finset.mem_insert_self a A) i (Finset.mem_insert_of_mem hi) hne) ξ η)
section CellGeometry
private lemma cell_disjoint (G : CellGrid) (n : ℕ) [NeZero n] (hG : G.Compatible n) {κ κ' : Fin 4 → ℤ}
    (hκ : κ ∈ G.indices n) (hκ' : κ' ∈ G.indices n) (hne : κ ≠ κ') :
    Disjoint (G.cell n κ) (G.cell n κ') := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [CellGrid.cell, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  obtain ⟨h, hh, rfl⟩ := hx
  obtain ⟨h', hh', hxe⟩ := hx'
  apply hne
  obtain ⟨t, ht⟩ := hG.two_mul_side_dvd
  have hs : (0 : ℤ) < G.side := by exact_mod_cast hG.side_pos
  have hq : ((n / G.side : ℕ) : ℤ) = 2 * t := by
    have : n / G.side = 2 * t := by
      rw [ht, mul_assoc, mul_comm 2, mul_assoc, Nat.mul_div_cancel_left _ hG.side_pos]
      ring
    rw [this]; push_cast; ring
  have hn : (n : ℤ) = G.side * (2 * t) := by rw [ht]; push_cast; ring
  funext i
  have hκi := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hκ i)
  have hκi' := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hκ' i)
  rw [hq] at hκi hκi'
  have he := congrFun hxe i
  simp only [siteOfInt] at he
  have he' : ((G.side : ℤ) * κ i + h i : ℤ) % n = ((G.side : ℤ) * κ' i + h' i : ℤ) % n := by
    have : ((G.offset i + (G.side : ℤ) * κ i + h i : ℤ) : ZMod n) =
        ((G.offset i + (G.side : ℤ) * κ' i + h' i : ℤ) : ZMod n) := he
    have h2 := (ZMod.intCast_eq_intCast_iff' _ _ n).mp this
    have h3 : (G.offset i + ((G.side : ℤ) * κ i + h i)) % n = (G.offset i + ((G.side : ℤ) * κ' i + h' i)) % n := by
      simpa [add_assoc] using h2
    have h4 : Int.ModEq (n : ℤ) (G.offset i + ((G.side : ℤ) * κ i + h i))
        (G.offset i + ((G.side : ℤ) * κ' i + h' i)) := h3
    exact Int.ModEq.add_left_cancel' _ h4
  have hlt : ∀ a b : ℤ, 0 ≤ a → a < 2 * t → 0 ≤ b → b < G.side →
      0 ≤ (G.side : ℤ) * a + b ∧ (G.side : ℤ) * a + b < n := by
    intro a b ha ha' hb hb'
    refine ⟨by positivity, ?_⟩
    rw [hn]
    nlinarith
  have e₁ := hlt _ _ hκi.1 hκi.2 (hh i).1 (hh i).2
  have e₂ := hlt _ _ hκi'.1 hκi'.2 (hh' i).1 (hh' i).2
  rw [Int.emod_eq_of_lt e₁.1 e₁.2, Int.emod_eq_of_lt e₂.1 e₂.2] at he'
  have hb₁ := hh i
  have hb₂ := hh' i
  by_contra hne'
  rcases lt_or_gt_of_ne hne' with hlt' | hlt'
  · nlinarith
  · nlinarith
private lemma card_filter_parity_Ico (q : ℕ) (a : ℤ) :
    ((Finset.Ico (0 : ℤ) (2 * (q : ℤ))).filter fun t => (2 : ℤ) ∣ t - a).card = q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hI : Finset.Ico (0 : ℤ) (2 * ((q + 1 : ℕ) : ℤ)) =
        insert (2 * (q : ℤ) + 1) (insert (2 * (q : ℤ)) (Finset.Ico (0 : ℤ) (2 * (q : ℤ)))) := by
      ext t
      simp only [Finset.mem_Ico, Finset.mem_insert]
      push_cast
      omega
    have h₂ : (2 * (q : ℤ)) ∉ Finset.Ico (0 : ℤ) (2 * (q : ℤ)) := by
      simp
    rw [hI, Finset.filter_insert, Finset.filter_insert]
    by_cases hp : (2 : ℤ) ∣ 2 * (q : ℤ) - a
    · have hp' : ¬ (2 : ℤ) ∣ 2 * (q : ℤ) + 1 - a := by omega
      rw [if_neg hp', if_pos hp, Finset.card_insert_of_notMem, ih]
      simp [h₂]
    · have hp' : (2 : ℤ) ∣ 2 * (q : ℤ) + 1 - a := by omega
      rw [if_pos hp', if_neg hp, Finset.card_insert_of_notMem, ih]
      simp only [Finset.mem_filter, Finset.mem_Ico, not_and]
      omega
private lemma card_sameParityIndices (G : CellGrid) (n q : ℕ) (hq : n / G.side = 2 * q) (κ : Fin 4 → ℤ) :
    (G.sameParityIndices n κ).card = q ^ 4 := by
  classical
  have : G.sameParityIndices n κ = Fintype.piFinset fun i =>
      (Finset.Ico (0 : ℤ) (2 * (q : ℤ))).filter fun t => (2 : ℤ) ∣ t - κ i := by
    ext κ'
    simp only [CellGrid.sameParityIndices, CellGrid.indices, hq, Finset.mem_filter, Fintype.mem_piFinset]
    push_cast
    exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  rw [this, Fintype.card_piFinset]
  simp [card_filter_parity_Ico]
private lemma card_indices (G : CellGrid) (n q : ℕ) (hq : n / G.side = 2 * q) :
    (G.indices n).card = 16 * q ^ 4 := by
  have h : (Finset.Ico (0 : ℤ) ((2 * q : ℕ) : ℤ)).card = 2 * q := by
    simp only [Int.card_Ico, sub_zero, Int.toNat_natCast]
  simp only [CellGrid.indices, hq, Fintype.card_piFinset, h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring
private lemma sameParityIndices_subset (G : CellGrid) (n : ℕ) (κ : Fin 4 → ℤ) :
    G.sameParityIndices n κ ⊆ G.indices n := by
  classical
  exact Finset.filter_subset _ _
private lemma refineBy_side (L d : ℕ) : ∀ G : CellGrid, (CellGrid.refineBy L d G).side = G.side * L ^ d := by
  induction d with
  | zero => intro G; simp [CellGrid.refineBy]
  | succ d ih =>
    intro G
    simp only [CellGrid.refineBy, ih, CellGrid.refine]
    ring
private lemma refineBy_indices (L d n : ℕ) (hL : 0 < L) (G : CellGrid) :
    (CellGrid.refineBy L d G).indices (fineSide L d n) = G.indices n := by
  have : fineSide L d n / (CellGrid.refineBy L d G).side = n / G.side := by
    rw [refineBy_side, fineSide_eq]
    exact Nat.mul_div_mul_right _ _ (pow_pos hL d)
  simp only [CellGrid.indices, this]
end CellGeometry
section Probabilities
variable {ℓ : StepParameters} (T : StageTower ℓ) (S : ChainSampler T)
private lemma cellEventProb_nonneg (k n : ℕ) [NeZero n] (c : Finset (TorusSite n))
    (U : TorusField (fineSide ℓ.side k n)) : 0 ≤ cellEventProb T S k n c U := ENNReal.toReal_nonneg
private lemma cellEventProb_le_one (k n : ℕ) [NeZero n] (c : Finset (TorusSite n))
    (U : TorusField (fineSide ℓ.side k n)) : cellEventProb T S k n c U ≤ 1 := by
  have := isProbabilityMeasure_chainNoiseMeasure ℓ k n
  unfold cellEventProb
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top
    (prob_le_one (μ := chainNoiseMeasure ℓ k n) (s := {ξ | CellEvent T k n (sampleChain T S k n U ξ) c}))
private lemma cellEventProb_measurable {k n : ℕ} [NeZero n] {c : Finset (TorusSite n)}
    (hloc : CellEventIsLocal T S k n c) : Measurable (cellEventProb T S k n c) := by
  have := isProbabilityMeasure_chainNoiseMeasure ℓ k n
  exact (measurable_measure_prodMk_left (ν := chainNoiseMeasure ℓ k n) hloc.1).ennreal_toReal
private lemma cellEventProb_dependsOnlyOn {k n : ℕ} [NeZero n] {c : Finset (TorusSite n)}
    (hloc : CellEventIsLocal T S k n c) :
    DependsOnlyOn (cellBelow ℓ.side k n c) (cellEventProb T S k n c) := by
  intro W W' h
  have hset : {ξ | CellEvent T k n (sampleChain T S k n W ξ) c} =
      {ξ | CellEvent T k n (sampleChain T S k n W' ξ) c} :=
    Set.ext fun ξ => hloc.2 W W' ξ ξ h (noiseAgreesOn_refl ℓ k n c ξ)
  unfold cellEventProb
  rw [hset]
private lemma cellEvents_measure_eq_prod {k n : ℕ} [NeZero n] (G : CellGrid) (hG : G.Compatible n)
    (hloc : ∀ κ, CellEventIsLocal T S k n (G.cell n κ)) {A : Finset (Fin 4 → ℤ)} (hA : A ⊆ G.indices n)
    (U : TorusField (fineSide ℓ.side k n)) :
    chainNoiseMeasure ℓ k n {ξ | ∀ κ ∈ A, CellEvent T k n (sampleChain T S k n U ξ) (G.cell n κ)} =
      ∏ κ ∈ A, chainNoiseMeasure ℓ k n {ξ | CellEvent T k n (sampleChain T S k n U ξ) (G.cell n κ)} := by
  classical
  refine chainNoiseMeasure_biInter_eq_prod ℓ k n A (fun κ => G.cell n κ)
    (fun κ => {ξ | CellEvent T k n (sampleChain T S k n U ξ) (G.cell n κ)}) ?_ ?_ ?_
  · intro κ _
    exact measurable_prodMk_left (hloc κ).1
  · intro κ hκ κ' hκ' hne
    exact cell_disjoint G n hG (hA hκ) (hA hκ') hne
  · intro κ _ ξ ξ' h
    exact (hloc κ).2 U U ξ ξ' (fun _ _ _ => rfl) h
private lemma sFinite_wilsonLaw (β : ℝ) (m : ℕ) [NeZero m] : SFinite (wilsonLaw β m) := by
  unfold wilsonLaw fieldHaar
  infer_instance
private lemma copyProductMean_le (β : ℝ) (k n : ℕ) [NeZero n] (G : CellGrid) (hG : G.Compatible n)
    (κ : Fin 4 → ℤ)
    (hloc : ∀ κ, CellEventIsLocal T S k n (G.cell n κ))
    (hdraw : Measurable (fun p : TorusField (fineSide ℓ.side k n) × ChainNoise ℓ k n =>
      sampleChain T S k n p.1 p.2))
    (hmap : Measure.map (fun p : TorusField (fineSide ℓ.side k n) × ChainNoise ℓ k n =>
      sampleChain T S k n p.1 p.2)
      ((wilsonLaw β (fineSide ℓ.side k n)).prod (chainNoiseMeasure ℓ k n)) = markedSampleLaw T β k n)
    (hcarry : ∀ κ' ∈ G.sameParityIndices n κ, ∀ W : TorusField (fineSide ℓ.side k n),
      cellCopy (CellGrid.refineBy ℓ.side k G) κ κ' (cellEventProb T S k n (G.cell n κ)) W =
        cellEventProb T S k n (G.cell n κ') W)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : markedSampleLaw T β k n {u | ∀ κ' ∈ G.sameParityIndices n κ, CellEvent T k n u (G.cell n κ')} ≤
      ENNReal.ofReal B) :
    copyProductMean (CellGrid.refineBy ℓ.side k G) β κ (G.indices n) (cellEventProb T S k n (G.cell n κ)) ≤ B := by
  classical
  have := isProbabilityMeasure_chainNoiseMeasure ℓ k n
  have := sFinite_wilsonLaw β (fineSide ℓ.side k n)
  set F := cellEventProb T S k n (G.cell n κ) with hF
  set G' := CellGrid.refineBy ℓ.side k G with hG'
  set Ty := G.sameParityIndices n κ with hTy
  have hc0 : ∀ κ' W, 0 ≤ cellCopy G' κ κ' F W := fun κ' W => cellEventProb_nonneg T S k n _ _
  have hc1 : ∀ κ' W, cellCopy G' κ κ' F W ≤ 1 := fun κ' W => cellEventProb_le_one T S k n _ _
  have hf0 : ∀ W, 0 ≤ ∏ κ' ∈ G.indices n, cellCopy G' κ κ' F W :=
    fun W => Finset.prod_nonneg fun κ' _ => hc0 κ' W
  have hsub : Ty ⊆ G.indices n := sameParityIndices_subset G n κ
  have hfg : ∀ W, ENNReal.ofReal (∏ κ' ∈ G.indices n, cellCopy G' κ κ' F W) ≤
      chainNoiseMeasure ℓ k n {ξ | ∀ κ' ∈ Ty, CellEvent T k n (sampleChain T S k n W ξ) (G.cell n κ')} := by
    intro W
    have h₁ : ∏ κ' ∈ G.indices n, cellCopy G' κ κ' F W ≤ ∏ κ' ∈ Ty, cellCopy G' κ κ' F W := by
      rw [← Finset.prod_sdiff hsub]
      have hle : ∏ κ' ∈ G.indices n \ Ty, cellCopy G' κ κ' F W ≤ 1 :=
        Finset.prod_le_one (fun κ' _ => hc0 κ' W) (fun κ' _ => hc1 κ' W)
      have h0 : 0 ≤ ∏ κ' ∈ Ty, cellCopy G' κ κ' F W := Finset.prod_nonneg fun κ' _ => hc0 κ' W
      calc _ ≤ 1 * ∏ κ' ∈ Ty, cellCopy G' κ κ' F W := mul_le_mul_of_nonneg_right hle h0
        _ = _ := one_mul _
    have h₂ : ∏ κ' ∈ Ty, cellCopy G' κ κ' F W = ∏ κ' ∈ Ty, cellEventProb T S k n (G.cell n κ') W :=
      Finset.prod_congr rfl fun κ' hκ' => hcarry κ' hκ' W
    have h₃ : ∏ κ' ∈ Ty, cellEventProb T S k n (G.cell n κ') W =
        (chainNoiseMeasure ℓ k n
          {ξ | ∀ κ' ∈ Ty, CellEvent T k n (sampleChain T S k n W ξ) (G.cell n κ')}).toReal := by
      rw [cellEvents_measure_eq_prod T S G hG hloc hsub W, ENNReal.toReal_prod]
      rfl
    calc ENNReal.ofReal (∏ κ' ∈ G.indices n, cellCopy G' κ κ' F W)
        ≤ ENNReal.ofReal ((chainNoiseMeasure ℓ k n
            {ξ | ∀ κ' ∈ Ty, CellEvent T k n (sampleChain T S k n W ξ) (G.cell n κ')}).toReal) :=
          ENNReal.ofReal_le_ofReal (by rw [← h₃, ← h₂]; exact h₁)
      _ = _ := ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hD : MeasurableSet {p : TorusField (fineSide ℓ.side k n) × ChainNoise ℓ k n |
      ∀ κ' ∈ Ty, CellEvent T k n (sampleChain T S k n p.1 p.2) (G.cell n κ')} := by
    have : {p : TorusField (fineSide ℓ.side k n) × ChainNoise ℓ k n |
        ∀ κ' ∈ Ty, CellEvent T k n (sampleChain T S k n p.1 p.2) (G.cell n κ')} =
        ⋂ κ' ∈ Ty, {p | CellEvent T k n (sampleChain T S k n p.1 p.2) (G.cell n κ')} := by
      ext p; simp
    rw [this]
    exact Finset.measurableSet_biInter _ fun κ' _ => (hloc κ').1
  have hlin : ∫⁻ W, ENNReal.ofReal (∏ κ' ∈ G.indices n, cellCopy G' κ κ' F W)
      ∂(wilsonLaw β (fineSide ℓ.side k n)) ≤ ENNReal.ofReal B := by
    calc ∫⁻ W, ENNReal.ofReal (∏ κ' ∈ G.indices n, cellCopy G' κ κ' F W) ∂(wilsonLaw β (fineSide ℓ.side k n))
        ≤ ∫⁻ W, chainNoiseMeasure ℓ k n
            {ξ | ∀ κ' ∈ Ty, CellEvent T k n (sampleChain T S k n W ξ) (G.cell n κ')}
            ∂(wilsonLaw β (fineSide ℓ.side k n)) := lintegral_mono hfg
      _ = ((wilsonLaw β (fineSide ℓ.side k n)).prod (chainNoiseMeasure ℓ k n)) {p |
            ∀ κ' ∈ Ty, CellEvent T k n (sampleChain T S k n p.1 p.2) (G.cell n κ')} :=
          (Measure.prod_apply hD).symm
      _ ≤ Measure.map (fun p : TorusField (fineSide ℓ.side k n) × ChainNoise ℓ k n =>
              sampleChain T S k n p.1 p.2)
            ((wilsonLaw β (fineSide ℓ.side k n)).prod (chainNoiseMeasure ℓ k n))
            {u | ∀ κ' ∈ Ty, CellEvent T k n u (G.cell n κ')} :=
          Measure.le_map_apply hdraw.aemeasurable _
      _ = markedSampleLaw T β k n {u | ∀ κ' ∈ Ty, CellEvent T k n u (G.cell n κ')} := by rw [hmap]
      _ ≤ ENNReal.ofReal B := hB
  unfold copyProductMean
  by_cases hint : Integrable (fun W => ∏ κ' ∈ G.indices n, cellCopy G' κ κ' F W)
      (wilsonLaw β (fineSide ℓ.side k n))
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hint.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hB0 hlin
  · rw [integral_undef hint]
    exact hB0
end Probabilities
section Decomposition
private lemma measure_le_of_cover_by_choices {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {ι O : Type*}
    [Fintype ι] [Fintype O] [DecidableEq ι] [DecidableEq O] (E : Set Ω) (P : ι → O → Set Ω) (w : O → ℝ)
    (hw : ∀ o, 0 ≤ w o) (C : ℝ) (hC : 0 ≤ C)
    (hcov : ∀ u ∈ E, ∀ i, ∃ o, u ∈ P i o)
    (hb : ∀ J : ι → O, μ (⋂ i, P i (J i)) ≤ ENNReal.ofReal (C * ∏ i, w (J i))) :
    μ E ≤ ENNReal.ofReal (C * (∑ o, w o) ^ Fintype.card ι) := by
  have hsub : E ⊆ ⋃ J : ι → O, ⋂ i, P i (J i) := by
    intro u hu
    choose J hJ using hcov u hu
    exact Set.mem_iUnion.2 ⟨J, Set.mem_iInter.2 hJ⟩
  calc μ E ≤ μ (⋃ J : ι → O, ⋂ i, P i (J i)) := measure_mono hsub
    _ ≤ ∑ J : ι → O, μ (⋂ i, P i (J i)) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ J : ι → O, ENNReal.ofReal (C * ∏ i, w (J i)) := Finset.sum_le_sum fun J _ => hb J
    _ = ENNReal.ofReal (∑ J : ι → O, C * ∏ i, w (J i)) :=
        (ENNReal.ofReal_sum_of_nonneg fun J _ => mul_nonneg hC (Finset.prod_nonneg fun i _ => hw _)).symm
    _ = _ := by
      congr 1
      rw [← Finset.mul_sum]
      congr 1
      have h := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset O)) (fun _ o => w o)
      rw [Fintype.piFinset_univ] at h
      rw [← h]
      simp
variable {ℓ : StepParameters} (T : StageTower ℓ)
private lemma measurableSet_stageHull_pred (s n : ℕ) [NeZero n] (P : Finset (TorusSite n) → Prop) :
    MeasurableSet[stageSigma T s n] {u | P (stageHull T s n u)} := by
  have hS : MeasurableSet {p : (Σ Y : Finset (TorusSite n), (Y → (T.stage s).labels.Ω)) | P p.1} := by
    refine MeasurableSpace.measurableSet_iInf.2 fun Y => MeasurableSpace.map_def.2 ?_
    by_cases h : P Y
    · convert MeasurableSet.univ using 1
      ext ω; simp [h]
    · convert MeasurableSet.empty using 1
      ext ω; simp [h]
  exact MeasurableSpace.measurableSet_comap.2 ⟨_, measurable_snd hS, rfl⟩
private lemma measure_cellEvents_le (β : ℝ) (k n : ℕ) [NeZero n] (G : CellGrid) (κ : Fin 4 → ℤ) (a V : ℝ)
    (f : ℕ → ℝ)
    (hfalse : ∀ (u : MarkedSample ℓ k n) (κ' : Fin 4 → ℤ), ∀ v ∈ upperHull T k k n u (G.cell n κ'),
      v ∉ stageHull T k n u → ∃ j < k, HasLongSupport T k j k n u (G.cell n κ'))
    (hlong : ∀ Sj : ℕ → Finset (Fin 4 → ℤ), (∀ j < k, Sj j ⊆ G.sameParityIndices n κ) →
      ∀ A : Set (MarkedSample ℓ k n), MeasurableSet[stageSigma T k n] A →
        markedSampleLaw T β k n (A ∩ {u | ∀ j < k, ∀ κ' ∈ Sj j, HasLongSupport T k j k n u (G.cell n κ')}) ≤
          ENNReal.ofReal (∏ j ∈ Finset.range k, Real.exp (-(f j * (Sj j).card))) * markedSampleLaw T β k n A)
    (hhull : ∀ Y : Finset (Fin 4 → ℤ), Y ⊆ G.sameParityIndices n κ → markedSampleLaw T β k n
        {u | ∀ κ' ∈ Y, (stageHull T k n u ∩ interiorAtDepth (8 * stageRange T k) (G.cell n κ')).Nonempty} ≤
      ENNReal.ofReal (Real.exp (V - a * Y.card))) :
    markedSampleLaw T β k n {u | ∀ κ' ∈ G.sameParityIndices n κ, CellEvent T k n u (G.cell n κ')} ≤
      ENNReal.ofReal (Real.exp V *
        (Real.exp (-a) + ∑ j ∈ Finset.range k, Real.exp (-f j)) ^ (G.sameParityIndices n κ).card) := by
  classical
  set Ty := G.sameParityIndices n κ with hTy
  let g : Option (Fin k) → ℝ := fun o => match o with
    | none => a
    | some j => f j
  let P : Ty → Option (Fin k) → Set (MarkedSample ℓ k n) := fun i o => match o with
    | none => {u | (stageHull T k n u ∩ interiorAtDepth (8 * stageRange T k) (G.cell n i.1)).Nonempty}
    | some j => {u | HasLongSupport T k j.1 k n u (G.cell n i.1)}
  have key := measure_le_of_cover_by_choices (markedSampleLaw T β k n)
    {u | ∀ κ' ∈ Ty, CellEvent T k n u (G.cell n κ')} P
    (fun o => Real.exp (-g o)) (fun _ => (Real.exp_pos _).le) (Real.exp V) (Real.exp_pos _).le ?_ ?_
  · have hsum : ∑ o, Real.exp (-g o) = Real.exp (-a) + ∑ j ∈ Finset.range k, Real.exp (-f j) := by
      rw [Fintype.sum_option, Finset.sum_range]
    rw [hsum, Fintype.card_coe] at key
    exact key
  · intro u hu i
    obtain ⟨v, hv⟩ : (upperHull T k k n u (G.cell n i.1) ∩
        interiorAtDepth (8 * stageRange T k) (G.cell n i.1)).Nonempty := hu i.1 i.2
    rw [Finset.mem_inter] at hv
    by_cases hvh : v ∈ stageHull T k n u
    · exact ⟨none, ⟨v, Finset.mem_inter.2 ⟨hvh, hv.2⟩⟩⟩
    · obtain ⟨j, hj, hl⟩ := hfalse u i.1 v hv.1 hvh
      exact ⟨some ⟨j, hj⟩, hl⟩
  · intro J
    set SY : Finset (Fin 4 → ℤ) :=
      (Finset.univ.filter fun i : Ty => J i = none).map (Function.Embedding.subtype _) with hSY
    set Sj : ℕ → Finset (Fin 4 → ℤ) := fun j =>
      (Finset.univ.filter fun i : Ty => (J i).map Fin.val = some j).map (Function.Embedding.subtype _) with hSj
    have hSYs : SY ⊆ Ty := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      exact i.2
    have hSjs : ∀ j < k, Sj j ⊆ Ty := by
      intro j _ x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      exact i.2
    let A : Set (MarkedSample ℓ k n) :=
      {u | ∀ κ' ∈ SY, (stageHull T k n u ∩ interiorAtDepth (8 * stageRange T k) (G.cell n κ')).Nonempty}
    have hA : MeasurableSet[stageSigma T k n] A :=
      measurableSet_stageHull_pred T k n fun Y =>
        ∀ κ' ∈ SY, (Y ∩ interiorAtDepth (8 * stageRange T k) (G.cell n κ')).Nonempty
    have hsub : (⋂ i, P i (J i)) ⊆
        A ∩ {u | ∀ j < k, ∀ κ' ∈ Sj j, HasLongSupport T k j k n u (G.cell n κ')} := by
      intro u hu
      have hu' := Set.mem_iInter.mp hu
      refine ⟨fun κ' hκ' => ?_, fun j _ κ' hκ' => ?_⟩
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hκ'
        have hJ : J i = none := (Finset.mem_filter.mp hi).2
        have := hu' i
        rw [hJ] at this
        exact this
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hκ'
        have hJ := (Finset.mem_filter.mp hi).2
        obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.mp hJ
        have := hu' i
        rw [hj'] at this
        exact this
    have hsum : ∑ i, g (J i) = a * SY.card + ∑ j ∈ Finset.range k, f j * (Sj j).card := by
      have h₁ : ∑ i, g (J i) = ∑ o, ((Finset.univ.filter fun i : Ty => J i = o).card : ℝ) * g o := by
        rw [← Finset.sum_fiberwise Finset.univ J]
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [Finset.sum_congr rfl (g := fun _ => g o)
          (fun i hi => by rw [(Finset.mem_filter.mp hi).2]), Finset.sum_const, nsmul_eq_mul]
      rw [h₁, Fintype.sum_option, Finset.sum_range]
      have hc : ∀ j : Fin k, (Sj j).card = (Finset.univ.filter fun i : Ty => J i = some j).card := by
        intro j
        simp only [hSj, Finset.card_map]
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          obtain ⟨j', hj', he⟩ := Option.map_eq_some_iff.mp h
          rw [hj', Fin.ext he]
        · intro h
          rw [h]; rfl
      have hY : SY.card = (Finset.univ.filter fun i : Ty => J i = none).card := by
        simp only [hSY, Finset.card_map]
      rw [hY]
      congr 1
      · exact mul_comm _ _
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [hc j]
        exact mul_comm _ _
    calc markedSampleLaw T β k n (⋂ i, P i (J i))
        ≤ markedSampleLaw T β k n
            (A ∩ {u | ∀ j < k, ∀ κ' ∈ Sj j, HasLongSupport T k j k n u (G.cell n κ')}) := measure_mono hsub
      _ ≤ ENNReal.ofReal (∏ j ∈ Finset.range k, Real.exp (-(f j * (Sj j).card))) * markedSampleLaw T β k n A :=
          hlong Sj hSjs A hA
      _ ≤ ENNReal.ofReal (∏ j ∈ Finset.range k, Real.exp (-(f j * (Sj j).card))) *
            ENNReal.ofReal (Real.exp (V - a * SY.card)) := by
          gcongr
          exact hhull SY hSYs
      _ = ENNReal.ofReal ((∏ j ∈ Finset.range k, Real.exp (-(f j * (Sj j).card))) *
            Real.exp (V - a * SY.card)) :=
          (ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)).symm
      _ = ENNReal.ofReal (Real.exp V * ∏ i, Real.exp (-g (J i))) := by
          congr 1
          rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add, ← Real.exp_add, Finset.sum_neg_distrib,
            Finset.sum_neg_distrib, hsum]
          congr 1
          ring
end Decomposition
section Estimates
private lemma exp_mul_two_exp_pow_le {Cl a : ℝ} {M : ℕ} (h : Cl + 1 ≤ a / 32) :
    Real.exp (Cl * (16 * (M : ℝ))) * (2 * Real.exp (-a)) ^ M ≤ Real.exp (-(a / 32 * (16 * (M : ℝ)))) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h3 : 2 * Real.exp (-a) ≤ Real.exp (1 - a) := by
    rw [sub_eq_add_neg, Real.exp_add]
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  have h4 : (2 * Real.exp (-a)) ^ M ≤ Real.exp ((M : ℝ) * (1 - a)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) h3 M
  calc Real.exp (Cl * (16 * (M : ℝ))) * (2 * Real.exp (-a)) ^ M
      ≤ Real.exp (Cl * (16 * (M : ℝ))) * Real.exp ((M : ℝ) * (1 - a)) :=
        mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    _ = Real.exp (Cl * (16 * (M : ℝ)) + (M : ℝ) * (1 - a)) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith
private lemma exp_mul_pow_bound {V Cl a s : ℝ} {M : ℕ} (hV : V = Cl * (16 * (M : ℝ)))
    (hs : s ≤ Real.exp (-a)) (hs0 : 0 ≤ s) (h : Cl + 1 ≤ a / 32) :
    0 ≤ Real.exp V * (Real.exp (-a) + s) ^ M ∧
      Real.exp V * (Real.exp (-a) + s) ^ M ≤ Real.exp (-(a / 32 * (16 * (M : ℝ)))) := by
  refine ⟨by positivity, ?_⟩
  have h1 : Real.exp V * (Real.exp (-a) + s) ^ M ≤ Real.exp V * (2 * Real.exp (-a)) ^ M :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) (Real.exp_pos _).le
  rw [hV] at h1 ⊢
  exact h1.trans (exp_mul_two_exp_pow_le h)
private lemma volume_factor_eq (A l p : ℝ) (q : ℕ) (h : p = l * q) :
    A * (2 * p) ^ 4 = (A * l ^ 4) * (16 * ((q ^ 4 : ℕ) : ℝ)) := by
  subst h
  push_cast
  ring
private lemma baseCellSide_le {L r : ℕ} (hL : 2 ≤ L) (hr : 1 ≤ r) : baseCellSide L r ≤ L * (2 ^ 7 * r) := by
  have hb : 1 < 2 ^ 7 * r := by omega
  have hc : 0 < Nat.clog L (2 ^ 7 * r) := Nat.clog_pos (by omega) (by omega)
  have hlt := Nat.pow_pred_clog_lt_self (by omega : 1 < L) hb
  unfold baseCellSide
  obtain ⟨c, hc'⟩ : ∃ c, Nat.clog L (2 ^ 7 * r) = c + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hc).symm⟩
  rw [hc'] at hlt ⊢
  simp only [Nat.pred_succ] at hlt
  rw [pow_succ, mul_comm]
  exact Nat.mul_le_mul_left L hlt.le
abbrev _root_.YangMills.SharedProofs.p1293 := @baseCellSide_le
private lemma mul_le_of_div_le {A u v c x : ℝ} (hc : 0 < c) (h1 : A * 32 / c ≤ u) (hv : 0 ≤ v)
    (hx : x = u * v) : A * v ≤ x * c / 32 := by
  have h2 : A * 32 ≤ u * c := by rwa [div_le_iff₀ hc] at h1
  have h3 := mul_le_mul_of_nonneg_right h2 hv
  rw [hx]
  linarith [h3, (by ring : u * c * v = u * v * c), (by ring : A * 32 * v = 32 * (A * v)),
    (by ring : u * v * c / 32 = (u * v * c) / 32)]
private lemma exists_large_coupling_bound (L : ℕ) (hL : 2 ≤ L) (C₁ C₂ c : ℝ) (hc : 0 < c) :
    ∃ y₃ : ℝ, 1 ≤ y₃ ∧ ∀ x, y₃ ≤ x →
      (C₁ + C₂ * Real.log x) * (baseCellSide L (clusterRange x) : ℝ) ^ 4 + 1 ≤ x * c / 32 := by
  set K : ℝ := |C₁| + 100 * |C₂| with hK
  set M : ℝ := 2 ^ 32 * (L : ℝ) ^ 4 with hM
  set D : ℝ := (K * M + 1) * 32 / c + 1 with hD
  have hD1 : 1 ≤ D := by
    have : 0 ≤ (K * M + 1) * 32 / c := by positivity
    linarith
  refine ⟨D ^ 100, one_le_pow₀ hD1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (one_le_pow₀ hD1).trans hx
  have hx0 : 0 ≤ x := by linarith
  set t : ℝ := x ^ ((1 : ℝ) / 100) with ht
  have ht1 : 1 ≤ t := Real.one_le_rpow hx1 (by norm_num)
  have ht0 : 0 ≤ t := by linarith
  have htx : t ^ 100 = x := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have hDt : D ≤ t := by
    exact (pow_le_pow_iff_left₀ (by linarith) ht0 (by norm_num : (100 : ℕ) ≠ 0)).1 (by rw [htx]; exact hx)
  have hlog : Real.log x ≤ 100 * t := by
    have h1 : Real.log t = Real.log x / 100 := by
      rw [ht, Real.log_rpow (by linarith)]
      ring
    have h2 : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos (by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hr1 : 1 ≤ clusterRange x := by
    unfold clusterRange
    exact Nat.one_le_ceil_iff.mpr (by linarith)
  have hr : (clusterRange x : ℝ) ≤ 2 * t := by
    have := (Nat.ceil_lt_add_one ht0).le
    have h' : ((clusterRange x : ℕ) : ℝ) ≤ t + 1 := this
    linarith
  have hl : (baseCellSide L (clusterRange x) : ℝ) ≤ 2 ^ 8 * (L : ℝ) * t := by
    have h := baseCellSide_le hL hr1
    have h' : (baseCellSide L (clusterRange x) : ℝ) ≤ (L : ℝ) * (2 ^ 7 * (clusterRange x : ℝ)) := by
      exact_mod_cast h
    nlinarith
  have hl4 : (baseCellSide L (clusterRange x) : ℝ) ^ 4 ≤ M * t ^ 4 := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg _) hl 4
    calc _ ≤ (2 ^ 8 * (L : ℝ) * t) ^ 4 := this
      _ = M * t ^ 4 := by rw [hM]; ring
  have hC : C₁ + C₂ * Real.log x ≤ K * t := by
    have h1 : C₁ ≤ |C₁| * t := (le_abs_self C₁).trans (le_mul_of_one_le_right (abs_nonneg _) ht1)
    have h2 : C₂ * Real.log x ≤ |C₂| * (100 * t) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C₂) hlog0).trans
        (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))
    rw [hK]
    nlinarith
  have hprod : (C₁ + C₂ * Real.log x) * (baseCellSide L (clusterRange x) : ℝ) ^ 4 ≤ K * M * t ^ 5 := by
    calc _ ≤ (K * t) * (baseCellSide L (clusterRange x) : ℝ) ^ 4 := mul_le_mul_of_nonneg_right hC (by positivity)
      _ ≤ (K * t) * (M * t ^ 4) := mul_le_mul_of_nonneg_left hl4 (by positivity)
      _ = K * M * t ^ 5 := by ring
  have ht5 : 1 ≤ t ^ 5 := one_le_pow₀ ht1
  have hbig : (K * M + 1) * t ^ 5 ≤ x * c / 32 := by
    have h95 : D ≤ t ^ 95 := hDt.trans (le_self_pow₀ ht1 (by norm_num))
    have h1 : (K * M + 1) * 32 / c ≤ t ^ 95 := le_trans (by rw [hD]; linarith) h95
    have h3 : x = t ^ 95 * t ^ 5 := by
      rw [← pow_add]
      exact htx.symm
    exact mul_le_of_div_le hc h1 (by positivity) h3
  linarith
private lemma chessboardNorm_le {m : ℕ} [NeZero m] (G' : CellGrid) (β : ℝ) (κ : Fin 4 → ℤ)
    (F : TorusField m → ℝ) {Ix : Finset (Fin 4 → ℤ)} (hI : G'.indices m = Ix) {M : ℕ} (hM : 0 < M)
    (hN : Ix.card = 16 * M) {a : ℝ}
    (h0 : 0 ≤ copyProductMean G' β κ Ix F)
    (hle : copyProductMean G' β κ Ix F ≤ Real.exp (-(a / 32 * (16 * (M : ℝ))))) :
    chessboardNorm G' β κ F ≤ Real.exp (-(a / 2 ^ 5)) := by
  unfold chessboardNorm
  rw [hI, hN]
  have hpos : (0 : ℝ) ≤ 1 / ((16 * M : ℕ) : ℝ) := by positivity
  calc copyProductMean G' β κ Ix F ^ (1 / ((16 * M : ℕ) : ℝ))
      ≤ Real.exp (-(a / 32 * (16 * (M : ℝ)))) ^ (1 / ((16 * M : ℕ) : ℝ)) := Real.rpow_le_rpow h0 hle hpos
    _ = Real.exp (-(a / 2 ^ 5)) := by
      rw [← Real.exp_mul]
      congr 1
      push_cast
      field_simp
      norm_num
end Estimates
section Assembly
private lemma holdsAtAdmissibleParameters_and {P Q : ParameterAssignment → ℝ → Prop} (hP : HoldsAtAdmissibleParameters P)
    (hQ : HoldsAtAdmissibleParameters Q) : HoldsAtAdmissibleParameters fun T y => P T y ∧ Q T y := by apply _root_.YangMills.SharedProofs.p114722 <;> assumption
private lemma couplingFlow_step_le (ℓ : StepParameters) (hR : ExpansionReturnsAt ℓ) (β : ℝ)
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) (k : ℕ)
    (hx : ∀ j ≤ k, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) :
    ∀ j < k, |(couplingFlow ℓ β (j + 1)).1 - (couplingFlow ℓ β j).1| ≤ 2 * ℓ.B := by
  have hstep : ∀ j, j ≤ k → HasExpansion ℓ j (couplingFlow ℓ β j).1 (couplingFlow ℓ β j).2 →
      HasExpansion ℓ (j + 1) (couplingFlow ℓ β (j + 1)).1 (couplingFlow ℓ β (j + 1)).2 ∧
        |(couplingFlow ℓ β (j + 1)).1 - (couplingFlow ℓ β j).1| ≤ 2 * ℓ.B := by
    intro j hj hrow
    obtain ⟨x', ⟨hx', hmove⟩, huniq⟩ := hR j _ _ (hx j hj) hrow
    have hex : ∃ x', HasExpansion ℓ (j + 1) x'
        (kernelImage ℓ (couplingFlow ℓ β j).1 (couplingFlow ℓ β j).2) := ⟨x', hx'⟩
    have hnext : (couplingFlow ℓ β (j + 1)).1 = hex.choose := by
      simp only [couplingFlow, expansionCoupling, dif_pos hex]
    have hch := hex.choose_spec
    obtain ⟨_, f, hf, _⟩ := hch
    have hsame : hex.choose = x' := huniq _ f hf
    have hx1 : (couplingFlow ℓ β (j + 1)).1 = x' := hnext.trans hsame
    refine ⟨?_, by rw [hx1]; exact hmove⟩
    rw [hx1]
    exact hx'
  have hrows : ∀ j, j ≤ k → HasExpansion ℓ j (couplingFlow ℓ β j).1 (couplingFlow ℓ β j).2 := by
    intro j
    induction j with
    | zero => intro _; exact h0
    | succ j ih =>
      intro hj
      exact (hstep j (by omega) (ih (by omega))).1
  intro j hj
  exact (hstep j hj.le (hrows j hj.le)).2
private lemma pullbackBy_reflectionTo_eq_translate (G' : CellGrid) {m : ℕ} [NeZero m] (κ κ' : Fin 4 → ℤ)
    (h : ∀ i, (2 : ℤ) ∣ κ' i - κ i) (W : TorusField m) :
    pullbackBy (G'.reflectionTo κ κ') W = TorusFields.translate (siteOfInt fun i => (G'.side : ℤ) * (κ' i - κ i)) W := by
  have hev : ∀ i, Even (κ' i - κ i) := fun i => even_iff_two_dvd.2 (h i)
  have hs : ∀ i, (G'.reflectionTo κ κ').axisSign i = 1 := by
    intro i
    simp [CellGrid.reflectionTo, hev i]
  have hsh : ∀ i, (G'.reflectionTo κ κ').offset i = (G'.side : ℤ) * (κ' i - κ i) := by
    intro i
    simp [CellGrid.reflectionTo, hev i]
  funext x j
  have hperm : (G'.reflectionTo κ κ').axisPerm.symm j = j := rfl
  have hon : (G'.reflectionTo κ κ').mapSite x = x + siteOfInt fun i => (G'.side : ℤ) * (κ' i - κ i) := by
    funext i
    have hp : (G'.reflectionTo κ κ').axisPerm i = i := rfl
    simp only [TorusIsometry.mapSite, hs, hsh, hp, siteOfInt, Pi.add_apply]
    simp
  simp only [pullbackBy, hperm, hs, if_true, TorusFields.translate, hon]
private lemma image_cell_add (G : CellGrid) (n : ℕ) [NeZero n] (κ κ' : Fin 4 → ℤ) :
    (G.cell n κ).image (· + siteOfInt fun i => (G.side : ℤ) * (κ' i - κ i)) = G.cell n κ' := by
  ext x
  simp only [Finset.mem_image, CellGrid.cell, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨h, hh, ?_⟩
    funext i
    simp only [siteOfInt, Pi.add_apply]
    push_cast
    ring
  · rintro ⟨h, hh, rfl⟩
    refine ⟨siteOfInt fun i => G.offset i + (G.side : ℤ) * κ i + h i, ⟨h, hh, rfl⟩, ?_⟩
    funext i
    simp only [siteOfInt, Pi.add_apply]
    push_cast
    ring
private lemma clusterRange_mono {x y : ℝ} (hy : 0 ≤ y) (h : y ≤ x) : clusterRange y ≤ clusterRange x :=
  Nat.ceil_mono (Real.rpow_le_rpow hy h (by norm_num))
private lemma le_clusterRange (A : ℕ) {y : ℝ} (hy : (A : ℝ) ^ 100 ≤ y) : A ≤ clusterRange y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
end Assembly
set_option maxHeartbeats 4000000 in
theorem cellEventProbChessboardBound (h₁ : sampleChainLawStatement)
    (h₂ : cellEventIsLocalStatement) (h₃ : extraHullSiteHasLongSupportStatement)
    (h₄ : longSupportsAllStagesBoundStatement) (h₅ : longSupportPriceSumStatement)
    (h₆ : hullMeetsCellsBoundStatement) (h₇ : translationCarriesCellMeansStatement) :
    cellEventProbChessboardBoundStatement := by
  obtain ⟨C₁, C₂, h₆⟩ := h₆
  have hall := holdsAtAdmissibleParameters_and h₂ (holdsAtAdmissibleParameters_and h₃ (holdsAtAdmissibleParameters_and h₄
    (holdsAtAdmissibleParameters_and h₅ (holdsAtAdmissibleParameters_and h₆ h₇))))
  intro a₀ ha₀
  obtain ⟨L₀, rt₀, hrt₀, H⟩ := hall a₀ ha₀
  refine ⟨L₀, rt₀, hrt₀, fun L hL hLe Tb hTa hTL hD hrt => ?_⟩
  obtain ⟨y₀, Y⟩ := H L hL hLe Tb hTa hTL hD hrt
  have hκσ : 0 < Tb.κ₁ * Tb.threshold ^ 2 := by
    have hσ := hD.σ_pos
    have hκ : 0 < Tb.κ₁ := lt_min (by have := hD.κ_pos; linarith) (div_pos hD.cE_pos (by positivity))
    positivity
  have hLTb : 2 ≤ Tb.side := by
    have := hD.L_ge
    omega
  obtain ⟨y₃, hy₃, Hnum⟩ :=
    exists_large_coupling_bound Tb.side hLTb (C₁ Tb) (C₂ Tb) (Tb.κ₁ * Tb.threshold ^ 2) hκσ
  refine ⟨max (max y₀ y₃) (max Tb.floorMin (((Tb.side * Tb.n₀ : ℕ) : ℝ) ^ 100)), fun y hy hR hW => ?_⟩
  have hyy₀ : y₀ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hyy₃ : y₃ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hyTb : Tb.floorMin ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hyn : ((Tb.side * Tb.n₀ : ℕ) : ℝ) ^ 100 ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  obtain ⟨P₂, P₃, P₄, P₅, P₆, P₇⟩ := Y y hyy₀ hR hW
  have hfit := hD.fits y hyTb
  intro T S β k hrun hS e G κ hside hle hκ
  have hy1 : 1 ≤ y := hy₃.trans hyy₃
  have hL1 : 1 < (Tb.stepParameters y).side := hLTb
  have hLge : 2 ^ 16 ≤ (Tb.stepParameters y).side := hfit.L_ge
  have hcoup := hrun.onFamily.coupling_eq
  have htab := hrun.onFamily.onFamily
  have hxge : ∀ j ≤ k, y ≤ (T.stage j).coupling := fun j hj => (htab j hj).le_coupling
  have hβ : y ≤ β := by
    have h := hxge 0 (Nat.zero_le _)
    rw [hcoup 0 (Nat.zero_le _)] at h
    exact h
  have hβ0 : 0 < β := by linarith
  have hmove : ∀ j < k, |(T.stage (j + 1)).coupling - (T.stage j).coupling| ≤ 2 * Tb.B := by
    intro j hj
    rw [hcoup (j + 1) (by omega), hcoup j (by omega)]
    refine couplingFlow_step_le (Tb.stepParameters y) hR β (hW β hβ) k (fun i hi => ?_) j hj
    have h := hxge i hi
    rw [hcoup i (by omega)] at h
    exact h
  have hrange : clusterRange y ≤ stageRange T k := clusterRange_mono (by linarith) (hxge k le_rfl)
  have hr16 : 2 ^ 16 ≤ clusterRange y := hfit.range_ge
  have hr1 : 1 ≤ stageRange T k := by omega
  have hc1 : 0 < Nat.clog (Tb.stepParameters y).side (2 ^ 7 * stageRange T k) := Nat.clog_pos hL1 (by omega)
  have hsidepow : G.side =
      (Tb.stepParameters y).side ^ Nat.clog (Tb.stepParameters y).side (2 ^ 7 * stageRange T k) := hside
  have hspos : 0 < G.side := by
    rw [hsidepow]
    exact pow_pos (by omega) _
  have hsle : G.side ≤ (Tb.stepParameters y).side ^ e := by omega
  have hce : Nat.clog (Tb.stepParameters y).side (2 ^ 7 * stageRange T k) ≤ e :=
    (Nat.pow_le_pow_iff_right hL1).1 (hsidepow ▸ hsle)
  have hge : 2 ^ 7 * stageRange T k ≤ G.side := by
    rw [hsidepow]
    exact Nat.le_pow_clog hL1 _
  have he1 : e ≠ 0 := by omega
  obtain ⟨q, hq⟩ : ∃ q, (Tb.stepParameters y).side ^ e = G.side * q :=
    ⟨(Tb.stepParameters y).side ^ (e - Nat.clog (Tb.stepParameters y).side (2 ^ 7 * stageRange T k)), by
      rw [hsidepow, ← pow_add, Nat.add_sub_cancel' hce]⟩
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, mul_zero] at hq
      exact absurd hq (pow_ne_zero _ (by omega))
    · exact h
  have hFit : G.Compatible (2 * (Tb.stepParameters y).side ^ e) := ⟨hspos, ⟨q, by rw [hq]; ring⟩⟩
  have hdiv : 2 * (Tb.stepParameters y).side ^ e / G.side = 2 * q :=
    Nat.div_eq_of_eq_mul_left hspos (by rw [hq]; ring)
  have hdvd : (Tb.stepParameters y).side ∣ 2 * (Tb.stepParameters y).side ^ e :=
    Dvd.dvd.mul_left (dvd_pow_self _ he1) 2
  have hLe' : (Tb.stepParameters y).side ≤ (Tb.stepParameters y).side ^ e := Nat.le_self_pow he1 _
  have h64 : 64 ≤ 2 * (Tb.stepParameters y).side ^ e := by omega
  have hLn : (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ 2 * (Tb.stepParameters y).side ^ e := by
    have h := le_clusterRange (Tb.side * Tb.n₀) hyn
    have h' : (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ clusterRange y := h
    omega
  have hcut : ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn := by
    have h := (htab 0 (Nat.zero_le _)).barrierFn_eq
    have h' : T.base.barrierFn = Tb.cutoff := h
    rw [h']
    exact hD.cut
  obtain ⟨Pm, Pmap⟩ := h₁ (Tb.stepParameters y) hfit T S β hβ0 hcut hrun.measurable hS k
    (2 * (Tb.stepParameters y).side ^ e) hdvd h64
  have hloc : ∀ κ', CellEventIsLocal T S k (2 * (Tb.stepParameters y).side ^ e)
      (G.cell (2 * (Tb.stepParameters y).side ^ e) κ') :=
    fun κ' => P₂ T S β k hrun hS _ G κ' hdvd h64 hFit
  have hLside : ((Tb.stepParameters y).side : ℤ) ∣ (G.side : ℤ) := by
    rw [hsidepow]
    push_cast
    exact dvd_pow_self _ hc1.ne'
  have hcarry : ∀ κ' ∈ G.sameParityIndices (2 * (Tb.stepParameters y).side ^ e) κ,
      ∀ W : TorusField (fineSide (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ e)),
      cellCopy (CellGrid.refineBy (Tb.stepParameters y).side k G) κ κ'
          (cellEventProb T S k (2 * (Tb.stepParameters y).side ^ e)
            (G.cell (2 * (Tb.stepParameters y).side ^ e) κ)) W =
        cellEventProb T S k (2 * (Tb.stepParameters y).side ^ e)
          (G.cell (2 * (Tb.stepParameters y).side ^ e) κ') W := by
    intro κ' hκ' W
    have h2 : ∀ i, (2 : ℤ) ∣ κ' i - κ i := (Finset.mem_filter.mp hκ').2
    unfold cellCopy
    rw [pullbackBy_reflectionTo_eq_translate _ κ κ' h2 W]
    have hv : ∀ i, ((Tb.stepParameters y).side : ℤ) ∣ (G.side : ℤ) * (κ' i - κ i) :=
      fun i => Dvd.dvd.mul_right hLside _
    have hT := (P₇ T S β 0 0 k e hrun hS hLn (fun i => (G.side : ℤ) * (κ' i - κ i)) hv
      (G.cell (2 * (Tb.stepParameters y).side ^ e) κ) W).2
    have hveq : (fun i => ((CellGrid.refineBy (Tb.stepParameters y).side k G).side : ℤ) * (κ' i - κ i)) =
        fun i => ((Tb.stepParameters y).side : ℤ) ^ k * ((G.side : ℤ) * (κ' i - κ i)) := by
      funext i
      rw [refineBy_side]
      push_cast
      ring
    rw [hveq, hT, image_cell_add]
  have hbound := measure_cellEvents_le T β k (2 * (Tb.stepParameters y).side ^ e) G κ
    ((T.stage k).coupling * Tb.κ₁ * Tb.threshold ^ 2)
    ((C₁ Tb + C₂ Tb * Real.log (T.stage k).coupling) * (2 * ((Tb.stepParameters y).side : ℝ) ^ e) ^ 4)
    (fun j => 8 * Tb.gasRate * (T.stage j).coupling * (100 * ((k : ℝ) - j)))
    (fun u κ' v hv hnot => P₃ T β k hrun k le_rfl _ u G κ' hFit v hv hnot)
    (fun Sj hSj A hA => P₄ T β k hrun e G κ Sj hside hle hSj A hA)
    (fun Yc hY => P₆ T β k hrun e G κ Yc hside hle hY)
  have hcard : (G.sameParityIndices (2 * (Tb.stepParameters y).side ^ e) κ).card = q ^ 4 :=
    card_sameParityIndices G _ q hdiv κ
  rw [hcard] at hbound
  have hprice := P₅ (fun j => (T.stage j).coupling) k hxge hmove
  have hsum : ∑ j ∈ Finset.range k, Real.exp (-(8 * Tb.gasRate * (T.stage j).coupling * (100 * ((k : ℝ) - j)))) ≤
      Real.exp (-((T.stage k).coupling * Tb.κ₁ * Tb.threshold ^ 2)) := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_)) hprice
    congr 1
    ring
  have hnum := Hnum (T.stage k).coupling (hyy₃.trans (hxge k le_rfl))
  have hnum' : (C₁ Tb + C₂ Tb * Real.log (T.stage k).coupling) * (G.side : ℝ) ^ 4 + 1 ≤
      (T.stage k).coupling * Tb.κ₁ * Tb.threshold ^ 2 / 32 := by
    rw [hside, mul_assoc (T.stage k).coupling]
    exact hnum
  have hpq : ((Tb.stepParameters y).side : ℝ) ^ e = (G.side : ℝ) * q := by exact_mod_cast hq
  have hVeq := volume_factor_eq (C₁ Tb + C₂ Tb * Real.log (T.stage k).coupling) (G.side : ℝ) _ q hpq
  obtain ⟨hB0, hBle⟩ := exp_mul_pow_bound hVeq hsum (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) hnum'
  have hmean := copyProductMean_le T S β k (2 * (Tb.stepParameters y).side ^ e) G hFit κ hloc Pm Pmap hcarry
    hB0 hbound
  refine ⟨cellEventProb_measurable T S (hloc κ),
    fun U => ⟨cellEventProb_nonneg T S _ _ _ _, cellEventProb_le_one T S _ _ _ _⟩,
    cellEventProb_dependsOnlyOn T S (hloc κ), ?_⟩
  refine chessboardNorm_le (CellGrid.refineBy (Tb.stepParameters y).side k G) β κ _
    (refineBy_indices (Tb.stepParameters y).side k _ (by omega) G) (M := q ^ 4) (pow_pos hqpos 4)
    (card_indices G _ q hdiv) ?_ (hmean.trans hBle)
  exact integral_nonneg fun W => Finset.prod_nonneg fun κ' _ => cellEventProb_nonneg T S _ _ _ _
end YangMills.Construction.CellWindows
end
