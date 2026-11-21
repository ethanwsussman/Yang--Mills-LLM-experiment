import YangMills.Construction.CellOfTheFlow.TheDrawOfTheNoiseIsBorelProof
import YangMills.Construction.FourPointCondition.LawsAtALevelOfTheWindowProof
import YangMills.Construction.HullsInEveryVolume.ChessboardOnABareGrid
import YangMills.Construction.HullsInEveryVolume.CopiesByTranslationsOfTheChainProof
import YangMills.Construction.HullsInEveryVolume.ExponentialMomentOfTheSizes
import YangMills.Construction.LawByMomentsOfTheFlow.HullsInALimitFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullsInEveryVolume
open TorusFields TorusLumps RenormalizationStepParameters StepSettings StepReturn WeightedResponses HullTrees ChainNoise ChessboardGrids
private theorem eventually_and {P Q : ParameterAssignment → ResponseParameters → ℝ → Prop} (hP : EventuallyInParameters P)
    (hQ : EventuallyInParameters Q) : EventuallyInParameters fun Tb Kr y => P Tb Kr y ∧ Q Tb Kr y := by
  intro a ha
  obtain ⟨L₁, r₁, c₁, hr₁, h₁⟩ := hP a ha
  obtain ⟨L₂, r₂, c₂, hr₂, h₂⟩ := hQ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max c₁ c₂, fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hL hLm Tb e1 e2 hD hC hH hrt hcd
  obtain ⟨M₁, g₁⟩ := h₁ L hL (le_trans (le_max_left _ _) hLm) Tb e1 e2 hD hC hH (hrt.trans (min_le_left _ _))
    ((le_max_left _ _).trans hcd)
  obtain ⟨M₂, g₂⟩ := h₂ L hL (le_trans (le_max_right _ _) hLm) Tb e1 e2 hD hC hH (hrt.trans (min_le_right _ _))
    ((le_max_right _ _).trans hcd)
  refine ⟨max M₁ M₂, fun Kr hM e3 e4 hF hS => ?_⟩
  obtain ⟨y₁, k₁⟩ := g₁ Kr ((le_max_left _ _).trans hM) e3 e4 hF hS
  obtain ⟨y₂, k₂⟩ := g₂ Kr ((le_max_right _ _).trans hM) e3 e4 hF hS
  exact ⟨max y₁ y₂, fun y hy hR hH =>
    ⟨k₁ y ((le_max_left _ _).trans hy) hR hH, k₂ y ((le_max_right _ _).trans hy) hR hH⟩⟩
private structure ParameterFacts (Tb : ParameterAssignment) (Kr : ResponseParameters) (y : ℝ) : Prop where
  admissible : Tb.Admissible
  stepAdmissible : (Tb.stepParameters y).Admissible
  responseAdmissible : Kr.Admissible (Tb.stepParameters y)
  returns : ExpansionReturnsAt (Tb.stepParameters y)
  initial : ∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β)
private theorem eventually_parameterFacts : EventuallyInParameters ParameterFacts := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hD _ _ _ _
  exact ⟨0, fun Kr _ _ _ hF _ => ⟨Tb.floorMin, fun y hy hR hH => ⟨hD, hD.fits y hy, hF y, hR, hH⟩⟩⟩
private theorem flow_step_le {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {β : ℝ}
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) (j : ℕ)
    (h : ∀ i ≤ j, ℓ.y₁ ≤ (couplingFlow ℓ β i).1) :
    |(couplingFlow ℓ β (j + 1)).1 - (couplingFlow ℓ β j).1| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p4489 <;> assumption
private theorem stageCoupling_pos {Tb : ParameterAssignment} {Kr : ResponseParameters} {y g β : ℝ} {K m : ℕ}
    {T : StageTower (Tb.stepParameters y)} {u n : ℕ} (hF : ParameterFacts Tb Kr y)
    (hAt : HullChainAtLevel Tb y g β K m T u n) : 0 < stageCoupling T u := by
  have hflow := hAt.chain
  have hy1 : (1 : ℝ) ≤ y := hF.stepAdmissible.y₁_ge
  have hB : 0 < (Tb.stepParameters y).B := hF.stepAdmissible.B_pos
  have hfl : y ≤ (g ^ 2)⁻¹ := hflow.le_inv_sq
  have hab : windowUpper (Tb.stepParameters y) g ≤ β := hflow.upper_le
  have hwt : windowUpper (Tb.stepParameters y) g = (g ^ 2)⁻¹ + 2 * (Tb.stepParameters y).B := rfl
  have hcross := hflow.isFirst
  have hx : stageCoupling T u = (couplingFlow (Tb.stepParameters y) β u).1 :=
    hflow.follows u (by have := hAt.le; omega)
  rw [hx]
  rcases Nat.lt_or_ge u K with hu | hu
  · have := hcross.2 u hu
    linarith
  · have huK : u = K := le_antisymm hAt.le hu
    subst huK
    cases u with
    | zero =>
      show 0 < β
      linarith
    | succ j =>
      have h0 : HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β) := hF.initial β (by linarith)
      have hall : ∀ i ≤ j, (Tb.stepParameters y).y₁ ≤ (couplingFlow (Tb.stepParameters y) β i).1 := fun i hi => by
        have := hcross.2 i (Nat.lt_succ_of_le hi)
        show y ≤ _
        linarith
      have hs := flow_step_le hF.returns h0 j hall
      have hj := hcross.2 j (Nat.lt_succ_self j)
      have := (abs_le.mp hs).1
      linarith
private theorem cellIndex_parentBlock {L n : ℕ} [NeZero L] [NeZero n] (hL : Odd L) (g : MirrorGrid)
    (x : TorusSite (n * L)) : (g.atDepth L 1).cellIndex x = g.cellIndex (parentBlock L x) := by apply _root_.YangMills.SharedProofs.p15019 <;> assumption
private theorem atDepth_zero (g : MirrorGrid) (L : ℕ) : g.atDepth L 0 = g := by
  cases g
  simp [MirrorGrid.atDepth]
private theorem atDepth_succ {L : ℕ} (hL : Odd L) (g : MirrorGrid) (u : ℕ) :
    (g.atDepth L 1).atDepth L u = g.atDepth L (u + 1) := by apply _root_.YangMills.SharedProofs.p49727 <;> assumption
private theorem sitesUnder_subset_cellSites {L : ℕ} [NeZero L] (hL : Odd L) (u : ℕ) :
    ∀ (n : ℕ) [NeZero n] (g : MirrorGrid) (c : Fin 4 → ℕ),
      sitesUnder L u n (g.cellSites n c) ⊆ (g.atDepth L u).cellSites (fineSide L u n) c := by
  induction u with
  | zero =>
    intro n _ g c
    rw [atDepth_zero]
    exact subset_rfl
  | succ u ih =>
    intro n _ g c
    have e1 : sitesInBlocks L (g.cellSites n c) = (g.atDepth L 1).cellSites (n * L) c := by
      ext x
      simp only [sitesInBlocks, MirrorGrid.cellSites, Finset.mem_filter, Finset.mem_univ, true_and,
        cellIndex_parentBlock hL]
    show sitesUnder L u (n * L) (sitesInBlocks L (g.cellSites n c)) ⊆
      (g.atDepth L (u + 1)).cellSites (fineSide L u (n * L)) c
    rw [e1, ← atDepth_succ hL g u]
    exact ih (n * L) (g.atDepth L 1) c
private theorem sitesUnder_mono {L : ℕ} [NeZero L] (u : ℕ) :
    ∀ (n : ℕ) [NeZero n] {Q Q' : Finset (TorusSite n)}, Q ⊆ Q' → sitesUnder L u n Q ⊆ sitesUnder L u n Q' := by apply _root_.YangMills.SharedProofs.p53753 <;> assumption
private theorem noiseAgreeAbove_mono (ℓ : StepParameters) (u : ℕ) :
    ∀ (n : ℕ) [NeZero n] {Q Q' : Finset (TorusSite n)} {U U' : ChainNoise ℓ u n}, Q ⊆ Q' →
      NoiseAgreeAbove ℓ u n Q' U U' → NoiseAgreeAbove ℓ u n Q U U' := by apply _root_.YangMills.SharedProofs.p6852 <;> assumption
private theorem noiseAgreeAbove_refl (ℓ : StepParameters) (u : ℕ) :
    ∀ (n : ℕ) [NeZero n] (Q : Finset (TorusSite n)) (U : ChainNoise ℓ u n), NoiseAgreeAbove ℓ u n Q U U := by
  induction u with
  | zero => exact fun _ _ _ _ => trivial
  | succ u ih => exact fun n _ Q U => ⟨ih (n * ℓ.side) _ U.1, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
private theorem box_subset_cellSites {n : ℕ} [NeZero n] (z : TorusSite n) (R l : ℕ) (hR : 2 * R < l) (hl : l ≤ n) :
    HullTrees.box z R ⊆ (⟨l, fun i => ((z i).val : ℤ) - (R : ℤ) - 1⟩ : MirrorGrid).cellSites n 0 := by
  intro x hx
  have hx' : supDist x z ≤ R := by
    simp only [HullTrees.box, thickening, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      exists_eq_left] at hx
    exact hx
  simp only [MirrorGrid.cellSites, Finset.mem_filter, Finset.mem_univ, true_and]
  funext i
  simp only [MirrorGrid.cellIndex, Pi.zero_apply]
  have hd : ((x i - z i).valMinAbs).natAbs ≤ R :=
    (Finset.le_sup (f := fun i => ((x i - z i).valMinAbs).natAbs) (Finset.mem_univ i)).trans hx'
  set d : ℤ := (x i - z i).valMinAbs with hdd
  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ d + R by omega)
  have hel : e < l := by omega
  have key : x i - (((((z i).val : ℤ) - (R : ℤ) - 1 + 1 : ℤ)) : ZMod n) = ((e : ℕ) : ZMod n) := by
    have h1 : ((d : ℤ) : ZMod n) = x i - z i := ZMod.coe_valMinAbs _
    have h2 : (((e : ℕ) : ℤ) : ZMod n) = ((d + R : ℤ) : ZMod n) := by rw [he]
    rw [Int.cast_natCast] at h2
    rw [h2]
    push_cast
    rw [h1, ZMod.natCast_zmod_val]
    ring
  rw [key, ZMod.val_natCast_of_lt (hel.trans_le hl)]
  exact Nat.div_eq_of_lt hel
private theorem chainNoiseLaw_isProbability (ℓ : StepParameters) (s : ℕ) :
    ∀ (n : ℕ) [NeZero n], IsProbabilityMeasure (chainNoiseLaw ℓ s n) := by apply _root_.YangMills.SharedProofs.p2413 <;> assumption
private theorem measurable_pairTranslate (ℓ : StepParameters) (u n : ℕ) [NeZero n] (h : Fin 4 → ℤ) :
    Measurable (pairTranslate ℓ u n h) := by apply _root_.YangMills.SharedProofs.p68462 <;> assumption
private theorem measurableSet_of_fibres {X D : Type} [MeasurableSpace X] [Countable D] (f : X → D)
    (hf : ∀ d, MeasurableSet {x | f x = d}) (S : Set D) : MeasurableSet {x | f x ∈ S} := by
  have e : {x | f x ∈ S} = ⋃ d ∈ S, {x | f x = d} := by
    ext x
    constructor
    · intro h
      exact Set.mem_biUnion (show f x ∈ S from h) rfl
    · intro h
      obtain ⟨d, hd, hx⟩ := Set.mem_iUnion₂.1 h
      have hx' : f x = d := hx
      show f x ∈ S
      rw [hx']
      exact hd
  rw [e]
  exact MeasurableSet.biUnion (Set.to_countable S) fun d _ => hf d
private theorem measurable_of_fibres {X D Z : Type} [MeasurableSpace X] [Countable D] [MeasurableSpace Z]
    (f : X → D) (hf : ∀ d, MeasurableSet {x | f x = d}) (G : D → X → Z) (hG : ∀ d, Measurable (G d)) :
    Measurable fun x => G (f x) x := by apply _root_.YangMills.SharedProofs.p26930 <;> assumption
section LocalHull
variable {ℓ : StepParameters}
private abbrev StepIndexSets (ℓ : StepParameters) (n : ℕ) : Type :=
  Finset (TorusSite (n * ℓ.side)) × Finset (TorusBond (n * ℓ.side)) × Finset (TorusSite n)
open Classical in
private def coreZone (T : StageTower ℓ) (j n : ℕ) [NeZero n] (Q : Finset (TorusSite n)) (d : StepIndexSets ℓ n) :
    Finset (TorusSite n) :=
  (d.2.2 ∩ Q) ∪ (coreBlocks ℓ.side (T.stage j).toStepSetup.range (attachedSites ℓ.side
    (T.stage j).toStepSetup.range (d.2.1.filter fun b => b.1 ∈ sitesInBlocks ℓ.side Q) d.1 (d.2.2 ∩ Q)) ∩ Q)
open Classical in
private def hullZone (T : StageTower ℓ) (j n : ℕ) [NeZero n] (Q : Finset (TorusSite n)) (d : StepIndexSets ℓ n) :
    Finset (TorusSite n) :=
  thickening ((T.stage j).toStepSetup.nextRange / 2) (coreZone T j n Q d) ∩ Q
open Classical in
private def zoneSize (T : StageTower ℓ) (s₁ : ℝ) (j n : ℕ) [NeZero n] (Q : Finset (TorusSite n))
    (d : StepIndexSets ℓ n) (lo : TorusSite (n * ℓ.side) → ℝ) (y : TorusSite n) : ℝ :=
  if y ∈ coreZone T j n Q d then s₁ + ∑ z ∈ sitesInBlocks ℓ.side {y} ∩ d.1, lo z
  else if y ∈ hullZone T j n Q d then s₁ else 0
private def stepIndices (T : StageTower ℓ) (s₁ : ℝ) (j n : ℕ) [NeZero n] (Q : Finset (TorusSite n))
    (w : MarkedSample ℓ (j + 1) n) : StepIndexSets ℓ n :=
  ((localHullData T s₁ j (n * ℓ.side) w.1 (sitesInBlocks ℓ.side Q)).1, w.2.2.2,
    hotCoreSites (T.stage j).toStepSetup w.2.2.1)
private theorem localHullData_succ_snd (T : StageTower ℓ) (s₁ : ℝ) (j n : ℕ) [NeZero n] (Q : Finset (TorusSite n))
    (w : MarkedSample ℓ (j + 1) n) (y : TorusSite n) :
    (localHullData T s₁ (j + 1) n w Q).2 y = zoneSize T s₁ j n Q (stepIndices T s₁ j n Q w)
      (localHullData T s₁ j (n * ℓ.side) w.1 (sitesInBlocks ℓ.side Q)).2 y := rfl
private theorem localHullData_fibres (T : StageTower ℓ) (s₁ : ℝ)
    (hot : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (j : ℕ) : ∀ (n : ℕ) [NeZero n] (Q : Finset (TorusSite n)),
      (∀ A, MeasurableSet {w : MarkedSample ℓ j n | (localHullData T s₁ j n w Q).1 = A}) ∧
      ∀ y, Measurable fun w : MarkedSample ℓ j n => (localHullData T s₁ j n w Q).2 y := by
  induction j with
  | zero =>
    intro n _ Q
    refine ⟨fun A => ?_, fun y => measurable_const⟩
    let R : StepSetup := { (T.stage 0).toStepSetup with nextCoupling := T.base.coupling }
    exact measurableSet_of_fibres (X := TorusField n) (fun V => hotCoreSites R V) (fun d => hot R n d)
      {d | d ∩ Q = A}
  | succ j ih =>
    intro n _ Q
    letI := markedSampleMeasurableSpace ℓ j (n * ℓ.side)
    obtain ⟨ih1, ih2⟩ := ih (n * ℓ.side) (sitesInBlocks ℓ.side Q)
    have m1 : Measurable fun w : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n => w.1 := measurable_fst
    have m2 : Measurable fun w : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n => w.2 := measurable_snd
    have mV : Measurable fun w : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n => w.2.2.1 :=
      measurable_fst.comp (measurable_snd.comp m2)
    have mb : Measurable fun w : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n => w.2.2.2 :=
      measurable_snd.comp (measurable_snd.comp m2)
    have hf : ∀ d : StepIndexSets ℓ n, MeasurableSet {w : MarkedSample ℓ (j + 1) n | stepIndices T s₁ j n Q w = d} := by
      rintro ⟨a, b, c⟩
      have s1 := m1 (ih1 a)
      have s2 := mb (MeasurableSpace.measurableSet_top (s := ({b} : Set (BondSet (n * ℓ.side)))))
      have s3 := mV (hot (T.stage j).toStepSetup n c)
      refine (s1.inter (s2.inter s3)).congr (Set.ext fun w => ⟨fun h => Prod.ext h.1 (Prod.ext h.2.1 h.2.2),
        fun h => ⟨(Prod.mk.inj h).1, (Prod.mk.inj (Prod.mk.inj h).2).1, (Prod.mk.inj (Prod.mk.inj h).2).2⟩⟩)
    refine ⟨fun A => ?_, fun y => ?_⟩
    · exact measurableSet_of_fibres (stepIndices T s₁ j n Q) hf {d | hullZone T j n Q d = A}
    · refine measurable_of_fibres (stepIndices T s₁ j n Q) hf
        (fun d w => zoneSize T s₁ j n Q d (localHullData T s₁ j (n * ℓ.side) w.1 (sitesInBlocks ℓ.side Q)).2 y)
        fun d => ?_
      simp only [zoneSize]
      split_ifs
      · exact measurable_const.add (Finset.measurable_fun_sum _ fun z _ => (ih2 z).comp m1)
      · exact measurable_const
      · exact measurable_const
private theorem measurable_localScoreMoment (T : StageTower ℓ) (s₁ : ℝ)
    (hot : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (u n : ℕ) [NeZero n] (y : TorusSite n) (D : ℝ) (k : ℕ) : Measurable (localScoreMoment T s₁ u n y D k) := by
  obtain ⟨h1, h2⟩ := localHullData_fibres T s₁ hot u n (localHullBox T u y D)
  show Measurable fun w => localScoreMoment T s₁ u n y D k w
  simp only [localScoreMoment]
  exact Measurable.ite
    (measurableSet_of_fibres (fun w => (localHullData T s₁ u n w (localHullBox T u y D)).1) h1 {A | y ∈ A})
    ((h2 y).pow_const k) measurable_const
private theorem localHullData_bounded (T : StageTower ℓ) {s₁ : ℝ} (hs : 0 ≤ s₁) (j : ℕ) :
    ∀ (n : ℕ) [NeZero n], ∃ B : ℝ, 0 ≤ B ∧
      ∀ (w : MarkedSample ℓ j n) (Q : Finset (TorusSite n)) (y : TorusSite n),
        0 ≤ (localHullData T s₁ j n w Q).2 y ∧ (localHullData T s₁ j n w Q).2 y ≤ B := by
  induction j with
  | zero =>
    intro n _
    exact ⟨0, le_rfl, fun w Q y => ⟨le_rfl, le_rfl⟩⟩
  | succ j ih =>
    intro n _
    obtain ⟨B, hB, h⟩ := ih (n * ℓ.side)
    refine ⟨s₁ + (Fintype.card (TorusSite (n * ℓ.side)) : ℝ) * B, by positivity, fun w Q y => ?_⟩
    rw [localHullData_succ_snd]
    simp only [zoneSize]
    have hc : (0 : ℝ) ≤ (Fintype.card (TorusSite (n * ℓ.side)) : ℝ) * B := by positivity
    split_ifs
    · refine ⟨add_nonneg hs (Finset.sum_nonneg fun z _ => (h _ _ z).1), ?_⟩
      refine add_le_add_right ?_ _
      refine (Finset.sum_le_card_nsmul _ _ B fun z _ => (h _ _ z).2).trans ?_
      rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) hB
    · exact ⟨hs, by linarith⟩
    · exact ⟨le_rfl, by linarith⟩
private theorem siteSize_nonneg (T : StageTower ℓ) {s₁ : ℝ} (hs : 0 ≤ s₁) (u n : ℕ) [NeZero n]
    (w : MarkedSample ℓ u n) (y : TorusSite n) : 0 ≤ siteSize T s₁ u n w y := by apply _root_.YangMills.SharedProofs.p9879 <;> assumption
end LocalHull
private theorem pow_le_factorial_mul_exp {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    t ^ k ≤ 16 ^ k * (k.factorial : ℝ) * Real.exp (t / 16) := by
  have ht' : 0 ≤ t / 16 := by positivity
  have h : (t / 16) ^ k / (k.factorial : ℝ) ≤ Real.exp (t / 16) :=
    (Finset.single_le_sum (f := fun i => (t / 16) ^ i / (i.factorial : ℝ)) (fun i _ => by positivity)
      (Finset.self_mem_range_succ k)).trans (Real.sum_le_exp_of_nonneg ht' (k + 1))
  have hk : (0 : ℝ) < k.factorial := by positivity
  rw [div_le_iff₀ hk] at h
  calc t ^ k = 16 ^ k * (t / 16) ^ k := by rw [div_pow]; field_simp
    _ ≤ 16 ^ k * (Real.exp (t / 16) * (k.factorial : ℝ)) := by gcongr
    _ = _ := by ring
private theorem pow_sixteen_le_exp {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (t ^ k) ^ 16 ≤ (16 ^ k * (k.factorial : ℝ)) ^ 16 * Real.exp t := by
  have h := pow_le_pow_left₀ (by positivity) (pow_le_factorial_mul_exp ht k) 16
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring
section Core
variable {ℓ : StepParameters}
private structure MomentSetup (T : StageTower ℓ) (rule : NoiseRule ℓ) (β s₁ A : ℝ) (u n M : ℕ) [NeZero n]
    (z : TorusSite n) (D : ℝ) (k : ℕ) : Prop where
  odd : Odd ℓ.side
  large : 2 ^ 16 ≤ ℓ.side
  beta : 0 < β
  side : n = 2 * ℓ.side ^ M
  deep : 2 ≤ M + u
  wilson : IsProbabilityMeasure (wilsonLaw β (fineSide ℓ.side u n))
  law : IsProbabilityMeasure (markedSampleLaw T β u n)
  chain : Measurable fun p : TorusField (fineSide ℓ.side u n) × ChainNoise ℓ u n => rule.chain T u n p.1 p.2
  carries : ((wilsonLaw β (fineSide ℓ.side u n)).prod (chainNoiseLaw ℓ u n)).map
    (fun p => rule.chain T u n p.1 p.2) = markedSampleLaw T β u n
  borel : Measurable (localScoreMoment T s₁ u n z D k)
  bounded : ∃ B : ℝ, ∀ w, 0 ≤ localScoreMoment T s₁ u n z D k w ∧ localScoreMoment T s₁ u n z D k w ≤ B
  reads : DependsAbove ℓ u n (HullTrees.box z (⌊2 * D⌋₊ + 6 * stageRange T u)) (localScore rule T s₁ u n z D k)
  shift : ∀ (h : Fin 4 → ℤ) (p : TorusField (fineSide ℓ.side u n) × ChainNoise ℓ u n),
    localScore rule T s₁ u n z D k (pairTranslate ℓ u n (fun i => (ℓ.side : ℤ) * h i) p) =
      localScore rule T s₁ u n (z + siteOfInt fun i => (ℓ.side : ℤ) * h i) D k p
  below : ∀ (z' : TorusSite n) (w : MarkedSample ℓ u n),
    localScoreMoment T s₁ u n z' D k w ≤ siteSize T s₁ u n w z' ^ k
  nonneg : ∀ (z' : TorusSite n) (w : MarkedSample ℓ u n), 0 ≤ localScoreMoment T s₁ u n z' D k w
  sizes : ∀ (w : MarkedSample ℓ u n) (y : TorusSite n), 0 ≤ siteSize T s₁ u n w y
  integrable : Integrable (fun w => Real.exp (totalSize T s₁ u n w)) (markedSampleLaw T β u n)
  moment : ∫ w, Real.exp (totalSize T s₁ u n w) ∂(markedSampleLaw T β u n) ≤ Real.exp (A * (n : ℝ) ^ 4)
variable {T : StageTower ℓ} {rule : NoiseRule ℓ} {β s₁ A : ℝ} {u n M : ℕ} [NeZero n] {z : TorusSite n} {D : ℝ}
  {k : ℕ}
private theorem MomentSetup.rate_nonneg (S : MomentSetup T rule β s₁ A u n M z D k) : 0 ≤ A := by
  haveI := S.law
  have h1 : (1 : ℝ) ≤ ∫ w, Real.exp (totalSize T s₁ u n w) ∂(markedSampleLaw T β u n) := by
    have h := integral_mono (integrable_const (1 : ℝ)) S.integrable fun w => by
      show (1 : ℝ) ≤ Real.exp (totalSize T s₁ u n w)
      exact Real.one_le_exp (Finset.sum_nonneg fun y _ => S.sizes w y)
    simpa using h
  have h2 := h1.trans S.moment
  have h3 : 0 ≤ A * (n : ℝ) ^ 4 := by
    by_contra hc
    have := Real.exp_lt_exp.2 (not_le.mp hc)
    rw [Real.exp_zero] at this
    linarith
  have hn : (0 : ℝ) < (n : ℝ) ^ 4 := by
    have : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
    positivity
  exact (mul_nonneg_iff_of_pos_right hn).1 h3
private theorem MomentSetup.measurable_localScore (S : MomentSetup T rule β s₁ A u n M z D k) :
    Measurable (localScore rule T s₁ u n z D k) :=
  S.borel.comp S.chain
private theorem MomentSetup.isCellObservable (S : MomentSetup T rule β s₁ A u n M z D k) {g : MirrorGrid}
    {c : Fin 4 → ℕ} (hbox : HullTrees.box z (⌊2 * D⌋₊ + 6 * stageRange T u) ⊆ g.cellSites n c) {M₀ : ℝ}
    (hM₀ : 0 < M₀) :
    IsCellObservable ℓ g u n c fun p => min (localScore rule T s₁ u n z D k p) M₀ where
  measurable := S.measurable_localScore.min measurable_const
  bounded := ⟨M₀, fun p => by
    have h0 : 0 ≤ min (localScore rule T s₁ u n z D k p) M₀ := le_min (S.nonneg z _) hM₀.le
    rw [abs_of_nonneg h0]
    exact min_le_right _ _⟩
  nonneg := fun p => le_min (S.nonneg z _) hM₀.le
  depends := fun W W' U U' hW hU => by
    have := S.reads W W' U U'
      (fun b h1 h2 => hW b (sitesUnder_mono u n hbox h1) (sitesUnder_mono u n hbox h2))
      (noiseAgreeAbove_mono ℓ u n hbox hU)
    show min _ _ = min _ _
    rw [this]
private theorem isCellFunction_noiseExpectation (hodd : Odd ℓ.side) {g : MirrorGrid} {c : Fin 4 → ℕ}
    {Φ : TorusField (fineSide ℓ.side u n) × ChainNoise ℓ u n → ℝ} (hin : IsCellObservable ℓ g u n c Φ) :
    IsCellFunction (g.atDepth ℓ.side u) (fineSide ℓ.side u n) c (noiseExpectation ℓ u n Φ) := by
  haveI := chainNoiseLaw_isProbability ℓ u n
  obtain ⟨C, hC⟩ := hin.bounded
  refine ⟨?_, ⟨C, fun W => ?_⟩, fun W => integral_nonneg fun U => hin.nonneg _, fun W W' h => ?_⟩
  · exact (hin.measurable.stronglyMeasurable.integral_prod_right' (ν := chainNoiseLaw ℓ u n)).measurable
  · have := norm_integral_le_of_norm_le_const (μ := chainNoiseLaw ℓ u n) (f := fun U => Φ (W, U)) (C := C)
      (Filter.Eventually.of_forall fun U => by simpa using hC (W, U))
    show |∫ U, Φ (W, U) ∂(chainNoiseLaw ℓ u n)| ≤ C
    simpa using this
  · refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    exact hin.depends W W' U U
      (fun b h1 h2 => h b (sitesUnder_subset_cellSites hodd u n g c h1) (sitesUnder_subset_cellSites hodd u n g c h2))
      (noiseAgreeAbove_refl ℓ u n _ U)
private theorem integral_le_chessboardNormAt (hCh : chessboardEstimateStatement) {L M' N : ℕ} [NeZero N] {b : ℝ}
    {g : MirrorGrid} (hodd : Odd L) (h16 : 2 ^ 16 ≤ L) (hM : 2 ≤ M') (hb : 0 < b) (hN : N = 2 * L ^ M')
    (hg : IsGridOfTorus g L M') {c : Fin 4 → ℕ} (hc : c ∈ g.cellIndices N) {F : TorusField N → ℝ}
    (hF : IsCellFunction g N c F) :
    ∫ W, F W ∂(wilsonLaw b N) ≤ g.chessboardNormAt b N c F := by
  classical
  obtain ⟨h1, h2⟩ := hCh L M' N b g hodd h16 hM hb hN hg
  let F' : (Fin 4 → ℕ) → TorusField N → ℝ := fun c' => if c' = c then F else fun _ => 1
  have hall : ∀ c' ∈ g.cellIndices N, IsCellFunction g N c' (F' c') := by
    intro c' _
    by_cases e : c' = c
    · subst e
      simpa [F'] using hF
    · simp only [F', if_neg e]
      exact ⟨measurable_const, ⟨1, fun _ => by simp⟩, fun _ => zero_le_one, fun _ _ _ => rfl⟩
  have h := h1 F' hall
  have eL : ∀ W, ∏ c' ∈ g.cellIndices N, F' c' W = F W := fun W => by
    rw [Finset.prod_eq_single_of_mem c hc fun c' _ e => by simp [F', e]]
    simp [F']
  have eR : ∏ c' ∈ g.cellIndices N, g.chessboardNormAt b N c' (F' c') = g.chessboardNormAt b N c F := by
    rw [Finset.prod_eq_single_of_mem c hc fun c' hc' e => by
      simp only [F', if_neg e]
      exact (h2 c' hc').2]
    simp [F']
  simp only [eL] at h
  rwa [eR] at h
private theorem mem_cellIndices_atDepth (g : MirrorGrid) (L u n : ℕ) (hL : 0 < L) (c : Fin 4 → ℕ)
    (hc : c ∈ g.cellIndices n) : c ∈ (g.atDepth L u).cellIndices (fineSide L u n) := by
  have e : fineSide L u n / (g.atDepth L u).side = n / g.side := by
    rw [fineSide_eq]
    exact Nat.mul_div_mul_right _ _ (pow_pos hL u)
  simp only [MirrorGrid.cellIndices, e] at hc ⊢
  exact hc
private theorem MomentSetup.chessboardNormAt_le (S : MomentSetup T rule β s₁ A u n M z D k)
    (hCo : translatedCopiesBoundStatement) {g : MirrorGrid} {p : ℕ} (hp : 1 ≤ p) (hpM : p ≤ M)
    (hgs : g.side = ℓ.side ^ p) (h2 : 2 * g.side ≤ n) {c : Fin 4 → ℕ} (hc : c ∈ g.cellIndices n)
    (hbox : HullTrees.box z (⌊2 * D⌋₊ + 6 * stageRange T u) ⊆ g.cellSites n c) {M₀ : ℝ} (hM₀ : 0 < M₀) :
    (g.atDepth ℓ.side u).chessboardNormAt β (fineSide ℓ.side u n) c
        (noiseExpectation ℓ u n fun q => min (localScore rule T s₁ u n z D k q) M₀) ≤
      16 ^ k * (k.factorial : ℝ) * Real.exp (A * (g.side : ℝ) ^ 4) := by
  classical
  haveI := S.wilson
  haveI := chainNoiseLaw_isProbability ℓ u n
  have hLpos : 0 < ℓ.side := NeZero.pos _
  have hspos : 0 < g.side := by rw [hgs]; positivity
  have hcop := hCo ℓ β u n M g S.odd S.large S.beta S.side ⟨p, hp, hpM, hgs⟩ h2 c _ hc (S.isCellObservable hbox hM₀)
  set G : ℝ := 16 ^ k * (k.factorial : ℝ) with hG
  set q : ℕ := ℓ.side ^ (M - p) with hq
  have hnq : n = 2 * q * g.side := by
    rw [S.side, hq, hgs, mul_assoc, ← pow_add, Nat.sub_add_cancel hpM]
  have hqpos : 0 < q := by rw [hq]; positivity
  have hd1 : n / g.side = 2 * q := by rw [hnq]; exact Nat.mul_div_cancel _ hspos
  have hd2 : n / (2 * g.side) = q := by
    rw [hnq, show 2 * q * g.side = q * (2 * g.side) by ring]
    exact Nat.mul_div_cancel _ (by omega)
  have hcard : (g.evenTranslations n).card = q ^ 4 := by
    simp [MirrorGrid.evenTranslations, hd2, Fintype.card_piFinset]
  have hcc : numCells n g.side = 16 * q ^ 4 := by
    rw [numCells, hd1]
    ring
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  let he : (Fin 4 → ℕ) → Fin 4 → ℤ := fun e i => 2 * (ℓ.side : ℤ) ^ p' * (e i : ℤ)
  have hsh : ∀ e : Fin 4 → ℕ, (fun i => 2 * (g.side : ℤ) * (e i : ℤ)) = fun i => (ℓ.side : ℤ) * he e i := by
    intro e
    funext i
    simp only [he, hgs]
    push_cast
    ring
  let site : (Fin 4 → ℕ) → TorusSite n := fun e => z + siteOfInt fun i => (ℓ.side : ℤ) * he e i
  have hinj : Set.InjOn site (g.evenTranslations n : Set (Fin 4 → ℕ)) := by
    intro e he1 e' he2 h
    funext i
    have h1 : e i < q := by
      have := (Fintype.mem_piFinset.1 (Finset.mem_coe.1 he1)) i
      rw [hd2] at this
      exact Finset.mem_range.1 this
    have h2 : e' i < q := by
      have := (Fintype.mem_piFinset.1 (Finset.mem_coe.1 he2)) i
      rw [hd2] at this
      exact Finset.mem_range.1 this
    have h3 := congrFun (add_left_cancel h) i
    have hc1 := congrFun (hsh e) i
    have hc2 := congrFun (hsh e') i
    simp only [siteOfInt] at h3
    rw [← hc1, ← hc2] at h3
    have h4 : (((2 * g.side * e i : ℕ)) : ZMod n) = ((2 * g.side * e' i : ℕ) : ZMod n) := by
      push_cast at h3 ⊢
      exact h3
    have hlt : ∀ a, a < q → 2 * g.side * a < n := fun a ha => by
      rw [hnq, show 2 * q * g.side = 2 * g.side * q by ring]
      exact Nat.mul_lt_mul_of_pos_left ha (by omega)
    have h5 := congrArg ZMod.val h4
    rw [ZMod.val_natCast_of_lt (hlt _ h1), ZMod.val_natCast_of_lt (hlt _ h2)] at h5
    exact Nat.eq_of_mul_eq_mul_left (by omega) h5
  set Φ : TorusField (fineSide ℓ.side u n) × ChainNoise ℓ u n → ℝ :=
    fun q' => min (localScore rule T s₁ u n z D k q') M₀ with hΦ
  set Ψ : TorusField (fineSide ℓ.side u n) × ChainNoise ℓ u n → ℝ :=
    fun p' => ∏ e ∈ g.evenTranslations n, Φ (pairTranslate ℓ u n (fun i => 2 * (g.side : ℤ) * (e i : ℤ)) p') ^ 16
    with hΨ
  set Gf : ℝ := (G ^ 16) ^ (q ^ 4) with hGf
  let Θ : TorusField (fineSide ℓ.side u n) × ChainNoise ℓ u n → ℝ :=
    fun p' => Gf * Real.exp (totalSize T s₁ u n (rule.chain T u n p'.1 p'.2))
  have hΦ0 : ∀ q', 0 ≤ Φ q' := fun q' => le_min (S.nonneg z _) hM₀.le
  have hΨ0 : ∀ p', 0 ≤ Ψ p' := fun p' => Finset.prod_nonneg fun e _ => pow_nonneg (hΦ0 _) _
  have hpt : ∀ p', Ψ p' ≤ Θ p' := by
    intro p'
    set w := rule.chain T u n p'.1 p'.2 with hw
    have hterm : ∀ e ∈ g.evenTranslations n,
        Φ (pairTranslate ℓ u n (fun i => 2 * (g.side : ℤ) * (e i : ℤ)) p') ^ 16 ≤
          G ^ 16 * Real.exp (siteSize T s₁ u n w (site e)) := by
      intro e _
      have h1 : Φ (pairTranslate ℓ u n (fun i => 2 * (g.side : ℤ) * (e i : ℤ)) p') ≤
          siteSize T s₁ u n w (site e) ^ k := by
        refine (min_le_left _ _).trans ?_
        rw [hsh e, S.shift (he e) p']
        exact S.below (site e) w
      exact (pow_le_pow_left₀ (hΦ0 _) h1 16).trans (pow_sixteen_le_exp (S.sizes w _) k)
    have hsum : ∑ e ∈ g.evenTranslations n, siteSize T s₁ u n w (site e) ≤ totalSize T s₁ u n w := by
      rw [← Finset.sum_image (f := fun y => siteSize T s₁ u n w y) hinj]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun y _ _ => S.sizes w y
    calc Ψ p' ≤ ∏ e ∈ g.evenTranslations n, (G ^ 16 * Real.exp (siteSize T s₁ u n w (site e))) :=
          Finset.prod_le_prod (fun e _ => pow_nonneg (hΦ0 _) _) hterm
      _ = Gf * Real.exp (∑ e ∈ g.evenTranslations n, siteSize T s₁ u n w (site e)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, Real.exp_sum]
      _ ≤ Θ p' := by
          have : 0 ≤ Gf := by positivity
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hsum) this
  have hΘi : Integrable Θ ((wilsonLaw β (fineSide ℓ.side u n)).prod (chainNoiseLaw ℓ u n)) := by
    have h := S.integrable
    rw [← S.carries] at h
    exact (h.comp_measurable S.chain).const_mul Gf
  have hΦm : Measurable Φ := S.measurable_localScore.min measurable_const
  have hΨm : Measurable Ψ :=
    Finset.measurable_fun_prod _ fun e _ => (hΦm.comp (measurable_pairTranslate ℓ u n _)).pow_const 16
  have hΨi : Integrable Ψ ((wilsonLaw β (fineSide ℓ.side u n)).prod (chainNoiseLaw ℓ u n)) :=
    hΘi.mono' hΨm.aestronglyMeasurable (Filter.Eventually.of_forall fun p' => by
      rw [Real.norm_of_nonneg (hΨ0 p')]
      exact hpt p')
  have hmean : pairExpectation ℓ β u n Ψ ≤ Gf * Real.exp (A * (n : ℝ) ^ 4) := by
    have e1 : pairExpectation ℓ β u n Ψ =
        ∫ p', Ψ p' ∂((wilsonLaw β (fineSide ℓ.side u n)).prod (chainNoiseLaw ℓ u n)) :=
      (integral_prod Ψ hΨi).symm
    have e2 : ∫ p', Θ p' ∂((wilsonLaw β (fineSide ℓ.side u n)).prod (chainNoiseLaw ℓ u n)) =
        Gf * ∫ w, Real.exp (totalSize T s₁ u n w) ∂(markedSampleLaw T β u n) := by
      rw [integral_const_mul, ← S.carries, integral_map S.chain.aemeasurable]
      rw [S.carries]
      exact S.integrable.aestronglyMeasurable
    rw [e1]
    refine (integral_mono hΨi hΘi hpt).trans ?_
    rw [e2]
    exact mul_le_mul_of_nonneg_left S.moment (by positivity)
  have hfin : ((g.atDepth ℓ.side u).chessboardNormAt β (fineSide ℓ.side u n) c (noiseExpectation ℓ u n Φ)) ^
      (16 * q ^ 4) ≤ (G * Real.exp (A * (g.side : ℝ) ^ 4)) ^ (16 * q ^ 4) := by
    rw [← hcc]
    refine hcop.trans (hmean.trans (le_of_eq ?_))
    rw [hcc, mul_pow, ← Real.exp_nat_mul, hGf, ← pow_mul]
    congr 2
    have hnr : (n : ℝ) = 2 * (q : ℝ) * (g.side : ℝ) := by exact_mod_cast hnq
    rw [hnr]
    push_cast
    ring
  by_contra hlt
  have hpos : 0 ≤ G * Real.exp (A * (g.side : ℝ) ^ 4) := by positivity
  have := pow_lt_pow_left₀ (not_le.mp hlt) hpos (n := 16 * q ^ 4) (by positivity)
  exact absurd hfin (not_le.mpr this)
private theorem MomentSetup.integral_le_of_grid (S : MomentSetup T rule β s₁ A u n M z D k)
    (hCo : translatedCopiesBoundStatement) (hCh : chessboardEstimateStatement) {g : MirrorGrid} {p : ℕ}
    (hp : 1 ≤ p) (hpM : p ≤ M) (hgs : g.side = ℓ.side ^ p) (h2 : 2 * g.side ≤ n) {c : Fin 4 → ℕ}
    (hc : c ∈ g.cellIndices n) (hbox : HullTrees.box z (⌊2 * D⌋₊ + 6 * stageRange T u) ⊆ g.cellSites n c) :
    ∫ w, localScoreMoment T s₁ u n z D k w ∂(markedSampleLaw T β u n) ≤
      16 ^ k * (k.factorial : ℝ) * Real.exp (A * (g.side : ℝ) ^ 4) := by
  haveI := S.wilson
  haveI := chainNoiseLaw_isProbability ℓ u n
  obtain ⟨B, hB⟩ := S.bounded
  have hM₀ : 0 < |B| + 1 := by positivity
  have hin := S.isCellObservable hbox hM₀
  have hcell := isCellFunction_noiseExpectation S.odd hin
  have hN : fineSide ℓ.side u n = 2 * ℓ.side ^ (M + u) := by
    calc fineSide ℓ.side u n = n * ℓ.side ^ u := fineSide_eq _ _ _
      _ = (2 * ℓ.side ^ M) * ℓ.side ^ u := by rw [← S.side]
      _ = 2 * ℓ.side ^ (M + u) := by rw [pow_add]; ring
  have hgrid : IsGridOfTorus (g.atDepth ℓ.side u) ℓ.side (M + u) :=
    ⟨p + u, by omega, by omega, by
      show g.side * ℓ.side ^ u = ℓ.side ^ (p + u)
      rw [hgs, pow_add]⟩
  have hmean := integral_le_chessboardNormAt hCh S.odd S.large S.deep S.beta hN hgrid
    (mem_cellIndices_atDepth g ℓ.side u n (NeZero.pos _) c hc) hcell
  refine le_trans (le_of_eq ?_) (hmean.trans (S.chessboardNormAt_le hCo hp hpM hgs h2 hc hbox hM₀))
  have hΦeq : ∀ q, min (localScore rule T s₁ u n z D k q) (|B| + 1) = localScore rule T s₁ u n z D k q :=
    fun q => min_eq_left (((hB _).2.trans (le_abs_self B)).trans (by linarith))
  simp only [hΦeq]
  have hint : Integrable (localScore rule T s₁ u n z D k)
      ((wilsonLaw β (fineSide ℓ.side u n)).prod (chainNoiseLaw ℓ u n)) :=
    Integrable.of_bound S.measurable_localScore.aestronglyMeasurable B (Filter.Eventually.of_forall fun q => by
      have h := hB (rule.chain T u n q.1 q.2)
      show ‖localScoreMoment T s₁ u n z D k (rule.chain T u n q.1 q.2)‖ ≤ B
      rw [Real.norm_of_nonneg h.1]
      exact h.2)
  rw [← S.carries, integral_map S.chain.aemeasurable (by rw [S.carries]; exact S.borel.aestronglyMeasurable)]
  exact integral_prod _ hint
private theorem MomentSetup.integral_le_of_small (S : MomentSetup T rule β s₁ A u n M z D k) :
    ∫ w, localScoreMoment T s₁ u n z D k w ∂(markedSampleLaw T β u n) ≤
      16 ^ k * (k.factorial : ℝ) * Real.exp (A * (n : ℝ) ^ 4) := by
  have hpt : ∀ w, localScoreMoment T s₁ u n z D k w ≤
      16 ^ k * (k.factorial : ℝ) * Real.exp (totalSize T s₁ u n w) := fun w => by
    have hs := S.sizes w z
    have h1 : siteSize T s₁ u n w z ≤ totalSize T s₁ u n w :=
      Finset.single_le_sum (f := fun y => siteSize T s₁ u n w y) (fun y _ => S.sizes w y) (Finset.mem_univ z)
    refine (S.below z w).trans ((pow_le_factorial_mul_exp hs k).trans ?_)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (S.nonneg z))
    (S.integrable.const_mul _) (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left S.moment (by positivity)
end Core
theorem localHullMomentBound_proof (hCh : chessboardEstimateStatement) (hCo : translatedCopiesBoundStatement)
    (hLo : localHullSubsetStatement) (hRe : localHullLocalityStatement)
    (hEx : totalSizeExpMomentStatement) (hNo : noiseRepresentationStatement)
    (hBo : noiseChainMeasurableStatement) (hWh : ResponseInTheExpansion.chainMeasurabilityStatement) :
    localHullMomentBound := by
  obtain ⟨CE, hE⟩ := hEx
  refine ⟨fun Tb => 16 * CE Tb, ?_⟩
  have H := eventually_and (eventually_and hLo hRe) (eventually_and hE (eventually_and hNo eventually_parameterFacts))
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, h⟩ := H a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hL hLm Tb e1 e2 hD hC hH' hr hcd => ?_⟩
  obtain ⟨M, h⟩ := h L hL hLm Tb e1 e2 hD hC hH' hr hcd
  refine ⟨M, fun Kr hM e3 e4 hF hS => ?_⟩
  obtain ⟨y₀, h⟩ := h Kr hM e3 e4 hF hS
  refine ⟨y₀, fun y hy hR hH => ?_⟩
  obtain ⟨⟨hLo', hRe'⟩, hE', hNo', hFa⟩ := h y hy hR hH
  intro g β K m T u n _ hAt rule hrule z D k hD0 hk
  have hfit := hFa.stepAdmissible
  have hflow := hAt.chain
  have hLg : 2 ^ 16 ≤ (Tb.stepParameters y).side := hfit.L_ge
  have hL1 : 1 < (Tb.stepParameters y).side := by omega
  have hx := stageCoupling_pos hFa hAt
  have hβ : 0 < β := by
    have h1 : (1 : ℝ) ≤ y := hfit.y₁_ge
    have h2 : y ≤ (g ^ 2)⁻¹ := hflow.le_inv_sq
    have h3 : windowUpper (Tb.stepParameters y) g ≤ β := hflow.upper_le
    have h4 : windowUpper (Tb.stepParameters y) g = (g ^ 2)⁻¹ + 2 * (Tb.stepParameters y).B := rfl
    have h5 := hfit.B_pos
    linarith
  have hm : 2 ≤ m := by
    by_contra hlt
    have hvol : Tb.side * Tb.n₀ ≤ 2 * Tb.side ^ m := hflow.volume_le
    have hn0 : 4096 ≤ Tb.n₀ := hFa.admissible.n₀_ge
    have hLg' : 2 ^ 16 ≤ Tb.side := hLg
    have hm' : m = 0 ∨ m = 1 := by omega
    rcases hm' with rfl | rfl
    · simp only [pow_zero, mul_one] at hvol
      nlinarith
    · simp only [pow_one] at hvol
      nlinarith
  have hnM : n = 2 * (Tb.stepParameters y).side ^ (m + (K - u)) := by
    have h1 : n = torusSideAtLevel Tb.side K m u := hAt.side_eq
    rw [h1]
    show fineSide Tb.side (K - u) (2 * Tb.side ^ m) = 2 * Tb.side ^ (m + (K - u))
    rw [fineSide_eq, pow_add]
    ring
  have hdvd : (Tb.stepParameters y).side ∣ n := by
    rw [hnM]
    exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) 2
  have h64 : 64 ≤ n := by
    have h1 : (Tb.stepParameters y).side ≤ (Tb.stepParameters y).side ^ (m + (K - u)) :=
      Nat.le_self_pow (by omega) _
    omega
  have hco := hflow.marks
  obtain ⟨hhot, -, hlaw⟩ := hWh
  have hl := hlaw (Tb.stepParameters y) hfit hfit.depth_lt T hflow.cutoff_bottom hco
  have hs₁ : 0 ≤ Kr.s₁ := by
    have kf := hFa.responseAdmissible
    have h1 := kf.Kc_ge
    have h2 := kf.N₀_nonneg
    have h3 := hfit.a_ge
    have hC : 0 ≤ Kr.C₀ + 2 := by
      rw [kf.C₀_eq]
      linarith
    rw [kf.s₁_eq]
    exact add_nonneg (mul_nonneg (by positivity) hC) (by linarith)
  have hle := fun w => ((hLo' g β K m T).1 u n hAt w).1
  obtain ⟨B, hB0, hB⟩ := localHullData_bounded T hs₁ u n
  have hnon : ∀ (z' : TorusSite n) (w : MarkedSample (Tb.stepParameters y) u n),
      0 ≤ localScoreMoment T Kr.s₁ u n z' D k w := by
    intro z' w
    simp only [localScoreMoment]
    split_ifs
    · exact pow_nonneg (hB w _ z').1 k
    · exact le_rfl
  have hreach := hRe' g β K m T u n hAt rule hrule z D k hD0 hk
  have hexp := hE' g β K m T u n hAt
  have S : MomentSetup T rule β Kr.s₁ (CE Tb * Real.log (stageCoupling T u)) u n (m + (K - u)) z D k :=
    { odd := hfit.L_odd
      large := hfit.L_ge
      beta := hβ
      side := hnM
      deep := by omega
      wilson := (hl β 0 (fineSide (Tb.stepParameters y).side u n)).1
      law := (hl β u n).1
      chain := hBo _ hfit T rule hco hrule u n hdvd h64
      carries := (hNo' g β K m T hflow).2 rule hrule u n hAt
      borel := measurable_localScoreMoment T Kr.s₁ hhot u n z D k
      bounded := ⟨B ^ k, fun w => ⟨hnon z w, by
        simp only [localScoreMoment]
        split_ifs
        · exact pow_le_pow_left₀ (hB w _ z).1 (hB w _ z).2 k
        · exact pow_nonneg hB0 k⟩⟩
      reads := hreach.1
      shift := hreach.2
      below := by
        intro z' w
        simp only [localScoreMoment]
        split_ifs with hy'
        · exact pow_le_pow_left₀ (hB w _ z').1 ((hle w _).2 z' hy') k
        · exact pow_nonneg (siteSize_nonneg T hs₁ u n w z') k
      nonneg := hnon
      sizes := fun w y' => siteSize_nonneg T hs₁ u n w y'
      integrable := hexp.1
      moment := hexp.2 }
  have hA := S.rate_nonneg
  have hr : 1 ≤ stageRange T u := Nat.ceil_pos.2 (Real.rpow_pos_of_pos hx _)
  have hrR : (1 : ℝ) ≤ (stageRange T u : ℝ) := by exact_mod_cast hr
  set a : ℝ := 16 * D + 40 * (stageRange T u : ℝ) with ha'
  have ha40 : 40 ≤ a := by rw [ha']; linarith
  have hc2 : 1 < ⌈a⌉₊ := Nat.lt_ceil.2 (by norm_num; linarith)
  set p : ℕ := Nat.clog (Tb.stepParameters y).side ⌈a⌉₊ with hp
  have hp1 : 1 ≤ p := Nat.clog_pos hL1 hc2
  have hside : leastPowerAbove (Tb.stepParameters y).side ⌈a⌉₊ = (Tb.stepParameters y).side ^ p := rfl
  have hLa : 0 < ((Tb.stepParameters y).side : ℝ) := by
    exact_mod_cast (by omega : 0 < (Tb.stepParameters y).side)
  have hlow : a ≤ (((Tb.stepParameters y).side ^ p : ℕ) : ℝ) :=
    (Nat.le_ceil a).trans (by exact_mod_cast Nat.le_pow_clog hL1 _)
  have hup : (((Tb.stepParameters y).side ^ p : ℕ) : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) * a := by
    have h1 : (Tb.stepParameters y).side ^ (p - 1) < ⌈a⌉₊ := Nat.pow_pred_clog_lt_self hL1 hc2
    have h2 : (((Tb.stepParameters y).side ^ (p - 1) : ℕ) : ℝ) ≤ a := by
      have h3 : (Tb.stepParameters y).side ^ (p - 1) + 1 ≤ ⌈a⌉₊ := h1
      have h4 : (((Tb.stepParameters y).side ^ (p - 1) + 1 : ℕ) : ℝ) ≤ (⌈a⌉₊ : ℝ) := by exact_mod_cast h3
      have h5 : (⌈a⌉₊ : ℝ) < a + 1 := Nat.ceil_lt_add_one (by linarith)
      push_cast at h4 ⊢
      linarith
    have h6 : (Tb.stepParameters y).side ^ p =
        (Tb.stepParameters y).side * (Tb.stepParameters y).side ^ (p - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hp1]
    rw [h6]
    push_cast at h2 ⊢
    exact mul_le_mul_of_nonneg_left h2 hLa.le
  have hpMof : ∀ hs : 2 * (Tb.stepParameters y).side ^ p ≤ n, p ≤ m + (K - u) := by
    intro hs
    rw [hnM] at hs
    have h1 : (Tb.stepParameters y).side ^ p ≤ (Tb.stepParameters y).side ^ (m + (K - u)) := by omega
    exact (Nat.pow_le_pow_iff_right hL1).1 h1
  have hG0 : (0 : ℝ) ≤ 16 ^ k * (k.factorial : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · intro gr hgs h2 c hc hbox M₀ hM₀
    have hgs' : gr.side = (Tb.stepParameters y).side ^ p := hgs
    have hpM := hpMof (by rw [← hgs']; exact h2)
    refine (S.chessboardNormAt_le hCo hp1 hpM hgs' h2 hc hbox hM₀).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hG0)
    have h4 : (0 : ℝ) ≤ (gr.side : ℝ) ^ 4 := by positivity
    have h5 := mul_nonneg hA h4
    show CE Tb * Real.log (stageCoupling T u) * (gr.side : ℝ) ^ 4 ≤
      16 * CE Tb * Real.log (stageCoupling T u) * (gr.side : ℝ) ^ 4
    nlinarith
  · have hLax : (0 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) * a := by
      have : (0 : ℝ) ≤ a := by linarith
      positivity
    have hLa4 : (0 : ℝ) ≤ (((Tb.stepParameters y).side : ℝ) * a) ^ 4 := by positivity
    have hfin : ∀ v : ℝ, v ≤ 16 * (((Tb.stepParameters y).side : ℝ) * a) ^ 4 →
        16 ^ k * (k.factorial : ℝ) * Real.exp (CE Tb * Real.log (stageCoupling T u) * v) ≤
        16 ^ k * (k.factorial : ℝ) * Real.exp (16 * CE Tb * Real.log (stageCoupling T u) *
          (((Tb.stepParameters y).side : ℝ) * a) ^ 4) := by
      intro v hv
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hG0
      have := mul_le_mul_of_nonneg_left hv hA
      nlinarith
    by_cases h2 : 2 * (Tb.stepParameters y).side ^ p ≤ n
    · set R : ℕ := ⌊2 * D⌋₊ + 6 * stageRange T u with hRdef
      have hR : 2 * R < (Tb.stepParameters y).side ^ p := by
        have h1 : ((⌊2 * D⌋₊ : ℕ) : ℝ) ≤ 2 * D := Nat.floor_le (by linarith)
        have h2' : ((2 * R : ℕ) : ℝ) < (((Tb.stepParameters y).side ^ p : ℕ) : ℝ) := by
          refine lt_of_lt_of_le ?_ hlow
          rw [hRdef, ha']
          push_cast
          linarith
        exact_mod_cast h2'
      have hle' : (Tb.stepParameters y).side ^ p ≤ n := by omega
      have hspos : 0 < (Tb.stepParameters y).side ^ p := by omega
      have hbox := box_subset_cellSites z R _ hR hle'
      have hmem : (0 : Fin 4 → ℕ) ∈ (⟨(Tb.stepParameters y).side ^ p,
          fun i => ((z i).val : ℤ) - (R : ℤ) - 1⟩ : MirrorGrid).cellIndices n := by
        refine Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 ?_
        exact Nat.div_pos hle' hspos
      refine (S.integral_le_of_grid hCo hCh hp1 (hpMof h2) rfl h2 hmem hbox).trans (hfin _ ?_)
      have h0 : (0 : ℝ) ≤ (((Tb.stepParameters y).side ^ p : ℕ) : ℝ) := by positivity
      have := pow_le_pow_left₀ h0 hup 4
      show (((Tb.stepParameters y).side ^ p : ℕ) : ℝ) ^ 4 ≤ _
      linarith
    · refine S.integral_le_of_small.trans (hfin _ ?_)
      have h3 : (n : ℝ) ≤ 2 * (((Tb.stepParameters y).side : ℝ) * a) := by
        have h4 : n ≤ 2 * (Tb.stepParameters y).side ^ p := by omega
        have h5 : (n : ℝ) ≤ 2 * (((Tb.stepParameters y).side ^ p : ℕ) : ℝ) := by exact_mod_cast h4
        linarith
      have h6 := pow_le_pow_left₀ (Nat.cast_nonneg n) h3 4
      rw [mul_pow] at h6
      norm_num at h6 ⊢
      exact h6
end YangMills.Construction.HullsInEveryVolume
end
