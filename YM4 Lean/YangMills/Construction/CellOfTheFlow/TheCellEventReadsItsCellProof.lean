import YangMills.Construction.CellOfTheFlow.BlocksOfACellAreACell
import YangMills.Construction.CellOfTheFlow.TheCellEventReadsItsCell
import YangMills.Construction.CellOfTheFlow.TheChainReadsItsCell
import YangMills.Construction.CellOfTheFlow.TheDrawOfTheNoiseIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsAboveABox
import YangMills.Construction.ClusterExpansionOfAStep.PriceOfTheHotLumps
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses BlockAverages LumpContours
namespace CellEventLocality
section Sets
variable {n : ℕ} [NeZero n] {L : ℕ} [NeZero L]
private theorem mem_sitesInBlocks_iff (S : Finset (TorusSite n)) (x : TorusSite (n * L)) :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.Construction.CongruentBoxes.mem_sitesInBlocks <;> assumption
private theorem interiorAtDepth_antitone {a b : ℕ} (h : b ≤ a) (c : Finset (TorusSite n)) :
    interiorAtDepth a c ⊆ interiorAtDepth b c := by
  classical
  intro v hv
  have hmem := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hmem.1, fun w hw => h.trans (hmem.2 w hw)⟩
private theorem chainComponents_subset {m : ℕ} [NeZero m] (r : ℕ) (X : Finset (TorusSite m))
    {K : Finset (TorusSite m)} (hK : K ∈ chainComponents r X) : K ⊆ X := by apply _root_.YangMills.Construction.TorusLumps.subset_of_mem_chainComponents <;> assumption
private theorem windowSeeds_congr {C C' : Finset (TorusSite n)} {bad bad' : Finset (TorusBond (n * L))}
    (Yw : Finset (TorusSite (n * L))) {D : Finset (TorusSite n)} (hC : ∀ z ∈ D, z ∈ C ↔ z ∈ C')
    (hb : ∀ b : TorusBond (n * L), b.1 ∈ sitesInBlocks L D → (b ∈ bad ↔ b ∈ bad')) :
    windowSeeds L bad Yw C (sitesInBlocks L D) = windowSeeds L bad' Yw C' (sitesInBlocks L D) := by
  classical
  ext x
  unfold windowSeeds
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_image]
  refine and_congr_left fun hx => ?_
  have hbond : (∃ e ∈ bad, e.1 = x) ↔ ∃ e ∈ bad', e.1 = x := by
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, (hb e hx).1 he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, (hb e hx).2 he, rfl⟩
  have hsite : x ∈ sitesInBlocks L C ↔ x ∈ sitesInBlocks L C' := by
    rw [mem_sitesInBlocks_iff, mem_sitesInBlocks_iff]
    exact hC _ ((mem_sitesInBlocks_iff D x).1 hx)
  rw [hbond, hsite]
private theorem upperAttached_congr (r : ℕ) {X Z Z' W : Finset (TorusSite (n * L))} (hX : X ⊆ W)
    (h : ∀ x ∈ W, x ∈ Z ↔ x ∈ Z') : upperAttached L r X Z W = upperAttached L r X Z' W := by
  classical
  unfold upperAttached
  congr 1
  refine Finset.filter_congr fun K hK => ?_
  have hKX := chainComponents_subset _ _ hK
  have hne : (K ∩ Z).Nonempty ↔ (K ∩ Z').Nonempty := by
    constructor
    · rintro ⟨x, hx⟩
      have hx' := Finset.mem_inter.mp hx
      exact ⟨x, Finset.mem_inter.mpr ⟨hx'.1, (h x (hX (hKX hx'.1))).1 hx'.2⟩⟩
    · rintro ⟨x, hx⟩
      have hx' := Finset.mem_inter.mp hx
      exact ⟨x, Finset.mem_inter.mpr ⟨hx'.1, (h x (hX (hKX hx'.1))).2 hx'.2⟩⟩
  rw [hne]
private theorem windowZone_congr (r : ℕ) (θ : Finset (TorusSite (n * L))) {C C' D : Finset (TorusSite n)}
    (hC : ∀ z ∈ D, z ∈ C ↔ z ∈ C') : windowZone L r θ C D = windowZone L r θ C' D := by
  classical
  ext z
  unfold windowZone
  simp only [Finset.mem_inter, Finset.mem_union]
  exact and_congr_left fun hz => by rw [hC z hz]
end Sets
private theorem measurableSet_of_measurable_fibres {X D : Type} [MeasurableSpace X] [Countable D] (f : X → D)
    (hf : ∀ d, MeasurableSet {x | f x = d}) (P : D → Prop) : MeasurableSet {x | P (f x)} := by
  have e : {x | P (f x)} = ⋃ d ∈ {d | P d}, {x | f x = d} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨d, h, h'⟩ => h' ▸ h⟩
  rw [e]
  exact MeasurableSet.biUnion (Set.to_countable _) fun d _ => hf d
abbrev _root_.YangMills.SharedProofs.p26374 := @measurableSet_of_measurable_fibres
private theorem measurableSet_hotCoreSites_eq {R : StepSetup} {n : ℕ} [NeZero n] (hadm : R.params.Admissible)
    (hdvd : R.params.side ∣ n) (C : Finset (TorusSite n)) :
    MeasurableSet {V : TorusField n | hotCoreSites R V = C} :=
  measurableSet_of_measurable_fibres (fun V : TorusField n => torusHotLumps R.params V)
    (measurableSet_torusHotLumps_eq hadm hdvd)
    fun H => thickening (2 * R.nextRange) (H.biUnion id) = C
abbrev _root_.YangMills.SharedProofs.p8979 := @measurableSet_hotCoreSites_eq
variable {ℓ : StepParameters}
private theorem upperZone_congr (T : StageTower ℓ) (k s : ℕ) {n : ℕ} [NeZero n] {C C' : Finset (TorusSite n)}
    {bad bad' : Finset (TorusBond (n * ℓ.side))} (Yw : Finset (TorusSite (n * ℓ.side))) (c : Finset (TorusSite n))
    (hC : ∀ z ∈ interiorAtDepth (4 * stageRange T (s + 1)) c, z ∈ C ↔ z ∈ C')
    (hb : ∀ b : TorusBond (n * ℓ.side),
      b.1 ∈ sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T k s) c) → (b ∈ bad ↔ b ∈ bad')) :
    upperZone T k s C bad Yw c = upperZone T k s C' bad' Yw c := by
  have hC' : ∀ z ∈ interiorAtDepth (blockDepth T k s) c, z ∈ C ↔ z ∈ C' := fun z hz =>
    hC z (interiorAtDepth_antitone (le_max_left _ _) c hz)
  have hX : windowSeeds ℓ.side bad' Yw C' (sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T k s) c)) ⊆
      sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T k s) c) := by
    unfold windowSeeds
    exact Finset.inter_subset_right
  have hA : upperAttached ℓ.side (stageRange T s)
        (windowSeeds ℓ.side bad' Yw C' (sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T k s) c)))
        (sitesInBlocks ℓ.side C) (sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T k s) c)) =
      upperAttached ℓ.side (stageRange T s)
        (windowSeeds ℓ.side bad' Yw C' (sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T k s) c)))
        (sitesInBlocks ℓ.side C') (sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T k s) c)) :=
    upperAttached_congr _ hX fun x hx => by
      rw [mem_sitesInBlocks_iff, mem_sitesInBlocks_iff]
      exact hC' _ ((mem_sitesInBlocks_iff _ x).1 hx)
  unfold upperZone
  rw [windowSeeds_congr Yw hC' hb, hA, windowZone_congr _ _ hC']
private theorem upperHull_succ_eq (T : StageTower ℓ) (k s n : ℕ) [NeZero n] (u : MarkedSample ℓ (s + 1) n)
    (c : Finset (TorusSite n)) : upperHull T k (s + 1) n u c =
      interiorAtDepth (windowDepth T k (s + 1)) c ∩ thickening (stageRange T (s + 1) / 2)
        (upperZone T k s (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.2
          (upperHull T k s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c)) c) := rfl
private theorem measurableSet_upperHull_eq (T : StageTower ℓ) (k : ℕ) (hadm : ℓ.Admissible) (s : ℕ) :
    ∀ (n : ℕ) [NeZero n], ℓ.side ∣ n → ∀ (c a : Finset (TorusSite n)),
      MeasurableSet {u : MarkedSample ℓ s n | upperHull T k s n u c = a} := by
  induction s with
  | zero =>
    intro n _ hdvd c a
    exact measurableSet_of_measurable_fibres (fun W : TorusField n => torusHotLumps ℓ W)
      (measurableSet_torusHotLumps_eq hadm hdvd)
      fun H => thickening (2 * clusterRange T.base.coupling) (H.biUnion id) ∩
        interiorAtDepth (windowDepth T k 0) c = a
  | succ s ih =>
    intro n _ hdvd c a
    classical
    have hcore : ∀ C : Finset (TorusSite n), MeasurableSet {u : MarkedSample ℓ (s + 1) n |
        hotCoreSites (T.stage s).toStepSetup u.2.2.1 = C} := fun C =>
      (measurable_fst.comp (measurable_snd.comp measurable_snd) :
        Measurable fun u : MarkedSample ℓ (s + 1) n => u.2.2.1)
        (measurableSet_hotCoreSites_eq (R := (T.stage s).toStepSetup) hadm hdvd C)
    have hbonds : ∀ B : BondSet (n * ℓ.side), MeasurableSet {u : MarkedSample ℓ (s + 1) n | u.2.2.2 = B} :=
      fun B =>
      (measurable_snd.comp (measurable_snd.comp measurable_snd) :
        Measurable fun u : MarkedSample ℓ (s + 1) n => u.2.2.2) (MeasurableSpace.measurableSet_top (s := {B}))
    have hlower : ∀ Y : Finset (TorusSite (n * ℓ.side)), MeasurableSet {u : MarkedSample ℓ (s + 1) n |
        upperHull T k s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c) = Y} := fun Y =>
      (measurable_fst : Measurable fun u : MarkedSample ℓ (s + 1) n => u.1)
        (ih (n * ℓ.side) (Dvd.intro_left _ rfl) (sitesInBlocks ℓ.side c) Y)
    have hCount : Countable (Finset (TorusSite n) × BondSet (n * ℓ.side) × Finset (TorusSite (n * ℓ.side))) :=
      have : Countable (BondSet (n * ℓ.side)) := inferInstanceAs (Countable (Finset (TorusBond (n * ℓ.side))))
      inferInstance
    refine measurableSet_of_measurable_fibres
      (D := Finset (TorusSite n) × BondSet (n * ℓ.side) × Finset (TorusSite (n * ℓ.side)))
      (fun u : MarkedSample ℓ (s + 1) n => (hotCoreSites (T.stage s).toStepSetup u.2.2.1, u.2.2.2,
        upperHull T k s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c))) (fun d => ?_)
      (fun d => interiorAtDepth (windowDepth T k (s + 1)) c ∩ thickening (stageRange T (s + 1) / 2)
        (upperZone T k s d.1 d.2.1 d.2.2 c) = a)
    have e : {u : MarkedSample ℓ (s + 1) n | (hotCoreSites (T.stage s).toStepSetup u.2.2.1, u.2.2.2,
        upperHull T k s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c)) = d} =
        {u | hotCoreSites (T.stage s).toStepSetup u.2.2.1 = d.1} ∩ ({u | u.2.2.2 = d.2.1} ∩
          {u | upperHull T k s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c) = d.2.2}) := by
      ext u
      obtain ⟨d1, d2, d3⟩ := d
      simp [Prod.ext_iff]
    rw [e]
    exact (hcore _).inter ((hbonds _).inter (hlower _))
abbrev _root_.YangMills.SharedProofs.p56010 := @measurableSet_upperHull_eq
end CellEventLocality
open CellEventLocality in
theorem cellEventIsLocal (hch : chainLocalityStatement) (hdr : sampleChainMeasurableStatement)
    (hbl : cellBlocksEqRefinedCellStatement) : cellEventIsLocalStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, hrt, h⟩ := hch a ha
  refine ⟨L₀, rt₀, hrt, fun L hL hL₀ Tb h1 h2 h3 h4 => ?_⟩
  obtain ⟨y₀, hy⟩ := h L hL hL₀ Tb h1 h2 h3 h4
  refine ⟨max y₀ Tb.floorMin, fun y hy1 hr hw => ?_⟩
  have hadm : (Tb.stepParameters y).Admissible := h3.fits y ((le_max_right _ _).trans hy1)
  have hP := hy y ((le_max_left _ _).trans hy1) hr hw
  intro T S β k hrun hS m _ G κ hLm h64 hG
  obtain ⟨-, h2', h3'⟩ := hP T S β k hrun hS
  have key : ∀ s, s ≤ k → ∀ (n : ℕ) [NeZero n] (G : CellGrid) (κ : Fin 4 → ℤ), G.Compatible n →
      ∀ (U U' : TorusField (fineSide (Tb.stepParameters y).side s n))
        (ξ ξ' : ChainNoise (Tb.stepParameters y) s n),
        FieldsAgreeOn (cellBelow (Tb.stepParameters y).side s n (G.cell n κ)) U U' →
        NoiseAgreesOn (Tb.stepParameters y) s n (G.cell n κ) ξ ξ' →
        upperHull T k s n (sampleChain T S s n U ξ) (G.cell n κ) =
          upperHull T k s n (sampleChain T S s n U' ξ') (G.cell n κ) := by
    intro s
    induction s with
    | zero =>
      intro _ n _ G κ hG U U' ξ ξ' hU _
      ext z
      simp only [upperHull, sampleChain, Finset.mem_inter]
      exact and_congr_left fun hz => h2' n G κ hG U U' hU z hz
    | succ s ih =>
      intro hs n _ G κ hG U U' ξ ξ' hU hξ
      have hpos : 0 < (Tb.stepParameters y).side := Nat.pos_of_ne_zero (NeZero.ne _)
      have hF : (G.refine (Tb.stepParameters y).side).Compatible (n * (Tb.stepParameters y).side) := by
        refine ⟨Nat.mul_pos hG.side_pos hpos, ?_⟩
        show 2 * (G.side * (Tb.stepParameters y).side) ∣ n * (Tb.stepParameters y).side
        rw [← mul_assoc]
        exact Nat.mul_dvd_mul_right hG.two_mul_side_dvd _
      have hb := hbl (Tb.stepParameters y).side G n κ
      have hξ1 : NoiseAgreesOn (Tb.stepParameters y) s (n * (Tb.stepParameters y).side)
          (sitesInBlocks (Tb.stepParameters y).side (G.cell n κ)) ξ.1 ξ'.1 := hξ.1
      have hU1 : FieldsAgreeOn (cellBelow (Tb.stepParameters y).side s (n * (Tb.stepParameters y).side)
          (sitesInBlocks (Tb.stepParameters y).side (G.cell n κ))) U U' := hU
      have hY := ih (Nat.le_of_succ_le hs) (n * (Tb.stepParameters y).side)
        (G.refine (Tb.stepParameters y).side) κ hF U U' ξ.1 ξ'.1 (hb ▸ hU1) (hb ▸ hξ1)
      rw [← hb] at hY
      obtain ⟨hC, hB⟩ := h3' s hs n G κ hG U U' ξ ξ' hU hξ
      rw [upperHull_succ_eq, upperHull_succ_eq]
      have hY' : upperHull T k s (n * (Tb.stepParameters y).side) (sampleChain T S (s + 1) n U ξ).1
            (sitesInBlocks (Tb.stepParameters y).side (G.cell n κ)) =
          upperHull T k s (n * (Tb.stepParameters y).side) (sampleChain T S (s + 1) n U' ξ').1
            (sitesInBlocks (Tb.stepParameters y).side (G.cell n κ)) := hY
      rw [hY', upperZone_congr T k s _ (G.cell n κ) hC hB]
  refine ⟨?_, fun U U' ξ ξ' hU hξ => ?_⟩
  · have hset : MeasurableSet {u : MarkedSample (Tb.stepParameters y) k m | CellEvent T k m u (G.cell m κ)} :=
      measurableSet_of_measurable_fibres
        (fun u : MarkedSample (Tb.stepParameters y) k m => upperHull T k k m u (G.cell m κ))
        (fun d => measurableSet_upperHull_eq T k hadm k m hLm (G.cell m κ) d)
        fun d => (d ∩ interiorAtDepth (8 * stageRange T k) (G.cell m κ)).Nonempty
    exact hdr (Tb.stepParameters y) hadm T S hrun.measurable hS k m hLm h64 hset
  · unfold CellEvent
    rw [key k le_rfl m G κ hG U U' ξ ξ' hU hξ]
end YangMills.Construction.CellWindows
end
