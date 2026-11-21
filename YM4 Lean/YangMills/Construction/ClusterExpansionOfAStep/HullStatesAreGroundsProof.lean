import YangMills.Construction.ClusterExpansionOfAStep.BaseLawIsAProduct
import YangMills.Construction.ClusterExpansionOfAStep.BondInCoordinates
import YangMills.Construction.ClusterExpansionOfAStep.FactorsAtACaseProof
import YangMills.Construction.ClusterExpansionOfAStep.GoodBondsMakeAColdPlaquette
import YangMills.Construction.ClusterExpansionOfAStep.GroundsOfAgreeingStatesProof
import YangMills.Construction.ClusterExpansionOfAStep.HullStatesAreGrounds
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps StepSettings StepGas StepCosts StepMarks RenormalizationStepParameters StepFrames
  BlockTrees BlockZones LumpContours BlockPlaces TorusBlocks TorusBalls TopLevelSites
  ColdStepAtMirrorFrames BlockSites HoleSites ColdChain
namespace HullStates
variable {R : StepSetup} {n : ℕ} [NeZero n]
section Parts
variable (q : CoarseState R n) {X : Finset (TorusSite n)}
theorem markAt_restrict_of_mem {z : TorusSite n} (hz : z ∈ X) : (q.restrict X).markAt z = q.markAt z := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GroundsAgreeNearProof.markAt_restrict <;> assumption
theorem markAt_restrict_of_not_mem {z : TorusSite n} (hz : z ∉ X) : (q.restrict X).markAt z = none := by
  classical
  unfold CoarseState.markAt CoarseState.restrict
  rw [dif_neg (fun h' => hz (Finset.mem_inter.mp h').2)]
theorem mem_of_configAt_eq_some {z : TorusSite n} {s : BlockLabels R.labels.Ω R.params.side} (h : q.markAt z = some s) : z ∈ q.1 := by
  classical
  by_contra hn
  unfold CoarseState.markAt at h
  rw [dif_neg hn] at h
  exact absurd h (by simp)
theorem mem_controlRegion_iff {y : TorusSite n} : y ∈ q.markedZone ↔ (q.markAt y).isSome = true := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.mem_controlRegion <;> assumption
theorem mem_controlRegion_restrict_iff {y : TorusSite n} : y ∈ (q.restrict X).markedZone ↔ y ∈ X ∧ y ∈ q.markedZone := by
  rw [mem_controlRegion_iff, mem_controlRegion_iff]
  by_cases h : y ∈ X
  · rw [markAt_restrict_of_mem q h]
    simp [h]
  · rw [markAt_restrict_of_not_mem q h]
    simp [h]
theorem fieldWithStoredLinks_restrict (W : TorusField (n * R.params.side)) {x : TorusSite (n * R.params.side)} (i : Fin 4)
    (h : parentBlock R.params.side x ∈ X) :
    (q.restrict X).fieldWithStoredLinks W x i = q.fieldWithStoredLinks W x i := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentAdmission.fieldWithStoredLinks_restrict <;> assumption
theorem labelAt_restrict_of_mem {z : TorusSite (n * R.params.side)} (h : parentBlock R.params.side z ∈ X) :
    (q.restrict X).labelAt z = q.labelAt z := by
  unfold CoarseState.labelAt
  rw [markAt_restrict_of_mem q h]
theorem labelAt_restrict_of_not_mem {z : TorusSite (n * R.params.side)} (h : parentBlock R.params.side z ∉ X) :
    (q.restrict X).labelAt z = Sum.inl () := by
  unfold CoarseState.labelAt
  rw [markAt_restrict_of_not_mem q h]
theorem mem_labelSet_iff_ne {z : TorusSite (n * R.params.side)} : z ∈ q.labelSet ↔ q.labelAt z ≠ Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.mem_labelSet <;> assumption
theorem mem_labelSet_restrict_iff {z : TorusSite (n * R.params.side)} :
    z ∈ (q.restrict X).labelSet ↔ parentBlock R.params.side z ∈ X ∧ z ∈ q.labelSet := by
  rw [mem_labelSet_iff_ne, mem_labelSet_iff_ne]
  by_cases h : parentBlock R.params.side z ∈ X
  · rw [labelAt_restrict_of_mem q h]
    simp [h]
  · rw [labelAt_restrict_of_not_mem q h]
    simp [h]
theorem parentBlock_mem_markedZone_of_mem_labelSet {z : TorusSite (n * R.params.side)} (h : z ∈ q.labelSet) :
    parentBlock R.params.side z ∈ q.markedZone := by
  rw [mem_controlRegion_iff]
  rw [mem_labelSet_iff_ne] at h
  unfold CoarseState.labelAt at h
  cases hs : q.markAt (parentBlock R.params.side z) with
  | none => rw [hs] at h; exact absurd rfl h
  | some s => rfl
theorem mem_storedBadBonds_iff {b : TorusBond (n * R.params.side)} : b ∈ q.storedBadBonds ↔
    ∃ s, q.markAt (parentBlock R.params.side b.1) = some s ∧ s.badBond (siteOffset b.1, b.2) = true := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.mem_storedBadBonds <;> assumption
theorem mem_storedBadBonds_restrict_iff {b : TorusBond (n * R.params.side)} :
    b ∈ (q.restrict X).storedBadBonds ↔ parentBlock R.params.side b.1 ∈ X ∧ b ∈ q.storedBadBonds := by
  rw [mem_storedBadBonds_iff, mem_storedBadBonds_iff]
  by_cases h : parentBlock R.params.side b.1 ∈ X
  · rw [markAt_restrict_of_mem q h]
    simp [h]
  · rw [markAt_restrict_of_not_mem q h]
    simp [h]
theorem mem_storedFieldBonds_iff {b : TorusBond (n * R.params.side)} : b ∈ q.storedFieldBonds ↔
    ∃ s, q.markAt (parentBlock R.params.side b.1) = some s ∧ s.linkValue (siteOffset b.1, b.2) ≠ Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.mem_storedFieldBonds <;> assumption
theorem mem_storedFieldBonds_restrict_iff {b : TorusBond (n * R.params.side)} :
    b ∈ (q.restrict X).storedFieldBonds ↔ parentBlock R.params.side b.1 ∈ X ∧ b ∈ q.storedFieldBonds := by
  rw [mem_storedFieldBonds_iff, mem_storedFieldBonds_iff]
  by_cases h : parentBlock R.params.side b.1 ∈ X
  · rw [markAt_restrict_of_mem q h]
    simp [h]
  · rw [markAt_restrict_of_not_mem q h]
    simp [h]
end Parts
structure HullStateHypotheses (δ lam σA cg : ℝ) (N : ℕ → ℝ) (V : TorusField n) (q : CoarseState R n) : Prop where
  wellPosed : R.IsWellPosed
  isBlockSide : IsBlockTorusSide R.params n
  coldChain : ColdChainConstants R.params.coupling δ R.params.side lam R.anchorRadius σA cg N
  two_threshold_le : 2 * R.params.threshold ≤ σA
  decay_le : N 0 * R.params.threshold * Real.exp (-(δ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) ≤ R.params.threshold / 128
  isHull : IsHullState R.params R.nextRange V q.1
  factor_ne_zero : ∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0
  restricted : ClusterExpansionOfAStep.HullRestrictedToComponent
variable {δ lam σA cg : ℝ} {N : ℕ → ℝ} {V : TorusField n} {q : CoarseState R n}
section Admitted
variable (H : HullStateHypotheses δ lam σA cg N V q)
include H
theorem side_odd : Odd R.params.side := H.wellPosed.admissible.L_odd
theorem side_mul_le_range : 2 ^ 40 * R.params.side ≤ R.range := H.wellPosed.range_ge_side
theorem one_le_side : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
theorem two_le_size : 2 ≤ n := by
  have h1 := H.isBlockSide.2
  have h2 := H.wellPosed.admissible.n₀_ge
  have h3 := H.wellPosed.admissible.L_ge
  nlinarith
theorem restrict_isAdmissibleState {X : Finset (TorusSite n)} (hX : X ∈ chainComponents R.nextRange q.1) :
    (q.restrict X).IsAdmissibleCoarseState (hotNeighbourhoodOn R X V) X := by
  classical
  by_contra hn
  apply H.factor_ne_zero X hX
  unfold coarseFactor admissibilityIndicator
  rw [if_neg hn]
  ring
theorem mem_component_of_supDist_le {X : Finset (TorusSite n)} (hX : X ∈ chainComponents R.nextRange q.1)
    {y y' : TorusSite n} (hy : y ∈ X) (hy' : y' ∈ q.1) (hd : _root_.YangMills.Construction.TorusFields.supDist y y' ≤ 16) : y' ∈ X := by
  have h1 := H.wellPosed.nextRange_ge
  exact mem_of_chainConnected_of_mem_chainComponents hX hy hy'
    (chainConnected_of_supDist_le (subset_of_mem_chainComponents hX hy) hy' (by omega))
theorem exists_component_of_mem_supportZone {y : TorusSite n} (h : y ∈ q.markedZone) :
    ∃ X ∈ chainComponents R.nextRange q.1, y ∈ X ∧ y ∈ (q.restrict X).markedZone := by
  have hs := (mem_controlRegion_iff q).mp h
  obtain ⟨s, hs'⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨X, hX, hy⟩ := exists_mem_chainComponents (r := R.nextRange) (mem_of_configAt_eq_some q hs')
  exact ⟨X, hX, hy, (mem_controlRegion_restrict_iff q).mpr ⟨hy, h⟩⟩
theorem markedZone_subset : q.markedZone ⊆ q.1 := fun y h => by
  have hs := (mem_controlRegion_iff q).mp h
  obtain ⟨s, hs'⟩ := Option.isSome_iff_exists.mp hs
  exact mem_of_configAt_eq_some q hs'
theorem supDist_parentBlock_unitStep_le (x : TorusSite (n * R.params.side)) (i : Fin 4) :
    _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side x)
      (parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i)) ≤ 2 := by
  have h1 := _root_.YangMills.Construction.TorusBlocks.supDist_parentBlock_le (side_odd H) x (x + TorusFields.unitStep (n * R.params.side) i)
  have h2 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le x i
  omega
theorem mem_storedFieldBonds_iff_ends (c : TorusBond (n * R.params.side)) :
    c ∈ q.storedFieldBonds ↔ parentBlock R.params.side c.1 ∈ q.markedZone ∧
      parentBlock R.params.side (c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈ q.markedZone := by
  classical
  constructor
  · intro hc
    obtain ⟨s, hs, _⟩ := (mem_storedFieldBonds_iff q).mp hc
    have hz : parentBlock R.params.side c.1 ∈ q.markedZone := (mem_controlRegion_iff q).mpr (by rw [hs]; rfl)
    obtain ⟨X, hX, hy, _⟩ := exists_component_of_mem_supportZone H hz
    have hon : c ∈ (q.restrict X).storedFieldBonds := (mem_storedFieldBonds_restrict_iff q).mpr ⟨hy, hc⟩
    rw [(restrict_isAdmissibleState H hX).fieldBonds_eq] at hon
    have h2 := Finset.mem_filter.mp hon
    exact ⟨hz, ((mem_controlRegion_restrict_iff q).mp h2.2.2).2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨X, hX, hy, _⟩ := exists_component_of_mem_supportZone H h1
    have hy' := mem_component_of_supDist_le H hX hy (markedZone_subset H h2)
      ((_root_.YangMills.Construction.HullStates.supDist_parentBlock_unitStep_le H c.1 c.2).trans (by norm_num))
    have hon : c ∈ bondsOverBlocks R.params.side (q.restrict X).markedZone :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_controlRegion_restrict_iff q).mpr ⟨hy, h1⟩,
        (mem_controlRegion_restrict_iff q).mpr ⟨hy', h2⟩⟩
    rw [← (restrict_isAdmissibleState H hX).fieldBonds_eq] at hon
    exact ((mem_storedFieldBonds_restrict_iff q).mp hon).2
theorem mem_hotNeighbourhoodOn_iff {X : Finset (TorusSite n)} (hX : X ∈ chainComponents R.nextRange q.1)
    {z : TorusSite n} (hz : z ∈ X) :
    z ∈ hotNeighbourhoodOn R X V ↔ z ∈ hotCoreSites R V :=
  H.restricted R n V q.1 X z H.wellPosed.admissible H.wellPosed.nextRange_ge H.isBlockSide.1 H.isHull hX hz
theorem parentBlock_mem_restrict_markedZone_of_near_attached {X : Finset (TorusSite n)}
    (hX : X ∈ chainComponents R.nextRange q.1) {u x : TorusSite (n * R.params.side)}
    (hu : u ∈ (q.restrict X).storedBadBonds.image Prod.fst ∪ (q.restrict X).labelSet ∪
      sitesInBlocks R.params.side (hotNeighbourhoodOn R X V))
    (hd : _root_.YangMills.Construction.TorusFields.supDist x u ≤ 4 * R.range) : parentBlock R.params.side x ∈ (q.restrict X).markedZone := by
  classical
  have hA := restrict_isAdmissibleState H hX
  rw [← hA.storedBlocks_eq]
  unfold storedBlocks
  refine Finset.mem_union_right _ ?_
  unfold coreBlocks
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · unfold sitesInBlocks
    simp
  · rw [hA.attached_eq]
    exact (mem_thickening _ _ _).mpr ⟨u, hu, hd⟩
theorem parentBlock_mem_markedZone_of_near_badBond {c : TorusBond (n * R.params.side)} (hc : c ∈ q.storedBadBonds)
    {x : TorusSite (n * R.params.side)} (hd : _root_.YangMills.Construction.TorusFields.supDist x c.1 ≤ 4 * R.range) :
    parentBlock R.params.side x ∈ q.markedZone := by
  classical
  obtain ⟨s, hs, _⟩ := (mem_storedBadBonds_iff q).mp hc
  have hz : parentBlock R.params.side c.1 ∈ q.markedZone := (mem_controlRegion_iff q).mpr (by rw [hs]; rfl)
  obtain ⟨X, hX, hy, _⟩ := exists_component_of_mem_supportZone H hz
  have hu : c.1 ∈ (q.restrict X).storedBadBonds.image Prod.fst ∪ (q.restrict X).labelSet ∪
      sitesInBlocks R.params.side (hotNeighbourhoodOn R X V) :=
    Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨c, (mem_storedBadBonds_restrict_iff q).mpr ⟨hy, hc⟩, rfl⟩))
  exact ((mem_controlRegion_restrict_iff q).mp (parentBlock_mem_restrict_markedZone_of_near_attached H hX hu hd)).2
theorem parentBlock_mem_markedZone_of_near_label {z : TorusSite (n * R.params.side)} (hc : z ∈ q.labelSet)
    {x : TorusSite (n * R.params.side)} (hd : _root_.YangMills.Construction.TorusFields.supDist x z ≤ 4 * R.range) :
    parentBlock R.params.side x ∈ q.markedZone := by
  classical
  obtain ⟨X, hX, hy, _⟩ := exists_component_of_mem_supportZone H (parentBlock_mem_markedZone_of_mem_labelSet q hc)
  have hu : z ∈ (q.restrict X).storedBadBonds.image Prod.fst ∪ (q.restrict X).labelSet ∪
      sitesInBlocks R.params.side (hotNeighbourhoodOn R X V) :=
    Finset.mem_union_left _ (Finset.mem_union_right _ ((mem_labelSet_restrict_iff q).mpr ⟨hy, hc⟩))
  exact ((mem_controlRegion_restrict_iff q).mp (parentBlock_mem_restrict_markedZone_of_near_attached H hX hu hd)).2
theorem parentBlock_mem_markedZone_of_near_hotCore {z : TorusSite (n * R.params.side)}
    (hc : parentBlock R.params.side z ∈ hotCoreSites R V) {x : TorusSite (n * R.params.side)}
    (hd : _root_.YangMills.Construction.TorusFields.supDist x z ≤ 4 * R.range) : parentBlock R.params.side x ∈ q.markedZone := by
  classical
  obtain ⟨X, hX, hy⟩ := exists_mem_chainComponents (r := R.nextRange) (H.isHull.1 hc)
  have hu : z ∈ (q.restrict X).storedBadBonds.image Prod.fst ∪ (q.restrict X).labelSet ∪
      sitesInBlocks R.params.side (hotNeighbourhoodOn R X V) := by
    refine Finset.mem_union_right _ ?_
    unfold sitesInBlocks
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_hotNeighbourhoodOn_iff H hX hy).mpr hc⟩
  exact ((mem_controlRegion_restrict_iff q).mp (parentBlock_mem_restrict_markedZone_of_near_attached H hX hu hd)).2
end Admitted
section Field
abbrev emptyFamilySetting (V : TorusField n) (q : CoarseState R n) : ChartSetting R n :=
  (hotCaseGround R V q).settingWithFamily GasFamily.empty
abbrev frameGaugeField (V : TorusField n) (q : CoarseState R n) : TorusField (n * R.params.side) :=
  (emptyFamilySetting V q).field 0
theorem fieldAt_empty (b : TorusBond (n * R.params.side)) :
    (GasFamily.empty : GasFamily R n).fieldAt b = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.fieldAt_empty <;> assumption
theorem emptyFamilySetting_fine : (emptyFamilySetting V q).fine = q.fieldWithStoredLinks (trivialField _) := by
  funext x i
  show (match (GasFamily.empty : GasFamily R n).fieldAt (x, i) with
    | Sum.inr g => g
    | Sum.inl _ => q.fieldWithStoredLinks (trivialField _) x i) = _
  rw [fieldAt_empty]
theorem isRecorded_hotCaseGround_iff (b : TorusBond (n * R.params.side)) :
    (hotCaseGround R V q).IsRecorded b ↔ b ∈ q.storedFieldBonds := by
  rw [mem_storedFieldBonds_iff]
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, fun e => ?_⟩
    rw [e] at h
    exact absurd h (by simp)
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    cases hv : s.linkValue (siteOffset b.1, b.2) with
    | inl u => exact absurd hv h
    | inr g => rfl
theorem mem_emptyFamilySetting_free_iff (b : TorusBond (n * R.params.side)) :
    b ∈ (emptyFamilySetting V q).free ↔ b ∈ markedBonds R (hotCoreSites R V) ∧ b ∉ q.storedFieldBonds := by
  classical
  show b ∈ (hotCaseGround R V q).freeBonds.filter (fun b => GasFamily.empty.fieldAt b = Sum.inl ()) ↔ _
  simp only [GasGround.freeBonds, Finset.mem_filter, fieldAt_empty, and_true, isRecorded_hotCaseGround_iff]
  rfl
theorem emptyFamilySetting_free_subset : (emptyFamilySetting V q).free ⊆ chartBonds R.params.side n := by
  classical
  intro b hb
  have h := ((mem_emptyFamilySetting_free_iff b).mp hb).1
  unfold markedBonds at h
  exact (Finset.mem_filter.mp h).1
theorem toImaginary_zero : toImaginary 0 = (0 : imaginaryQuaternions) := by apply _root_.YangMills.Construction.BondCoordinates.toImaginary_zero <;> assumption
section Coordinates
variable (H : HullStateHypotheses δ lam σA cg N V q)
include H
theorem norm_frameCoord_le (b : TorusBond (n * R.params.side)) :
    ‖((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
      R.anchorRadius := by
  obtain ⟨_, _, _, h1, h2, _⟩ := H.coldChain
  unfold frameCoord bondFrameCoord reflectedBondCoord
  have hρ := h1.le
  have key : ∀ {F : BlockFrame} (a : ℝ) (Q : Finset F.Cell) (V : F.GaugeField F.top) (c : F.Site F.depth × Fin 4),
      ‖(minimizingBondCoordinate a R.anchorRadius Q c V : ℍ[ℝ])‖ ≤ R.anchorRadius := by
    intro F a Q V c
    classical
    unfold minimizingBondCoordinate minimizingCoordinates
    split_ifs with h
    · have hs := h.choose_spec
      by_cases hb : c ∈ chordBonds Q
      · exact hs.2.1 c hb
      · rw [hs.1 c hb]
        simpa using hρ
    · simpa using hρ
  split_ifs
  · exact key _ _ _ _
  · exact key _ _ _ _
theorem chartCoord_frameGaugeField_of_mem_free {b : TorusBond (n * R.params.side)}
    (hb : b ∈ (emptyFamilySetting V q).free) :
    chartCoord R.params V (frameGaugeField V q) b = frameCoord R.params R.anchorRadius R.depth R.frameReach V b := by
  obtain ⟨_, _, _, _, h2, _⟩ := H.coldChain
  have hz : ‖(((emptyFamilySetting V q).frame b +
      toImaginary ((0 : FreeCoords (emptyFamilySetting V q).free) ⟨b, hb⟩) : imaginaryQuaternions) : ℍ[ℝ])‖ <
      Real.pi := by
    have e : (0 : FreeCoords (emptyFamilySetting V q).free) ⟨b, hb⟩ = 0 := rfl
    rw [e, toImaginary_zero, add_zero]
    have h3 : ‖(((emptyFamilySetting V q).frame b : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ R.anchorRadius :=
      norm_frameCoord_le H b
    have := Real.pi_gt_three
    linarith
  have h := chartCoord_field_of_mem_free (s := emptyFamilySetting V q) emptyFamilySetting_free_subset
    (side_odd H) (two_le_size H) 0 ⟨b, hb⟩ hz
  have e : (0 : FreeCoords (emptyFamilySetting V q).free) ⟨b, hb⟩ = 0 := rfl
  rw [e, toImaginary_zero, add_zero] at h
  exact h
theorem chartCoord_frameGaugeField_of_not_mem_free {b : TorusBond (n * R.params.side)}
    (hb : b ∉ (emptyFamilySetting V q).free) :
    chartCoord R.params V (frameGaugeField V q) b =
      chartCoord R.params V (q.fieldWithStoredLinks (trivialField _)) b := by
  have h := chartCoord_field_of_not_mem_free (s := emptyFamilySetting V q) emptyFamilySetting_free_subset
    (side_odd H) (two_le_size H) 0 hb
  rw [emptyFamilySetting_fine] at h
  exact h
theorem frameGaugeField_of_not_mem_free {b : TorusBond (n * R.params.side)}
    (hb : b ∉ (emptyFamilySetting V q).free) :
    frameGaugeField V q b.1 b.2 = q.fieldWithStoredLinks (trivialField _) b.1 b.2 := by
  have h := field_of_not_mem_free (s := emptyFamilySetting V q) (η := 0) hb
  rw [emptyFamilySetting_fine] at h
  exact h
theorem chartCoord_restrict_storedField {X : Finset (TorusSite n)} {b : TorusBond (n * R.params.side)}
    (h1 : parentBlock R.params.side b.1 ∈ X)
    (h2 : parentBlock R.params.side (b.1 + TorusFields.unitStep (n * R.params.side) b.2) ∈ X) :
    chartCoord R.params V (q.restrict X).storedField b =
      chartCoord R.params V (q.fieldWithStoredLinks (trivialField _)) b := by
  have t1 : blockGauge R.params.side (q.restrict X).storedField b.1 =
      blockGauge R.params.side (q.fieldWithStoredLinks (trivialField _)) b.1 :=
    blockGauge_congr (side_odd H) (two_le_size H) _ _ _ fun z i hz _ =>
      fieldWithStoredLinks_restrict q _ i (by rw [hz]; exact h1)
  have t2 : blockGauge R.params.side (q.restrict X).storedField (b.1 + TorusFields.unitStep (n * R.params.side) b.2) =
      blockGauge R.params.side (q.fieldWithStoredLinks (trivialField _))
        (b.1 + TorusFields.unitStep (n * R.params.side) b.2) :=
    blockGauge_congr (side_odd H) (two_le_size H) _ _ _ fun z i hz _ =>
      fieldWithStoredLinks_restrict q _ i (by rw [hz]; exact h2)
  have t3 : (q.restrict X).storedField b.1 b.2 = q.fieldWithStoredLinks (trivialField _) b.1 b.2 :=
    fieldWithStoredLinks_restrict q _ _ h1
  rw [chartCoord_eq, chartCoord_eq, t1, t2, t3]
theorem bondMark_restrict_ne_zero {X : Finset (TorusSite n)} (hX : X ∈ chainComponents R.nextRange q.1)
    {b : TorusBond (n * R.params.side)}
    (hm : b ∈ markedBonds R (hotCoreSites R V)) (h1 : parentBlock R.params.side b.1 ∈ X)
    (h2 : parentBlock R.params.side (b.1 + TorusFields.unitStep (n * R.params.side) b.2) ∈ X)
    (z1 : parentBlock R.params.side b.1 ∈ q.markedZone)
    (z2 : parentBlock R.params.side (b.1 + TorusFields.unitStep (n * R.params.side) b.2) ∈ q.markedZone)
    (hbad : b ∉ q.storedBadBonds) :
    bondMark R V (q.restrict X).storedField b ≠ 0 := by
  classical
  have hphi := H.factor_ne_zero X hX
  unfold coarseFactor at hphi
  have hmark : markFactorProduct V q X ≠ 0 := by
    intro h
    apply hphi
    rw [h]
    ring
  unfold markFactorProduct at hmark
  have hb : b ∈ markedBonds R (hotNeighbourhoodOn R X V) ∩ bondsOverBlocks R.params.side (q.restrict X).markedZone := by
    refine Finset.mem_inter.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (mem_controlRegion_restrict_iff q).mpr ⟨h1, z1⟩, (mem_controlRegion_restrict_iff q).mpr ⟨h2, z2⟩⟩⟩
    unfold markedBonds at hm ⊢
    obtain ⟨hc, hn⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨hc, fun h => hn ((mem_hotNeighbourhoodOn_iff H hX h1).mp h)⟩
  have hf := (Finset.prod_ne_zero_iff.mp hmark) b hb
  rw [if_neg (fun h => hbad ((mem_storedBadBonds_restrict_iff q).mp h).2)] at hf
  exact hf
end Coordinates
end Field
section Rim
variable (H : HullStateHypotheses δ lam σA cg N V q)
  (hGood : StepFrames.coldPlaquette_of_small_frameDeviation)
theorem supDist_le_two_of_mem_plaquetteVertices {m : ℕ} [NeZero m] {x z : TorusSite m} {μ ν : Fin 4}
    (hz : z ∈ plaquetteVertices x μ ν) : _root_.YangMills.Construction.TorusFields.supDist x z ≤ 2 := by apply _root_.YangMills.Construction.InBoxTransfer.supDist_le_two_of_mem_plaquetteVertices <;> assumption
theorem curvature_congr {m : ℕ} {W W' : TorusField m} {x : TorusSite m} {μ ν : Fin 4} (h1 : W x μ = W' x μ)
    (h2 : W (x + TorusFields.unitStep m μ) ν = W' (x + TorusFields.unitStep m μ) ν)
    (h3 : W (x + TorusFields.unitStep m ν) μ = W' (x + TorusFields.unitStep m ν) μ)
    (h4 : W x ν = W' x ν) : TorusFields.curvature W x μ ν = TorusFields.curvature W' x μ ν := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentAdmission.curvature_congr <;> assumption
include H in
theorem supDist_le_side_of_parentBlock_eq {x z : TorusSite (n * R.params.side)}
    (h : parentBlock R.params.side x = parentBlock R.params.side z) : _root_.YangMills.Construction.TorusFields.supDist x z ≤ R.params.side := by
  have h1 := _root_.YangMills.Construction.TorusBlocks.supDist_le_mul_supDist_parentBlock_add_one (side_odd H) x z
  rw [h, _root_.YangMills.Construction.TorusFields.supDist_self] at h1
  simpa using h1
include H hGood in
theorem curvature_lt_of_vertex_outside {x : TorusSite (n * R.params.side)} {μ ν : Fin 4} (hlt : μ < ν)
    {z₀ : TorusSite (n * R.params.side)} (hz₀ : z₀ ∈ plaquetteVertices x μ ν)
    (hout : parentBlock R.params.side z₀ ∉ q.markedZone) :
    TorusFields.curvature (frameGaugeField V q) x μ ν < R.params.threshold / 4 := by
  classical
  have hr := side_mul_le_range H
  have hL1 := one_le_side H
  have hclose : ∀ z ∈ plaquetteVertices x μ ν, _root_.YangMills.Construction.TorusFields.supDist z₀ z ≤ 4 := by
    intro z hz
    have h1 := _root_.YangMills.Construction.HullStates.supDist_le_two_of_mem_plaquetteVertices hz
    have h2 := _root_.YangMills.Construction.HullStates.supDist_le_two_of_mem_plaquetteVertices hz₀
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle z₀ x z
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm z₀ x] at h3
    omega
  have hC : ∀ z ∈ plaquetteVertices x μ ν, parentBlock R.params.side z ∉ hotCoreSites R V := by
    intro z hz hc
    exact hout (parentBlock_mem_markedZone_of_near_hotCore H hc (by have := hclose z hz; omega))
  have hradius : 16 ≤ R.range / 2 ^ 11 := by
    have : 2 ^ 40 ≤ R.range := by nlinarith
    omega
  refine hGood R.params δ lam R.anchorRadius σA cg N H.wellPosed.admissible H.coldChain H.two_threshold_le
    R.depth R.range R.nextRange n V
    (Finset.univ \ thickening lumpRange (torusHotSites R.params V)) (hotCoreSites R V) R.params.threshold
    ⟨H.wellPosed.range_le, H.wellPosed.nextRange_ge, hradius⟩ (Or.inl ⟨H.isBlockSide, rfl, rfl, rfl⟩) H.decay_le
    (frameGaugeField V q) x μ ν hlt hC ?_
  rintro b hb ⟨z, hz, hbz⟩
  have hσ := H.wellPosed.admissible.σ_pos
  by_cases hf : b ∈ (emptyFamilySetting V q).free
  · have e : frameDeviation R.params R.anchorRadius R.depth (R.range / 2 ^ 11) V (frameGaugeField V q) b = 0 := by
      unfold frameDeviation
      rw [chartCoord_frameGaugeField_of_mem_free H hf]
      exact sub_self _
    rw [e]
    simpa using (by positivity : 0 ≤ R.params.threshold / 64)
  · have hm : b ∈ markedBonds R (hotCoreSites R V) := by
      unfold markedBonds
      exact Finset.mem_filter.mpr ⟨hb, by rw [hbz]; exact hC z hz⟩
    have hst : b ∈ q.storedFieldBonds := by
      by_contra hn
      exact hf ((mem_emptyFamilySetting_free_iff b).mpr ⟨hm, hn⟩)
    obtain ⟨z1, z2⟩ := (mem_storedFieldBonds_iff_ends H b).mp hst
    obtain ⟨X, hX, hy, _⟩ := exists_component_of_mem_supportZone H z1
    have hy' := mem_component_of_supDist_le H hX hy (markedZone_subset H z2)
      ((_root_.YangMills.Construction.HullStates.supDist_parentBlock_unitStep_le H b.1 b.2).trans (by norm_num))
    have hbad : b ∉ q.storedBadBonds := by
      intro hbd
      apply hout
      refine parentBlock_mem_markedZone_of_near_badBond H hbd ?_
      have h1 := _root_.YangMills.Construction.HullStates.supDist_le_side_of_parentBlock_eq H hbz
      have h2 := hclose z hz
      have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle z₀ z b.1
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm z b.1] at h3
      nlinarith
    have hk := bondMark_restrict_ne_zero H hX hm hy hy' z1 z2 hbad
    have hlt' : ‖((chartCoord R.params V (q.restrict X).storedField b : imaginaryQuaternions) : ℍ[ℝ]) -
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ])‖ <
          R.ballRadius := by
      by_contra hn
      apply hk
      unfold bondMark cutoffFactor
      rw [if_neg hn]
    rw [chartCoord_restrict_storedField H hy hy', ← chartCoord_frameGaugeField_of_not_mem_free H hf] at hlt'
    exact hlt'.le
include H hGood in
theorem parentBlock_mem_markedZone_of_hot {x : TorusSite (n * R.params.side)} {μ ν : Fin 4} (hlt : μ < ν)
    (hs : R.params.threshold ≤ TorusFields.curvature (frameGaugeField V q) x μ ν)
    {z : TorusSite (n * R.params.side)} (hz : z ∈ plaquetteVertices x μ ν) :
    parentBlock R.params.side z ∈ q.markedZone := by
  by_contra hn
  have h1 := curvature_lt_of_vertex_outside H hGood hlt hz hn
  have h2 := H.wellPosed.admissible.σ_pos
  linarith
theorem self_mem_plaquetteVertices (x : TorusSite (n * R.params.side)) (μ ν : Fin 4) :
    x ∈ plaquetteVertices x μ ν := by
  simp [plaquetteVertices]
include H in
theorem frameGaugeField_eq_restrict {X : Finset (TorusSite n)} {c : TorusBond (n * R.params.side)}
    (h1 : parentBlock R.params.side c.1 ∈ X) (z1 : parentBlock R.params.side c.1 ∈ q.markedZone)
    (z2 : parentBlock R.params.side (c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈ q.markedZone) :
    frameGaugeField V q c.1 c.2 = (q.restrict X).storedField c.1 c.2 := by
  have hst : c ∈ q.storedFieldBonds := (mem_storedFieldBonds_iff_ends H c).mpr ⟨z1, z2⟩
  have hf : c ∉ (emptyFamilySetting V q).free := fun h => ((mem_emptyFamilySetting_free_iff c).mp h).2 hst
  rw [frameGaugeField_of_not_mem_free H hf]
  exact (fieldWithStoredLinks_restrict q _ _ h1).symm
include H in
theorem curvature_frameGaugeField_eq_restrict {X : Finset (TorusSite n)} {x : TorusSite (n * R.params.side)}
    {μ ν : Fin 4}
    (h : ∀ z ∈ plaquetteVertices x μ ν, parentBlock R.params.side z ∈ X ∧ parentBlock R.params.side z ∈ q.markedZone) :
    TorusFields.curvature (frameGaugeField V q) x μ ν = TorusFields.curvature (q.restrict X).storedField x μ ν := by
  have c0 := h x (by simp [plaquetteVertices])
  have c1 := h (x + TorusFields.unitStep _ μ) (by simp [plaquetteVertices])
  have c2 := h (x + TorusFields.unitStep _ ν) (by simp [plaquetteVertices])
  have c3 := h (x + TorusFields.unitStep _ μ + TorusFields.unitStep _ ν) (by simp [plaquetteVertices])
  have e : x + TorusFields.unitStep (n * R.params.side) ν + TorusFields.unitStep (n * R.params.side) μ =
      x + TorusFields.unitStep _ μ + TorusFields.unitStep _ ν := by abel
  refine curvature_congr ?_ ?_ ?_ ?_
  · exact frameGaugeField_eq_restrict H (c := (x, μ)) c0.1 c0.2 c1.2
  · exact frameGaugeField_eq_restrict H (c := (x + TorusFields.unitStep _ μ, ν)) c1.1 c1.2 c3.2
  · exact frameGaugeField_eq_restrict H (c := (x + TorusFields.unitStep _ ν, μ)) c2.1 c2.2
      (by show parentBlock _ (x + TorusFields.unitStep _ ν + TorusFields.unitStep _ μ) ∈ _; rw [e]; exact c3.2)
  · exact frameGaugeField_eq_restrict H (c := (x, ν)) c0.1 c0.2 c2.2
theorem frameHotLumpSites_eq_hotLumpsOn (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (S : Finset (TorusSite (n * ℓ.side)))
    (W : TorusField (n * ℓ.side)) : frameHotLumpSites ℓ S W = hotLumpsOn ℓ S W := by apply _root_.YangMills.Construction.CongruentAdmission.frameHotLumpSites_eq_hotLumpsOn <;> assumption
include H hGood in
theorem exists_component_of_mem_torusHotLumps {l : Finset (TorusSite (n * R.params.side))}
    (hl : l ∈ torusHotLumps R.params (frameGaugeField V q)) :
    ∃ X ∈ chainComponents R.nextRange q.1,
      l ∈ frameHotLumpSites R.params (sitesInBlocks R.params.side (q.restrict X).markedZone) (q.restrict X).storedField := by
  classical
  have hLn : R.params.side ∣ n * R.params.side := Dvd.intro_left _ rfl
  obtain ⟨x, μ, ν, hlt, hs, z, hz, rfl⟩ := (mem_torusHotLumps_iff R.params H.wellPosed.admissible hLn _ l).mp hl
  have h0 := parentBlock_mem_markedZone_of_hot H hGood hlt hs (self_mem_plaquetteVertices x μ ν)
  obtain ⟨X, hX, hy, _⟩ := exists_component_of_mem_supportZone H h0
  have hall : ∀ z' ∈ plaquetteVertices x μ ν,
      parentBlock R.params.side z' ∈ X ∧ parentBlock R.params.side z' ∈ q.markedZone := by
    intro z' hz'
    have h1 := parentBlock_mem_markedZone_of_hot H hGood hlt hs hz'
    refine ⟨mem_component_of_supDist_le H hX hy (markedZone_subset H h1) ?_, h1⟩
    have h2 := _root_.YangMills.Construction.TorusBlocks.supDist_parentBlock_le (side_odd H) x z'
    have h3 := _root_.YangMills.Construction.HullStates.supDist_le_two_of_mem_plaquetteVertices hz'
    omega
  refine ⟨X, hX, ?_⟩
  rw [frameHotLumpSites_eq_hotLumpsOn, mem_hotLumpsOn_iff R.params H.wellPosed.admissible hLn]
  refine ⟨x, μ, ν, hlt, ?_, fun z' hz' => ?_, z, hz, rfl⟩
  · rw [← curvature_frameGaugeField_eq_restrict H hall]
    exact hs
  · unfold sitesInBlocks
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_controlRegion_restrict_iff q).mpr (hall z' hz')⟩
end Rim
theorem toTorusSite_torusSiteInFrame_top {L : ℕ} [NeZero L] (y : TorusSite n) :
    toTorusSite n (torusSiteInFrame (stepBlockFrame L n) (stepBlockFrame L n).top y : (stepBlockFrame L n).Cell) = y :=
  toTorusSite_torusSiteInFrame (j := (stepBlockFrame L n).top) stepBlockFrame_period_one y
theorem baseChoice_of_labelAt_eq_some {q : CoarseState R n} {c : (stepBlockFrame R.params.side n).Cell}
    {s : BlockLabels R.labels.Ω R.params.side} (hs : q.markAt (toTorusSite n c) = some s) :
    q.baseChoice c = torusSiteInFrame (stepBlockFrame R.params.side n) 0 (blockSite (toTorusSite n c) s.basePoint) := by
  unfold CoarseState.baseChoice
  rw [hs]
theorem baseChoice_of_labelAt_eq_none {q : CoarseState R n} {c : (stepBlockFrame R.params.side n).Cell}
    (hs : q.markAt (toTorusSite n c) = none) : q.baseChoice c = cellCentre (stepBlockFrame R.params.side n).depth c := by
  unfold CoarseState.baseChoice
  rw [hs]
section Case
variable (H : HullStateHypotheses δ lam σA cg N V q)
  (hGood : StepFrames.coldPlaquette_of_small_frameDeviation)
include H
theorem supDist_parentBlock_le_nextRange {u v : TorusSite (n * R.params.side)} (h : _root_.YangMills.Construction.TorusFields.supDist u v ≤ R.range) :
    _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side u) (parentBlock R.params.side v) ≤ R.nextRange := by
  have h1 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one R.params.side u v
  have hL := H.wellPosed.admissible.L_ge
  have h2 : _root_.YangMills.Construction.TorusFields.supDist u v / R.params.side ≤ _root_.YangMills.Construction.TorusFields.supDist u v / 16 := Nat.div_le_div_left (by omega) (by norm_num)
  have h3 := H.wellPosed.range_le
  have h4 := H.wellPosed.nextRange_ge
  omega
theorem chainConnected_restrict_of_labelSet {X : Finset (TorusSite n)} (hX : X ∈ chainComponents R.nextRange q.1)
    {y z : TorusSite (n * R.params.side)} (hy : parentBlock R.params.side y ∈ X) (hyl : y ∈ q.labelSet)
    (hj : ChainConnected R.range q.labelSet y z) :
    ChainConnected R.range (q.restrict X).labelSet y z ∧ parentBlock R.params.side z ∈ X := by
  classical
  induction hj with
  | refl => exact ⟨Relation.ReflTransGen.refl, hy⟩
  | @tail u v _ hs ih =>
    obtain ⟨hu, hv, hd⟩ := hs
    have hvz := parentBlock_mem_markedZone_of_mem_labelSet q hv
    have hvX : parentBlock R.params.side v ∈ X :=
      mem_of_chainConnected_of_mem_chainComponents hX ih.2 (markedZone_subset H hvz)
        (chainConnected_of_supDist_le (subset_of_mem_chainComponents hX ih.2) (markedZone_subset H hvz)
          (_root_.YangMills.Construction.HullStates.supDist_parentBlock_le_nextRange H hd))
    exact ⟨ih.1.tail ⟨(mem_labelSet_restrict_iff q).mpr ⟨ih.2, hu⟩, (mem_labelSet_restrict_iff q).mpr ⟨hvX, hv⟩, hd⟩, hvX⟩
theorem chainConnected_mono {A B : Finset (TorusSite (n * R.params.side))} (hs : A ⊆ B) {r : ℕ}
    {y z : TorusSite (n * R.params.side)} (hj : ChainConnected r A y z) : ChainConnected r B y z := by
  induction hj with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs' ih => exact ih.tail ⟨hs hs'.1, hs hs'.2.1, hs'.2.2⟩
theorem mem_chainComponents_restrict {X : Finset (TorusSite n)} (hX : X ∈ chainComponents R.nextRange q.1)
    {Xc : Finset (TorusSite (n * R.params.side))} (hXc : Xc ∈ chainComponents R.range q.labelSet)
    {y : TorusSite (n * R.params.side)} (hyc : y ∈ Xc) (hy : parentBlock R.params.side y ∈ X) :
    Xc ∈ chainComponents R.range (q.restrict X).labelSet := by
  classical
  have hyl := subset_of_mem_chainComponents hXc hyc
  have hyX : y ∈ (q.restrict X).labelSet := (mem_labelSet_restrict_iff q).mpr ⟨hy, hyl⟩
  have hsub : (q.restrict X).labelSet ⊆ q.labelSet := fun z hz => ((mem_labelSet_restrict_iff q).mp hz).2
  refine mem_chainComponents.mpr ⟨y, hyX, ?_⟩
  rw [eq_filter_of_mem_chainComponents hXc hyc]
  ext z
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hz, hj⟩
    have := chainConnected_restrict_of_labelSet H hX hy hyl hj
    exact ⟨(mem_labelSet_restrict_iff q).mpr ⟨this.2, hz⟩, this.1⟩
  · rintro ⟨hz, hj⟩
    exact ⟨hsub hz, chainConnected_mono H hsub hj⟩
theorem exists_component_of_mem_labelSet {z : TorusSite (n * R.params.side)} (hz : z ∈ q.labelSet) :
    ∃ X ∈ chainComponents R.nextRange q.1, parentBlock R.params.side z ∈ X := by
  obtain ⟨X, hX, hy, _⟩ := exists_component_of_mem_supportZone H (parentBlock_mem_markedZone_of_mem_labelSet q hz)
  exact ⟨X, hX, hy⟩
include hGood
theorem thickening_torusHotSites_subset_labelSet :
    thickening (2 * R.range) (torusHotSites R.params (frameGaugeField V q)) ⊆ q.labelSet := by
  classical
  intro z hz
  obtain ⟨u, hu, hd⟩ := (mem_thickening _ _ _).mp hz
  obtain ⟨l, hl, hul⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨X, hX, hcut⟩ := exists_component_of_mem_torusHotLumps H hGood hl
  have h1 := (restrict_isAdmissibleState H hX).hotHull_subset
    ((mem_thickening _ _ _).mpr ⟨u, Finset.mem_biUnion.mpr ⟨l, hcut, hul⟩, hd⟩)
  exact ((mem_labelSet_restrict_iff q).mp h1).2
theorem isHullState_frameGaugeField : IsHullState R.params R.range (frameGaugeField V q) q.labelSet := by
  classical
  refine ⟨thickening_torusHotSites_subset_labelSet H hGood, fun Xc hXc => ?_⟩
  obtain ⟨y, hy, hXe⟩ := mem_chainComponents.mp hXc
  have hyc : y ∈ Xc := by
    rw [hXe]
    exact Finset.mem_filter.mpr ⟨hy, Relation.ReflTransGen.refl⟩
  obtain ⟨X, hX, hyX⟩ := exists_component_of_mem_labelSet H hy
  obtain ⟨l, hl, hne⟩ := (restrict_isAdmissibleState H hX).component_meets Xc
    (mem_chainComponents_restrict H hX hXc hyc hyX)
  have hLn : R.params.side ∣ n * R.params.side := Dvd.intro_left _ rfl
  rw [frameHotLumpSites_eq_hotLumpsOn, mem_hotLumpsOn_iff R.params H.wellPosed.admissible hLn] at hl
  obtain ⟨x, μ, ν, hlt, hs, hS, z, hz, rfl⟩ := hl
  have hall : ∀ z' ∈ plaquetteVertices x μ ν,
      parentBlock R.params.side z' ∈ X ∧ parentBlock R.params.side z' ∈ q.markedZone := by
    intro z' hz'
    have h1 := hS z' hz'
    unfold sitesInBlocks at h1
    exact (mem_controlRegion_restrict_iff q).mp (Finset.mem_filter.mp h1).2
  refine ⟨torusLumpOf R.params z,
    (mem_torusHotLumps_iff R.params H.wellPosed.admissible hLn _ _).mpr ⟨x, μ, ν, hlt, ?_, z, hz, rfl⟩, hne⟩
  rw [curvature_frameGaugeField_eq_restrict H hall]
  exact hs
omit hGood in
theorem storedBadBonds_subset_markedBonds : q.storedBadBonds ⊆ markedBonds R (hotCoreSites R V) := by
  classical
  intro c hc
  obtain ⟨s, hs, _⟩ := (mem_storedBadBonds_iff q).mp hc
  have hz : parentBlock R.params.side c.1 ∈ q.markedZone := (mem_controlRegion_iff q).mpr (by rw [hs]; rfl)
  obtain ⟨X, hX, hy, _⟩ := exists_component_of_mem_supportZone H hz
  have h1 := (restrict_isAdmissibleState H hX).badBonds_subset ((mem_storedBadBonds_restrict_iff q).mpr ⟨hy, hc⟩)
  unfold markedBonds at h1 ⊢
  obtain ⟨hb, hn⟩ := Finset.mem_filter.mp h1
  exact Finset.mem_filter.mpr ⟨hb, fun h => hn ((mem_hotNeighbourhoodOn_iff H hX hy).mpr h)⟩
omit hGood in
theorem baseOffset_baseChoice {y : TorusSite n} {s : BlockLabels R.labels.Ω R.params.side}
    (hs : q.markAt y = some s) : baseOffset R q.baseChoice y = s.basePoint := by
  have hb := baseChoice_of_labelAt_eq_some (q := q)
    (c := torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top y) (s := s)
    (by rw [toTorusSite_torusSiteInFrame_top]; exact hs)
  rw [toTorusSite_torusSiteInFrame_top] at hb
  unfold baseOffset
  have hb' : q.baseChoice (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) =
      torusSiteInFrame (stepBlockFrame R.params.side n) 0 (blockSite y s.basePoint) := hb
  rw [hb', toTorusSite_torusSiteInFrame stepBlockFrame_period_zero, siteOffset_blockSite]
theorem isExtension_frameGaugeField :
    q.IsExtension (hotCoreSites R V) (frameGaugeField V q) q.labelSet q.labeling q.storedBadBonds q.baseChoice := by
  classical
  refine ⟨fun c hc => ?_, fun z => ?_, fun z _ _ => rfl, fun c => ?_, fun y s hs => baseOffset_baseChoice H hs,
    fun c hc hn => absurd ?_ hn, fun z hz hn => absurd (parentBlock_mem_markedZone_of_mem_labelSet q hz) hn⟩
  · have hf : c ∉ (emptyFamilySetting V q).free := fun h => ((mem_emptyFamilySetting_free_iff c).mp h).2 hc
    exact frameGaugeField_of_not_mem_free H hf
  · exact ⟨fun h => ⟨h, parentBlock_mem_markedZone_of_mem_labelSet q h⟩, fun h => h.1⟩
  · constructor
    · intro h
      obtain ⟨s, hs, _⟩ := (mem_storedBadBonds_iff q).mp h
      exact ⟨h, (mem_controlRegion_iff q).mpr (by rw [hs]; rfl)⟩
    · exact fun h => h.1
  · obtain ⟨s, hs, _⟩ := (mem_storedBadBonds_iff q).mp hc
    exact (mem_controlRegion_iff q).mpr (by rw [hs]; rfl)
end Case
section Rest
variable (H : HullStateHypotheses δ lam σA cg N V q)
  (hGood : StepFrames.coldPlaquette_of_small_frameDeviation)
theorem chainConnected_of_subset {A B : Finset (TorusSite (n * R.params.side))} (hs : A ⊆ B) {r : ℕ}
    {y z : TorusSite (n * R.params.side)} (hj : ChainConnected r A y z) : ChainConnected r B y z := by
  induction hj with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs' ih => exact ih.tail ⟨hs hs'.1, hs hs'.2.1, hs'.2.2⟩
theorem attachedSites_mono {r : ℕ} {bad' bad : Finset (TorusBond (n * R.params.side))}
    {Y' Y : Finset (TorusSite (n * R.params.side))} {C' C : Finset (TorusSite n)}
    (h1 : bad' ⊆ bad) (h2 : Y' ⊆ Y) (h3 : C' ⊆ C) :
    attachedSites R.params.side r bad' Y' C' ⊆ attachedSites R.params.side r bad Y C := by
  classical
  have hB : sitesInBlocks R.params.side C' ⊆ sitesInBlocks R.params.side C := fun z hz => by
    unfold sitesInBlocks at hz ⊢
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3 (Finset.mem_filter.mp hz).2⟩
  have hA : bad'.image Prod.fst ∪ Y' ∪ sitesInBlocks R.params.side C' ⊆
      bad.image Prod.fst ∪ Y ∪ sitesInBlocks R.params.side C :=
    Finset.union_subset_union (Finset.union_subset_union (Finset.image_subset_image h1) h2) hB
  intro z hz
  unfold attachedSites clusterComponents at hz ⊢
  simp only [Finset.mem_biUnion, Finset.mem_filter, id] at hz ⊢
  obtain ⟨K, ⟨hK, u, hu⟩, hzK⟩ := hz
  obtain ⟨huK, huB⟩ := Finset.mem_inter.mp hu
  have hj := chainConnected_of_mem_chainComponents hK hzK huK
  have hzA := hA (subset_of_mem_chainComponents hK hzK)
  have huA := hA (subset_of_mem_chainComponents hK huK)
  obtain ⟨K2, hK2, hz2⟩ := exists_mem_chainComponents (r := 10 * r) hzA
  exact ⟨K2, ⟨hK2, u, Finset.mem_inter.mpr
    ⟨mem_of_chainConnected_of_mem_chainComponents hK2 hz2 huA (chainConnected_of_subset hA hj), hB huB⟩⟩, hz2⟩
include H
theorem hotNeighbourhoodOn_subset {X : Finset (TorusSite n)} (hX : X ∈ chainComponents R.nextRange q.1) :
    hotNeighbourhoodOn R X V ⊆ hotCoreSites R V := by
  intro z hz
  have h1 := ((mem_controlRegion_restrict_iff q).mp ((restrict_isAdmissibleState H hX).subset_dataZone hz)).1
  exact (mem_hotNeighbourhoodOn_iff H hX h1).mp hz
theorem subset_attachedSites : (open Classical in q.storedBadBonds.image Prod.fst ∪ q.labelSet) ⊆
    attachedSites R.params.side R.range q.storedBadBonds q.labelSet (hotCoreSites R V) := by
  classical
  have key : ∀ {X : Finset (TorusSite n)}, X ∈ chainComponents R.nextRange q.1 → ∀ {z : TorusSite (n * R.params.side)},
      z ∈ (q.restrict X).storedBadBonds.image Prod.fst ∪ (q.restrict X).labelSet ∪
        sitesInBlocks R.params.side (hotNeighbourhoodOn R X V) →
      z ∈ attachedSites R.params.side R.range q.storedBadBonds q.labelSet (hotCoreSites R V) := by
    intro X hX z hz
    rw [← (restrict_isAdmissibleState H hX).attached_eq] at hz
    exact attachedSites_mono (fun c hc => ((mem_storedBadBonds_restrict_iff q).mp hc).2)
      (fun c hc => ((mem_labelSet_restrict_iff q).mp hc).2) (hotNeighbourhoodOn_subset H hX) hz
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨s, hs, _⟩ := (mem_storedBadBonds_iff q).mp hc
    have hzn : parentBlock R.params.side c.1 ∈ q.markedZone := (mem_controlRegion_iff q).mpr (by rw [hs]; rfl)
    obtain ⟨X, hX, hy, _⟩ := exists_component_of_mem_supportZone H hzn
    exact key hX (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨c, (mem_storedBadBonds_restrict_iff q).mpr ⟨hy, hc⟩, rfl⟩)))
  · obtain ⟨X, hX, hy⟩ := exists_component_of_mem_labelSet H hz
    exact key hX (Finset.mem_union_left _ (Finset.mem_union_right _ ((mem_labelSet_restrict_iff q).mpr ⟨hy, hz⟩)))
omit H in
theorem labelAt_eq_labeling (p : CoarseState R n) (z : p.labelSet) : p.labelAt z.1 = Sum.inr (p.labeling z) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.labelAt_eq_inr_labeling <;> assumption
theorem clusterFactor_frameGaugeField_ne_zero {Xc : Finset (TorusSite (n * R.params.side))}
    (hXc : Xc ∈ chainComponents R.range q.labelSet) :
    R.clusterFactor (n * R.params.side) (frameGaugeField V q) q.labelSet q.labeling Xc ≠ 0 := by
  classical
  obtain ⟨y, hy, hXe⟩ := mem_chainComponents.mp hXc
  have hyc : y ∈ Xc := by
    rw [hXe]
    exact Finset.mem_filter.mpr ⟨hy, Relation.ReflTransGen.refl⟩
  obtain ⟨X, hX, hyX⟩ := exists_component_of_mem_labelSet H hy
  have hon := mem_chainComponents_restrict H hX hXc hyc hyX
  have hphi := H.factor_ne_zero X hX
  unfold coarseFactor at hphi
  have hlevel : clusterFactorProduct q X ≠ 0 := by
    intro h
    apply hphi
    rw [h]
    ring
  unfold clusterFactorProduct at hlevel
  have hf := (Finset.prod_ne_zero_iff.mp hlevel) Xc hon
  have hLpos := one_le_side H
  have hsideL : IsBlockTorusSide R.params (n * R.params.side) := by
    refine ⟨Dvd.intro_left _ rfl, ?_⟩
    have h1 := H.isBlockSide.2
    nlinarith
  have hin : ∀ z ∈ Xc, parentBlock R.params.side z ∈ X ∧ z ∈ q.labelSet := fun z hz =>
    (mem_labelSet_restrict_iff q).mp (subset_of_mem_chainComponents hon hz)
  have hrc := H.wellPosed.hasExpansions.2.reads_class (n * R.params.side) hsideL (q.restrict X).storedField
    (frameGaugeField V q) (q.restrict X).labelSet q.labelSet (q.restrict X).labeling q.labeling Xc
    (subset_of_mem_chainComponents hon) (subset_of_mem_chainComponents hXc)
    (fun b h1 h2 => (frameGaugeField_eq_restrict H (hin _ h1).1
      (parentBlock_mem_markedZone_of_mem_labelSet q (hin _ h1).2)
      (parentBlock_mem_markedZone_of_mem_labelSet q (hin _ h2).2)).symm)
    (fun z hz hz' hzX => by
      have e1 := labelAt_eq_labeling (q.restrict X) ⟨z, hz⟩
      have e2 := labelAt_eq_labeling q ⟨z, hz'⟩
      have e3 : (q.restrict X).labelAt z = q.labelAt z := labelAt_restrict_of_mem q (hin z hzX).1
      simp only at e1 e2
      rw [e3, e2] at e1
      exact (Sum.inr.inj e1).symm)
  rw [← hrc]
  exact hf
theorem bondMark_frameGaugeField_ne_zero {c : TorusBond (n * R.params.side)}
    (hm : c ∈ markedBonds R (hotCoreSites R V)) (hst : c ∈ q.storedFieldBonds) :
    (open Classical in if c ∈ q.storedBadBonds then 1 - bondMark R V (frameGaugeField V q) c
      else bondMark R V (frameGaugeField V q) c) ≠ 0 := by
  classical
  obtain ⟨z1, z2⟩ := (mem_storedFieldBonds_iff_ends H c).mp hst
  obtain ⟨X, hX, hy, _⟩ := exists_component_of_mem_supportZone H z1
  have hy' := mem_component_of_supDist_le H hX hy (markedZone_subset H z2)
    ((_root_.YangMills.Construction.HullStates.supDist_parentBlock_unitStep_le H c.1 c.2).trans (by norm_num))
  have hphi := H.factor_ne_zero X hX
  unfold coarseFactor at hphi
  have hmark : markFactorProduct V q X ≠ 0 := by
    intro h
    apply hphi
    rw [h]
    ring
  unfold markFactorProduct at hmark
  have hb : c ∈ markedBonds R (hotNeighbourhoodOn R X V) ∩ bondsOverBlocks R.params.side (q.restrict X).markedZone := by
    refine Finset.mem_inter.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (mem_controlRegion_restrict_iff q).mpr ⟨hy, z1⟩, (mem_controlRegion_restrict_iff q).mpr ⟨hy', z2⟩⟩⟩
    unfold markedBonds at hm ⊢
    obtain ⟨hc, hn⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨hc, fun h => hn ((mem_hotNeighbourhoodOn_iff H hX hy).mp h)⟩
  have hf := (Finset.prod_ne_zero_iff.mp hmark) c hb
  have hfree : c ∉ (emptyFamilySetting V q).free := fun h => ((mem_emptyFamilySetting_free_iff c).mp h).2 hst
  have hsame : bondMark R V (frameGaugeField V q) c = bondMark R V (q.restrict X).storedField c := by
    unfold bondMark
    rw [chartCoord_frameGaugeField_of_not_mem_free H hfree, chartCoord_restrict_storedField H hy hy']
  rw [hsame]
  by_cases hbad : c ∈ q.storedBadBonds
  · rw [if_pos hbad]
    rwa [if_pos ((mem_storedBadBonds_restrict_iff q).mpr ⟨hy, hbad⟩)] at hf
  · rw [if_neg hbad]
    rwa [if_neg (fun h => hbad ((mem_storedBadBonds_restrict_iff q).mp h).2)] at hf
end Rest
section Bases
variable {L : ℕ} [NeZero L]
theorem torusSiteInFrame_top_add_toSite (x : TorusSite n) (h : Fin 4 → ℤ) :
    torusSiteInFrame (stepBlockFrame L n) 1 x + siteOfCoords 1 h =
      torusSiteInFrame (stepBlockFrame L n) 1 (x + siteOfInt h) := by apply _root_.YangMills.Construction.InBoxTransfer.torusSiteInFrame_one_add_siteOfInt <;> assumption
theorem plaquetteDefect_readAtLevel (W : TorusField (n * L)) (x : TorusSite (n * L)) (μ ν : Fin 4) :
    plaquetteDefect (readAtLevel (stepBlockFrame L n) 0 W) (torusSiteInFrame (stepBlockFrame L n) 0 x, μ, ν) =
      TorusFields.curvature W x μ ν := by apply _root_.YangMills.Construction.InBoxTransfer.plaquetteDefect_readAtLevel <;> assumption
theorem mem_plaquetteCorners_torusSiteInFrame_iff (x : TorusSite (n * L)) (μ ν : Fin 4)
    (c : (stepBlockFrame L n).Site 0) :
    c ∈ plaquetteCorners ((torusSiteInFrame (stepBlockFrame L n) 0 x, μ, ν) :
      (stepBlockFrame L n).Site 0 × Fin 4 × Fin 4) ↔
      ∃ z ∈ plaquetteVertices x μ ν, torusSiteInFrame (stepBlockFrame L n) 0 z = c := by
  simp only [plaquetteVertices, plaquetteCorners, List.mem_cons, List.not_mem_nil, or_false, Finset.mem_insert,
    Finset.mem_singleton, exists_eq_or_imp, exists_eq_left, BlockTrees.torusSiteInFrame_add, torusSiteInFrame_unitStep]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inr (Or.inr h.symm))
  · rintro (h | h | h | h)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inr (Or.inr h.symm))
theorem mem_levelSites (x : (stepBlockFrame L n).Site 0) : x ∈ levelSites (stepBlockFrame L n) 0 := by
  unfold levelSites boxSites
  refine Finset.mem_image.mpr ⟨siteCoords x, ?_, ?_⟩
  · refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_
    have hne : NeZero ((stepBlockFrame L n).period 0 i) := ⟨by
      rw [stepBlockFrame_period_zero]
      exact mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
    have h1 : siteCoords x i = (((x i).val : ℕ) : ℤ) := ZMod.cast_eq_val _
    have h2 := ZMod.val_lt (x i)
    simp only [Pi.zero_apply]
    rw [h1]
    omega
  · funext k
    have hne : NeZero ((stepBlockFrame L n).period 0 k) := ⟨by
      rw [stepBlockFrame_period_zero]
      exact mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
    simp [siteOfCoords, siteCoords]
end Bases
section Frames
theorem exists_plaquette_of_mem_hotLumps {Q : Finset ((stepBlockFrame R.params.side n).Site 0)}
    {W : TorusField (n * R.params.side)} {l : Finset ((stepBlockFrame R.params.side n).Site 0)}
    (hl : l ∈ hotLumps R.params.grid R.params.threshold Q (readAtLevel (stepBlockFrame R.params.side n) 0 W)) :
    ∃ (x : TorusSite (n * R.params.side)) (μ ν : Fin 4), μ < ν ∧ R.params.threshold ≤ TorusFields.curvature W x μ ν ∧
      (∀ z ∈ plaquetteVertices x μ ν, torusSiteInFrame (stepBlockFrame R.params.side n) 0 z ∈ Q) ∧
      ∃ z ∈ plaquetteVertices x μ ν, l = lumpOf R.params.grid (torusSiteInFrame (stepBlockFrame R.params.side n) 0 z) := by
  classical
  unfold hotLumps at hl
  obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨hp1, hs⟩ := Finset.mem_filter.mp hp
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hlp
  obtain ⟨x', μ, ν⟩ := p
  obtain ⟨x, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 0 stepBlockFrame_period_zero x'
  have hcut := Finset.mem_filter.mp hp1
  refine ⟨x, μ, ν, hcut.2.1, ?_, ?_, ?_⟩
  · rw [← plaquetteDefect_readAtLevel]
    exact hs
  · intro z hz
    exact hcut.2.2 ((mem_plaquetteCorners_torusSiteInFrame_iff x μ ν _).mpr ⟨z, hz, rfl⟩)
  · obtain ⟨z, hz, rfl⟩ := (mem_plaquetteCorners_torusSiteInFrame_iff x μ ν c).mp hc
    exact ⟨z, hz, rfl⟩
theorem lumpOf_mem_hotLumps {Q : Finset ((stepBlockFrame R.params.side n).Site 0)}
    {W : TorusField (n * R.params.side)} {x : TorusSite (n * R.params.side)} {μ ν : Fin 4} (hlt : μ < ν)
    (hs : R.params.threshold ≤ TorusFields.curvature W x μ ν)
    (hin : ∀ z ∈ plaquetteVertices x μ ν, torusSiteInFrame (stepBlockFrame R.params.side n) 0 z ∈ Q)
    {z : TorusSite (n * R.params.side)} (hz : z ∈ plaquetteVertices x μ ν) :
    lumpOf R.params.grid (torusSiteInFrame (stepBlockFrame R.params.side n) 0 z) ∈
      hotLumps R.params.grid R.params.threshold Q (readAtLevel (stepBlockFrame R.params.side n) 0 W) := by
  classical
  unfold hotLumps
  refine Finset.mem_biUnion.mpr ⟨(torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, μ, ν),
    Finset.mem_filter.mpr ⟨?_, ?_⟩,
    Finset.mem_image.mpr ⟨_, (mem_plaquetteCorners_torusSiteInFrame_iff x μ ν _).mpr ⟨z, hz, rfl⟩, rfl⟩⟩
  · unfold cutPlaquettes
    refine Finset.mem_filter.mpr ⟨?_, hlt, fun c hc => ?_⟩
    · simp only [Finset.mem_product, Finset.mem_univ, and_true]
      exact hin x (self_mem_plaquetteVertices x μ ν)
    · obtain ⟨z', hz', rfl⟩ := (mem_plaquetteCorners_torusSiteInFrame_iff x μ ν c).mp hc
      exact hin z' hz'
  · rw [plaquetteDefect_readAtLevel]
    exact hs
theorem nearbyLumps_congr {F : BlockFrame} {h h' : Finset (Finset (F.Site F.depth))} {y : F.Cell}
    (hh : ∀ l, l ⊆ cutBelow F.depth (cellBall y 2) → (l ∈ h ↔ l ∈ h')) :
    nearbyLumps h y = nearbyLumps h' y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.nearbyLumps_ext <;> assumption
theorem baseSitesAt_congr {F : BlockFrame} {J₀ : ℕ} {h h' : Finset (Finset (F.Site F.depth))} {y : F.Cell}
    (hl : nearbyLumps h y = nearbyLumps h' y) : baseSitesAt J₀ h y = baseSitesAt J₀ h' y := by apply _root_.YangMills.Construction.InBoxTransfer.baseSitesAt_congr <;> assumption
theorem exists_offset_of_lumpOf_subset {F : BlockFrame} (hF : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {L : ℕ}
    (hpos : 0 < L) (hodd : Odd L) (g : LumpGrid L) {x : F.Site F.depth} {y : F.Cell} {r : ℕ}
    (h : lumpOf g x ⊆ cutBelow F.depth (cellBall y r)) :
    ∃ c : Fin 4 → ℤ, (∀ i, |c i| ≤ r) ∧ enclosingCell x = y + siteOfCoords F.top c := by
  have h1 := (mem_cutBelow_iff hF hs).mp (h (mem_lumpOf hpos hodd g x))
  exact mem_cellBall_iff.mp h1
theorem supDist_parentBlock_le_two_of_enclosingCell (hodd : Odd R.params.side) {z : TorusSite (n * R.params.side)}
    {y₀ : TorusSite n} {c : Fin 4 → ℤ} (hc : ∀ i, |c i| ≤ 2)
    (he : enclosingCell (torusSiteInFrame (stepBlockFrame R.params.side n) 0 z) =
      torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀ + siteOfCoords 1 c) :
    _root_.YangMills.Construction.TorusFields.supDist y₀ (parentBlock R.params.side z) ≤ 2 := by
  have h0 := (enclosingCell_torusSiteInFrame z).symm.trans he
  have h1 : torusSiteInFrame (stepBlockFrame R.params.side n) 1 (parentBlock R.params.side z) =
      torusSiteInFrame (stepBlockFrame R.params.side n) 1 (y₀ + siteOfInt c) :=
    h0.trans (torusSiteInFrame_top_add_toSite y₀ c)
  have he2 := torusSiteInFrame_injective (stepBlockFrame R.params.side n) 1 stepBlockFrame_period_one h1
  rw [he2]
  refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ fun i => ?_
  have := hc i
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this
end Frames
section Final
variable (H : HullStateHypotheses δ lam σA cg N V q)
  (hGood : StepFrames.coldPlaquette_of_small_frameDeviation)
include H hGood
theorem nearbyLumps_stepHotLumps_eq {X : Finset (TorusSite n)} (hX : X ∈ chainComponents R.nextRange q.1)
    {y : TorusSite n} (hy : y ∈ X) :
    nearbyLumps (stepHotLumps R.params (frameGaugeField V q)) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) =
      nearbyLumps (frameHotLumps R.params (sitesInBlocks R.params.side (q.restrict X).markedZone) (q.restrict X).storedField)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) := by
  classical
  apply nearbyLumps_congr
  intro l hl
  have hpos : 0 < R.params.side := one_le_side H
  have hodd := side_odd H
  have hF : ∀ i, 0 < (stepBlockFrame R.params.side n).extent i := fun _ => Nat.pos_of_ne_zero (NeZero.ne n)
  constructor
  · intro hm
    obtain ⟨x, μ, ν, hlt, hs, _, z, hz, rfl⟩ := exists_plaquette_of_mem_hotLumps hm
    obtain ⟨cc, hcc, hcell⟩ := exists_offset_of_lumpOf_subset (F := stepBlockFrame R.params.side n) hodd hF hpos hodd
      R.params.grid hl
    have hd := _root_.YangMills.Construction.HullStates.supDist_parentBlock_le_two_of_enclosingCell hodd hcc hcell
    have hzz := parentBlock_mem_markedZone_of_hot H hGood hlt hs hz
    have hzX := mem_component_of_supDist_le H hX hy (markedZone_subset H hzz) (hd.trans (by norm_num))
    have hall : ∀ z' ∈ plaquetteVertices x μ ν,
        parentBlock R.params.side z' ∈ X ∧ parentBlock R.params.side z' ∈ q.markedZone := by
      intro z' hz'
      have h1 := parentBlock_mem_markedZone_of_hot H hGood hlt hs hz'
      refine ⟨mem_component_of_supDist_le H hX hzX (markedZone_subset H h1) ?_, h1⟩
      have h2 := _root_.YangMills.Construction.TorusBlocks.supDist_parentBlock_le hodd z z'
      have h3 := _root_.YangMills.Construction.HullStates.supDist_le_two_of_mem_plaquetteVertices hz
      have h4 := _root_.YangMills.Construction.HullStates.supDist_le_two_of_mem_plaquetteVertices hz'
      have h5 := _root_.YangMills.Construction.TorusFields.supDist_triangle z x z'
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm z x] at h5
      omega
    refine lumpOf_mem_hotLumps hlt ?_ (fun z' hz' => ?_) hz
    · rw [← curvature_frameGaugeField_eq_restrict H hall]
      exact hs
    · refine Finset.mem_image.mpr ⟨z', ?_, rfl⟩
      unfold sitesInBlocks
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_controlRegion_restrict_iff q).mpr (hall z' hz')⟩
  · intro hm
    obtain ⟨x, μ, ν, hlt, hs, hin, z, hz, rfl⟩ := exists_plaquette_of_mem_hotLumps hm
    have hall : ∀ z' ∈ plaquetteVertices x μ ν,
        parentBlock R.params.side z' ∈ X ∧ parentBlock R.params.side z' ∈ q.markedZone := by
      intro z' hz'
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp (hin z' hz')
      have e := torusSiteInFrame_injective (stepBlockFrame R.params.side n) 0 stepBlockFrame_period_zero he
      subst e
      unfold sitesInBlocks at hw
      exact (mem_controlRegion_restrict_iff q).mp (Finset.mem_filter.mp hw).2
    refine lumpOf_mem_hotLumps hlt ?_ (fun z' _ => mem_levelSites _) hz
    rw [curvature_frameGaugeField_eq_restrict H hall]
    exact hs
theorem nearbyLumps_stepHotLumps_eq_empty {y : TorusSite n} (hy : q.markAt y = none) :
    nearbyLumps (stepHotLumps R.params (frameGaugeField V q)) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun l hl => ?_
  obtain ⟨hm, hsub⟩ := Finset.mem_filter.mp hl
  have hpos : 0 < R.params.side := one_le_side H
  have hodd := side_odd H
  have hF : ∀ i, 0 < (stepBlockFrame R.params.side n).extent i := fun _ => Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨x, μ, ν, hlt, hs, _, z, hz, rfl⟩ := exists_plaquette_of_mem_hotLumps hm
  obtain ⟨cc, hcc, hcell⟩ := exists_offset_of_lumpOf_subset (F := stepBlockFrame R.params.side n) hodd hF hpos hodd
    R.params.grid hsub
  have hd := _root_.YangMills.Construction.HullStates.supDist_parentBlock_le_two_of_enclosingCell hodd hcc hcell
  have hLn : R.params.side ∣ n * R.params.side := Dvd.intro_left _ rfl
  have hhot : torusLumpOf R.params z ∈ torusHotLumps R.params (frameGaugeField V q) :=
    (mem_torusHotLumps_iff R.params H.wellPosed.admissible hLn _ _).mpr ⟨x, μ, ν, hlt, hs, z, hz, rfl⟩
  have hsite : z ∈ torusHotSites R.params (frameGaugeField V q) :=
    Finset.mem_biUnion.mpr ⟨_, hhot, mem_torusLumpOf_self z⟩
  have hlab : z ∈ q.labelSet := thickening_torusHotSites_subset_labelSet H hGood
    ((mem_thickening _ _ _).mpr ⟨z, hsite, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; exact Nat.zero_le _⟩)
  have hpt : parentBlock R.params.side (blockSite y (fun _ => ⟨0, hpos⟩)) = y := parentBlock_blockSite _ _
  have hnear : parentBlock R.params.side (blockSite (L := R.params.side) y (fun _ => ⟨0, hpos⟩)) ∈ q.markedZone := by
    refine parentBlock_mem_markedZone_of_near_label H hlab ?_
    have h1 := _root_.YangMills.Construction.TorusBlocks.supDist_le_mul_supDist_parentBlock_add_one hodd (blockSite (L := R.params.side) y (fun _ => ⟨0, hpos⟩)) z
    rw [hpt] at h1
    have h2 := side_mul_le_range H
    have h3 : R.params.side * (_root_.YangMills.Construction.TorusFields.supDist y (parentBlock R.params.side z) + 1) ≤ R.params.side * 3 :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith
  rw [hpt] at hnear
  have := (mem_controlRegion_iff q).mp hnear
  rw [hy] at this
  exact absurd this (by simp)
theorem baseLaw_frameGaugeField_ne_zero (hB : ClusterExpansionOfAStep.BaseLawIsProduct) :
    baseLaw (frameGaugeField V q) q.baseChoice ≠ 0 := by
  classical
  rw [hB R n (frameGaugeField V q) q.baseChoice]
  refine Finset.prod_ne_zero_iff.mpr fun c _ => ?_
  obtain ⟨y, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 1 stepBlockFrame_period_one c
  have ec : toTorusSite n (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top y :
      (stepBlockFrame R.params.side n).Cell) = y :=
    toTorusSite_torusSiteInFrame_top y
  cases hs : q.markAt y with
  | none =>
    have hb : q.baseChoice (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) =
        cellCentre (stepBlockFrame R.params.side n).depth (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) :=
      baseChoice_of_labelAt_eq_none (q := q)
        (c := torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top y)
        (by rw [ec]; exact hs)
    rw [hb]
    have hm : cellCentre (stepBlockFrame R.params.side n).depth (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) ∈
        baseSitesAt R.params.baseDepth (stepHotLumps R.params (frameGaugeField V q))
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) := by
      unfold baseSitesAt
      rw [if_pos (Or.inl (nearbyLumps_stepHotLumps_eq_empty H hGood hs))]
      exact Finset.mem_singleton_self _
    unfold blockBaseWeight
    split_ifs with hx
    · have h1 : 0 < (baseSitesAt R.params.baseDepth (stepHotLumps R.params (frameGaugeField V q))
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)).card := Finset.card_pos.mpr ⟨_, hm⟩
      have h2 : (0 : ℝ) < ((baseSitesAt R.params.baseDepth (stepHotLumps R.params (frameGaugeField V q))
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)).card : ℝ) := by exact_mod_cast h1
      exact (div_pos one_pos h2).ne'
    · exact absurd hm hx
  | some s =>
    have hz : y ∈ q.markedZone := (mem_controlRegion_iff q).mpr (by rw [hs]; rfl)
    obtain ⟨X, hX, hyX, hyz⟩ := exists_component_of_mem_supportZone H hz
    have hphi := H.factor_ne_zero X hX
    unfold coarseFactor at hphi
    have hbase : baseFactorProduct q X ≠ 0 := by
      intro h
      apply hphi
      rw [h]
      ring
    unfold baseFactorProduct at hbase
    have hf := (Finset.prod_ne_zero_iff.mp hbase) y hyz
    rw [markAt_restrict_of_mem q hyX, hs] at hf
    have hb : q.baseChoice (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) =
        torusSiteInFrame (stepBlockFrame R.params.side n) 0 (blockSite y s.basePoint) := by
      have := baseChoice_of_labelAt_eq_some (q := q)
        (c := torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top y) (s := s)
        (by rw [ec]; exact hs)
      rw [ec] at this
      exact this
    rw [hb]
    have hbe := baseSitesAt_congr (J₀ := R.params.baseDepth) (nearbyLumps_stepHotLumps_eq H hGood hX hyX)
    unfold blockBaseWeight at hf ⊢
    rw [hbe]
    exact hf
theorem isHotCase_hotCaseGround (hA : ClusterExpansionOfAStep.AdmissionIsProduct) (hB : ClusterExpansionOfAStep.BaseLawIsProduct) :
    (hotCaseGround R V q).IsHotCase := by
  classical
  refine ⟨H.isBlockSide, rfl, rfl, frameGaugeField V q, q.labelSet, q.labeling, q.storedBadBonds, q.baseChoice,
    (hA R H.wellPosed n H.isBlockSide V q H.isHull _ _ _ _ _ (storedBadBonds_subset_markedBonds H)
      (isHullState_frameGaugeField H hGood)).mpr
      ⟨fun X hX => restrict_isAdmissibleState H hX, isExtension_frameGaugeField H hGood⟩,
    isHullState_frameGaugeField H hGood, storedBadBonds_subset_markedBonds H, subset_attachedSites H,
    fun Xc hXc => clusterFactor_frameGaugeField_ne_zero H hXc,
    fun c hm hst => bondMark_frameGaugeField_ne_zero H hm ((isRecorded_hotCaseGround_iff c).mp hst),
    baseLaw_frameGaugeField_ne_zero H hGood hB⟩
end Final
theorem hullStateIsHotCase_holds (hA : ClusterExpansionOfAStep.AdmissionIsProduct) (hB : ClusterExpansionOfAStep.BaseLawIsProduct)
    (hRead : ClusterExpansionOfAStep.HullRestrictedToComponent) (hGood : StepFrames.coldPlaquette_of_small_frameDeviation)
    (hFl : StepFloors.EventuallyFloorConditions) : StepGas.HullStateIsHotCase := by
  intro T hD
  obtain ⟨_, _, _, _, _, hσA, _, hNpos, _⟩ := hD.chain
  have hC : 0 < T.N 0 * T.threshold + 1 := by
    have := hNpos 0
    have := hD.σ_pos
    positivity
  obtain ⟨yF, hyF⟩ := hFl T hD _ 1 hC one_pos
  refine ⟨yF, fun y hy R hR hF n _ hside V q hq hphi => ?_⟩
  have fl := hyF R.coupling (hy.trans hR.le_coupling)
  have hσ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have ha : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
  have hL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hchain : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [ha, hL, hR.anchorRadius_eq]
    exact hD.chain
  have hgap : T.N 0 * R.params.threshold * Real.exp (-(T.δ₁ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) ≤
      R.params.threshold / 128 := by
    rw [hσ]
    have h1 := fl.cold_tail
    have hδ : T.δc / 4 ≤ T.δ₁ := by
      have h2 := hD.δc_le
      have h3 := hD.δ₁_pos
      have h4 := hD.δc_pos
      linarith
    have hm : (0 : ℝ) ≤ ((R.range / 2 ^ 11 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hexp : Real.exp (-(T.δ₁ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) ≤
        Real.exp (-(T.δc / 4 * boxRadius R.coupling)) := by
      apply Real.exp_le_exp.mpr
      have : boxRadius R.coupling = R.range / 2 ^ 11 := rfl
      rw [this]
      nlinarith
    have hpos := Real.exp_pos (-(T.δ₁ * ((R.range / 2 ^ 11 : ℕ) : ℝ)))
    have hσp := hD.σ_pos
    have hN := hNpos 0
    have s1 : T.N 0 * T.threshold * Real.exp (-(T.δ₁ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) ≤
        (T.N 0 * T.threshold + 1) * Real.exp (-(T.δc / 4 * boxRadius R.coupling)) := by
      apply mul_le_mul (by linarith) hexp hpos.le (by positivity)
    have s2 : (2⁻¹ : ℝ) ^ 10 * T.threshold ≤ T.threshold / 128 := by
      norm_num
      linarith
    linarith
  exact isHotCase_hotCaseGround (V := V) (q := q) (δ := T.δ₁) (lam := T.lam) (σA := T.σA) (cg := T.cg) (N := T.N)
    ⟨hF, hside, hchain, by rw [hσ]; exact hD.σ_le, hgap, hq, hphi, hRead⟩ hGood hA hB
end HullStates
end YangMills.Construction
end
