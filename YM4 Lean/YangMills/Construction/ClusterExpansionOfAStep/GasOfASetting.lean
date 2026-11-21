import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.FreeClassesOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.LawOfAWeightOnSpins
import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction
namespace StepGas
open Dobrushin TorusFields TorusLumps StepSettings StepCosts MarkedIntegrals
variable {R : StepSetup} {n : ℕ}
def settingMass [NeZero n] (s : ChartSetting R n) : ℝ≥0∞ :=
  ∫⁻ η, ENNReal.ofReal (s.cutoffProduct η * Real.exp (-s.potential η))
structure GasGround (R : StepSetup) (n : ℕ) [NeZero n] where
  region : Finset (TorusSite n)
  cut : Finset (TorusSite n)
  coarse : TorusField n
  state : CoarseState R n
section GroundSetting
variable [NeZero n] (G : GasGround R n)
def GasGround.IsRecorded (b : TorusBond (n * R.params.side)) : Prop :=
  ∃ s, G.state.markAt (parentBlock R.params.side b.1) = some s ∧
    (s.linkValue (siteOffset b.1, b.2)).isRight = true
open Classical in
def GasGround.recordedSites : Finset (TorusSite (n * R.params.side)) :=
  Finset.univ.filter fun z => (G.state.labelAt z).isRight = true
def GasGround.recordedLabel (z : G.recordedSites) : R.labels.Ω :=
  (G.state.labelAt z.1).getRight (Finset.mem_filter.mp z.2).2
open Classical in
def GasGround.recordedBad : Finset (TorusBond (n * R.params.side)) :=
  Finset.univ.filter fun b =>
    ∃ s, G.state.markAt (parentBlock R.params.side b.1) = some s ∧ s.badBond (siteOffset b.1, b.2) = true
open Classical in
def GasGround.anchorSites : Finset (TorusSite (n * R.params.side)) :=
  sitesInBlocks R.params.side G.cut ∪ G.recordedBad.image Prod.fst ∪ G.recordedSites
open Classical in
def GasGround.freeBonds : Finset (TorusBond (n * R.params.side)) :=
  (markedBonds R G.cut).filter fun b => ¬ G.IsRecorded b
def frameBlockSite (L n : ℕ) (y : TorusSite n) (o : BlockOffset L) : (stepBlockFrame L n).Site 0 :=
  torusSiteInFrame (stepBlockFrame L n) 0 (blockSite y o)
def GasGround.groundBases : BaseChoice R.params.side n := fun c =>
  match G.state.markAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
  | some s => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) s.basePoint
  | none => BlockAverages.cellCentre (F := stepBlockFrame R.params.side n) 0 c
end GroundSetting
theorem sigmaFinite_comap_subtype_val {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (P : α → Prop) : SigmaFinite (μ.comap (Subtype.val : {a // P a} → α)) := by
  classical
  by_cases h : Function.Injective (Subtype.val : {a // P a} → α) ∧
      ∀ s : Set {a // P a}, MeasurableSet s → NullMeasurableSet (Subtype.val '' s : Set α) μ
  · refine ⟨⟨⟨fun k => Subtype.val ⁻¹' spanningSets μ k, fun _ => trivial, fun k => ?_, ?_⟩⟩⟩
    · rw [Measure.comap_apply₀ _ _ h.1 h.2
        ((measurableSet_spanningSets μ k).preimage measurable_subtype_coe).nullMeasurableSet]
      exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) (measure_spanningSets_lt_top μ k)
    · rw [← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]
  · rw [Measure.comap, dif_neg h]
    infer_instance
theorem sigmaFinite_withNoneMeasure {α : Type} [MeasurableSpace α] (ν : Measure α) [SigmaFinite ν] :
    SigmaFinite (withNoneMeasure ν) := by
  have hs : ∀ k, MeasurableSet (Set.range (Sum.inl : Unit → WithNone α) ∪ Sum.inr '' spanningSets ν k) :=
    fun k => measurableSet_range_inl.union (measurableSet_spanningSets ν k).inr_image
  refine ⟨⟨⟨fun k => Set.range (Sum.inl : Unit → WithNone α) ∪ Sum.inr '' spanningSets ν k, fun _ => trivial,
    fun k => ?_, ?_⟩⟩⟩
  · unfold withNoneMeasure
    rw [Measure.add_apply, Measure.map_apply measurable_inr (hs k)]
    have : (Sum.inr : α → WithNone α) ⁻¹' (Set.range (Sum.inl : Unit → WithNone α) ∪ Sum.inr '' spanningSets ν k) =
        spanningSets ν k := by
      ext a
      simp
    rw [this]
    exact ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, measure_spanningSets_lt_top ν k⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_univ, iff_true]
    rcases x with u | a
    · exact ⟨0, Or.inl ⟨u, rfl⟩⟩
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (show a ∈ ⋃ k, spanningSets ν k by
        rw [iUnion_spanningSets]; trivial)
      exact ⟨k, Or.inr ⟨a, hk, rfl⟩⟩
section Supports
abbrev GasSupport (R : StepSetup) (n : ℕ) : Type := ClusterSupport R.params.side n
variable [NeZero n]
abbrev GasSupport.sites (θ : GasSupport R n) : Finset (TorusSite (n * R.params.side)) :=
  clusterSupportSites R.params.side θ
abbrev GasSupport.core (θ : GasSupport R n) : Finset (TorusSite n) := supportCore R.params.side R.range θ
open Classical in
def GasSupport.coreBonds (θ : GasSupport R n) : Finset (TorusBond (n * R.params.side)) :=
  Finset.univ.filter fun b =>
    parentBlock R.params.side b.1 ∈ θ.core ∧
      parentBlock R.params.side (b.1 + unitStep (n * R.params.side) b.2) ∈ θ.core
def GasSupport.FarApart (θ θ' : GasSupport R n) : Prop :=
  ∀ z ∈ θ.sites, ∀ z' ∈ θ'.sites, 10 * R.range < supDist z z'
theorem GasSupport.FarApart.symm {θ θ' : GasSupport R n} (h : θ.FarApart θ') : θ'.FarApart θ :=
  fun z hz z' hz' => by rw [supDist_comm]; exact h z' hz' z hz
abbrev GasSupport.coreDiam (θ : GasSupport R n) : ℕ := siteDiameter θ.core
def GasSupport.Meets (θ : GasSupport R n) (Y : TorusSite n) : Prop :=
  (∃ b ∈ θ.1, parentBlock R.params.side b.1 = Y) ∨ ∃ z ∈ θ.2, parentBlock R.params.side z = Y
def GasSupport.Touches (θ : GasSupport R n) (A : Finset (TorusSite n)) : Prop :=
  (∃ b ∈ θ.1, parentBlock R.params.side b.1 ∈ A) ∨ ∃ z ∈ θ.2, parentBlock R.params.side z ∈ A
abbrev SupportState (θ : GasSupport R n) : Type :=
  (θ.coreBonds → BlockAverages.UnitQuaternion) × (θ.2 → R.labels.Ω) × (θ.core → BlockOffset R.params.side)
def supportStateMeasure (θ : GasSupport R n) : Measure (SupportState θ) :=
  (Measure.pi fun _ : θ.coreBonds => haarUnit).prod
    ((Measure.pi fun _ : θ.2 => R.labels.μ).prod (Measure.count : Measure (θ.core → BlockOffset R.params.side)))
abbrev GasFamily (R : StepSetup) (n : ℕ) [NeZero n] : Type :=
  ∀ θ : GasSupport R n, WithNone (SupportState θ)
def GasFamily.empty : GasFamily R n := fun _ => Sum.inl ()
open Classical in
def GasFamily.single (θ : GasSupport R n) (s : SupportState θ) : GasFamily R n :=
  Function.update GasFamily.empty θ (Sum.inr s)
def GasFamily.Occupies (γ : GasFamily R n) (θ : GasSupport R n) : Prop := (γ θ).isRight = true
def GasFamily.state (γ : GasFamily R n) {θ : GasSupport R n} (h : γ.Occupies θ) : SupportState θ :=
  (γ θ).getRight h
open Classical in
def GasFamily.fieldAt (γ : GasFamily R n) (b : TorusBond (n * R.params.side)) :
    WithNone BlockAverages.UnitQuaternion :=
  if h : ∃ θ, γ.Occupies θ ∧ b ∈ θ.coreBonds then
    Sum.inr ((γ.state h.choose_spec.1).1 ⟨b, h.choose_spec.2⟩)
  else Sum.inl ()
open Classical in
def GasFamily.sites (γ : GasFamily R n) : Finset (TorusSite (n * R.params.side)) :=
  (Finset.univ.filter fun θ => γ.Occupies θ).biUnion Prod.snd
theorem GasFamily.exists_of_mem_sites {γ : GasFamily R n} {z : TorusSite (n * R.params.side)}
    (h : z ∈ γ.sites) : ∃ θ, γ.Occupies θ ∧ z ∈ θ.2 := by
  classical
  obtain ⟨θ, hθ, hz⟩ := Finset.mem_biUnion.mp h
  exact ⟨θ, (Finset.mem_filter.mp hθ).2, hz⟩
def GasFamily.labelAt (γ : GasFamily R n) {z : TorusSite (n * R.params.side)} (h : z ∈ γ.sites) :
    R.labels.Ω :=
  (γ.state (GasFamily.exists_of_mem_sites h).choose_spec.1).2.1
    ⟨z, (GasFamily.exists_of_mem_sites h).choose_spec.2⟩
open Classical in
def GasFamily.baseAt (γ : GasFamily R n) (y : TorusSite n) : WithNone (BlockOffset R.params.side) :=
  if h : ∃ θ, γ.Occupies θ ∧ y ∈ θ.core then
    Sum.inr ((γ.state h.choose_spec.1).2.2 ⟨y, h.choose_spec.2⟩)
  else Sum.inl ()
variable (G : GasGround R n)
open Classical in
def GasGround.settingWithFamily (γ : GasFamily R n) : ChartSetting R n where
  coarse := G.coarse
  region := G.region
  fine := fun x i => match γ.fieldAt (x, i) with
    | Sum.inr g => g
    | Sum.inl _ => G.state.fieldWithStoredLinks (trivialField _) x i
  support := G.recordedSites ∪ γ.sites
  labelling := fun z => if h : z.1 ∈ γ.sites then γ.labelAt h else
    G.recordedLabel ⟨z.1, (Finset.mem_union.mp z.2).resolve_right h⟩
  bases := fun c => match γ.baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
    | Sum.inr o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o
    | Sum.inl _ => G.groundBases c
  free := G.freeBonds.filter fun b => γ.fieldAt b = Sum.inl ()
  bad := G.recordedBad ∪ (Finset.univ.filter fun θ => γ.Occupies θ).biUnion Prod.fst ∪
    (chartBonds R.params.side n).filter fun b => parentBlock R.params.side b.1 ∈ G.cut
def GasGround.settingOf (γ : GasFamily R n) : ChartSetting R n :=
  { G.settingWithFamily γ with fine := (G.settingWithFamily γ).field 0 }
def GasGround.groundSetting : ChartSetting R n := G.settingOf GasFamily.empty
def GasGround.frameField (γ : GasFamily R n) : TorusField (n * R.params.side) := (G.settingOf γ).fine
structure GasGround.IsGasSupport (θ : GasSupport R n) : Prop where
  isCluster : IsClusterSupport R.params.side R.range θ
  bad_subset_free : θ.1 ⊆ G.freeBonds
  far_from_anchor : ∀ z ∈ θ.sites, ∀ z' ∈ G.anchorSites, 10 * R.range < supDist z z'
def baseUniformWeight (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) (y : TorusSite n) : ℝ :=
  open Classical in
  if b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) then
    1 / ((Finset.univ.filter fun o : BlockOffset R.params.side =>
      Function.update b (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
          (frameBlockSite R.params.side n y o) ∈
        baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W)).card : ℝ)
  else 0
open Classical in
def GasGround.supportMarks (θ : GasSupport R n) (W : TorusField (n * R.params.side)) : ℝ :=
  ∏ b ∈ θ.coreBonds ∩ markedBonds R G.cut,
    if b ∈ θ.1 then 1 - bondMark R G.coarse W b else bondMark R G.coarse W b
def GasGround.activity (θ : GasSupport R n) (s : SupportState θ) : ℝ :=
  G.supportMarks θ (G.frameField (GasFamily.single θ s)) *
    (∏ X ∈ chainComponents R.range θ.2, R.clusterFactor (n * R.params.side) (G.frameField (GasFamily.single θ s))
      (G.settingOf (GasFamily.single θ s)).support (G.settingOf (GasFamily.single θ s)).labelling X) *
    ∏ y ∈ θ.core, baseUniformWeight (G.frameField (GasFamily.single θ s)) (G.settingOf (GasFamily.single θ s)).bases y
def GasGround.IsAllowed (θ : GasSupport R n) (s : SupportState θ) : Prop :=
  IsHullState R.params R.range (G.frameField (GasFamily.single θ s)) (G.settingOf (GasFamily.single θ s)).support ∧
    (∀ X ∈ chainComponents R.range θ.2, R.clusterFactor (n * R.params.side) (G.frameField (GasFamily.single θ s))
      (G.settingOf (GasFamily.single θ s)).support (G.settingOf (GasFamily.single θ s)).labelling X ≠ 0) ∧
    (∀ b ∈ θ.coreBonds ∩ markedBonds R G.cut, b ∉ θ.1 →
      bondMark R G.coarse (G.frameField (GasFamily.single θ s)) b ≠ 0) ∧
    ∀ y ∈ θ.core, baseUniformWeight (G.frameField (GasFamily.single θ s))
      (G.settingOf (GasFamily.single θ s)).bases y ≠ 0
abbrev GasGround.GasSpin : Type := {θ : GasSupport R n // G.IsGasSupport θ}
abbrev GasGround.SpinState (i : G.GasSpin) : Type := {s : SupportState i.1 // G.IsAllowed i.1 s}
abbrev GasGround.SpinValue (i : G.GasSpin) : Type := WithNone (G.SpinState i)
abbrev GasGround.Config : Type := ∀ i : G.GasSpin, G.SpinValue i
open Classical in
def GasGround.familyOf (σ : G.Config) : GasFamily R n := fun θ =>
  if h : G.IsGasSupport θ then
    match σ ⟨θ, h⟩ with
    | Sum.inr s => Sum.inr s.1
    | Sum.inl _ => Sum.inl ()
  else Sum.inl ()
open Classical in
instance : Fintype G.GasSpin := Fintype.ofFinite _
instance : DecidableEq G.GasSpin := Classical.decEq _
def GasGround.pairConstraint : PairConstraint G.SpinValue where
  vacant _ := Sum.inl ()
  compatible i j s t := s = Sum.inl () ∨ t = Sum.inl () ∨ i.1.FarApart j.1
  compatible_symm _ _ _ _ h := by
    rcases h with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h.symm)
  vacant_compatible _ _ _ := Or.inl rfl
def GasGround.spinStateMeasure (i : G.GasSpin) : Measure (G.SpinState i) :=
  ((supportStateMeasure i.1).comap Subtype.val).withDensity fun s => ENNReal.ofReal (G.activity i.1 s.1)
open Classical in
def GasGround.referenceMeasureOff (off : G.GasSpin → Prop) (i : G.GasSpin) : Measure (G.SpinValue i) :=
  if off i then Measure.map Sum.inl (Measure.dirac ()) else withNoneMeasure (G.spinStateMeasure i)
def GasGround.referenceMeasure (A : Finset (TorusSite n)) (i : G.GasSpin) : Measure (G.SpinValue i) :=
  G.referenceMeasureOff (fun j => j.1.Touches A) i
open Classical in
def GasGround.weight (σ : G.Config) : ℝ :=
  if G.pairConstraint.IsAdmissible σ then (settingMass (G.settingOf (G.familyOf σ))).toReal else 0
def GasGround.allVacant : G.Config := fun _ => Sum.inl ()
def GasGround.partitionFunction (A : Finset (TorusSite n)) : ℝ≥0∞ :=
  ∫⁻ σ, G.pairConstraint.weightDensity G.weight σ ∂Measure.pi (G.referenceMeasure A)
def GasGround.coldWeight : ℝ := G.weight G.allVacant
def GasGround.xi (A : Finset (TorusSite n)) : ℝ := (G.partitionFunction A).toReal / G.coldWeight
def GasGround.NoSpinMeets (Y : TorusSite n) : Set G.Config :=
  {σ | ∀ i : G.GasSpin, i.1.Meets Y → σ i = Sum.inl ()}
instance (θ : GasSupport R n) : SigmaFinite (supportStateMeasure θ) := by
  unfold supportStateMeasure
  infer_instance
instance (i : G.GasSpin) : SigmaFinite (G.spinStateMeasure i) := by
  unfold GasGround.spinStateMeasure
  have := sigmaFinite_comap_subtype_val (supportStateMeasure i.1) (G.IsAllowed i.1)
  infer_instance
instance (off : G.GasSpin → Prop) (i : G.GasSpin) : SigmaFinite (G.referenceMeasureOff off i) := by
  classical
  unfold GasGround.referenceMeasureOff
  split_ifs
  · infer_instance
  · exact sigmaFinite_withNoneMeasure _
instance (A : Finset (TorusSite n)) (i : G.GasSpin) : SigmaFinite (G.referenceMeasure A i) := by
  unfold GasGround.referenceMeasure
  infer_instance
def GasGround.gibbsLawOff (off : G.GasSpin → Prop) : Measure G.Config :=
  G.pairConstraint.gibbsLaw (G.referenceMeasureOff off) G.weight
def GasGround.gibbsLaw (A : Finset (TorusSite n)) : Measure G.Config := G.gibbsLawOff fun j => j.1.Touches A
def GasGround.expectation (A : Finset (TorusSite n)) (F : G.Config → ℝ) : ℝ := ∫ σ, F σ ∂(G.gibbsLaw A)
def GasGround.blockDensity (Y : TorusSite n) : ℝ :=
  ∫ u, (Real.log (G.xi (precedingBlocks u Y)) - Real.log (G.xi (insert Y (precedingBlocks u Y)))) ∂(randomOrderLaw n)
def GasGround.badBondsOf (σ : G.Config) : Finset (TorusBond (n * R.params.side)) :=
  open Classical in
  G.recordedBad ∪ (Finset.univ.filter fun θ => (G.familyOf σ).Occupies θ).biUnion Prod.fst
end Supports
section Situations
variable [NeZero n] (G : GasGround R n)
structure GasGround.IsColdCase : Prop where
  n₀_le : R.params.n₀ ≤ n
  coarse_cold : TorusFields.IsCold (9 / 8 * R.params.threshold) G.coarse
  region_eq : G.region = Finset.univ
  cut_eq : G.cut = ∅
  state_empty : G.state.1 = ∅
structure GasGround.IsHotCase : Prop where
  isBlockSide : IsBlockTorusSide R.params n
  region_eq : G.region = Finset.univ \ thickening LumpContours.lumpRange (torusHotSites R.params G.coarse)
  cut_eq : G.cut = hotCoreSites R G.coarse
  exists_state : ∃ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
      (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
    coarseStateOf R G.cut W Yt ωt bad b = G.state ∧ IsHullState R.params R.range W Yt ∧
      bad ⊆ markedBonds R G.cut ∧
      (open Classical in bad.image Prod.fst ∪ Yt) ⊆ attachedSites R.params.side R.range bad Yt G.cut ∧
      (∀ X ∈ chainComponents R.range Yt, R.clusterFactor (n * R.params.side) W Yt ωt X ≠ 0) ∧
      (∀ c ∈ markedBonds R G.cut, G.IsRecorded c →
        (open Classical in if c ∈ bad then 1 - bondMark R G.coarse W c else bondMark R G.coarse W c) ≠ 0) ∧
      baseLaw W b ≠ 0
def GasGround.IsAdmissibleGround : Prop := G.IsColdCase ∨ G.IsHotCase
end Situations
section TwoGrounds
variable {n' : ℕ} [NeZero n] [NeZero n']
structure GroundsAgreeNear (G : GasGround R n) (G' : GasGround R n') (Y : TorusSite n) (Y' : TorusSite n')
    (m : ℕ) : Prop where
  lt_extent : 2 * m + 2 < n
  lt_extent' : 2 * m + 2 < n'
  coarse_agree : FieldsAgreeNear G.coarse G'.coarse Y Y' m
  cut_iff : ∀ h, OffsetInBox m h → (Y + siteOfInt h ∈ G.cut ↔ Y' + siteOfInt h ∈ G'.cut)
  marking_eq : ∀ h, OffsetInBox m h → G.state.markAt (Y + siteOfInt h) = G'.state.markAt (Y' + siteOfInt h)
def BlockSetsAgreeNear (A : Finset (TorusSite n)) (A' : Finset (TorusSite n')) (Y : TorusSite n)
    (Y' : TorusSite n') (m : ℕ) : Prop :=
  ∀ h, OffsetInBox m h → (Y + siteOfInt h ∈ A ↔ Y' + siteOfInt h ∈ A')
end TwoGrounds
end StepGas
end YangMills.Construction
end
