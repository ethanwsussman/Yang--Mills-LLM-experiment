import YangMills.Construction.ClusterExpansionOfAStep.SizeOfAClassProof
import YangMills.Construction.ResponseInTheExpansion.ScoreOfAClassIsPaid
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction
namespace StepGas
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings StepCosts BlockOffsets RenormalizationStepParameters
theorem lintegral_comap_subtype_val_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (P : α → Prop)
    {g : α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ v : {a // P a}, g v.1 ∂(μ.comap (Subtype.val : {a // P a} → α)) ≤ ∫⁻ a, g a ∂μ := by apply _root_.YangMills.Construction.StepGas.lintegral_comap_subtypeVal_le <;> assumption
theorem lintegral_prod_three_le_one {A N B : Type} [MeasurableSpace A] [MeasurableSpace N] [MeasurableSpace B]
    [Fintype B] [MeasurableSingletonClass B] (μA : Measure A) [IsProbabilityMeasure μA] (μN : Measure N)
    [SFinite μN] (Bs : A → B → ℝ≥0∞) (J : A → N → ℝ≥0∞) (Q : A → ℝ≥0∞) (hBs : ∀ b, Measurable fun a => Bs a b)
    (hJ : Measurable fun p : A × N => J p.1 p.2) (hQ : Measurable Q) (hsum : ∀ a, ∑ b, Bs a b ≤ 1)
    (hint : ∀ a, Q a * ∫⁻ ν, J a ν ∂μN ≤ 1) :
    ∫⁻ p : A × N × B, Bs p.1 p.2.2 * J p.1 p.2.1 * Q p.1 ∂(μA.prod (μN.prod Measure.count)) ≤ 1 := by apply _root_.YangMills.Construction.StepGas.lintegral_prod_three_le <;> assumption
theorem sum_le_one_of_le_prod_indicator_inv_card {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] (A : I → Finset O) (f : (I → O) → ℝ≥0∞)
    (hf : ∀ o, f o ≤ ∏ i, (if o i ∈ A i then ((A i).card : ℝ≥0∞)⁻¹ else 0)) : ∑ o, f o ≤ 1 := by apply _root_.YangMills.Construction.StepGas.sum_le_one_of_le_prod_uniform <;> assumption
section Supports
variable {R : StepSetup} {n : ℕ} [NeZero n] (G : GasGround R n) (γ : GasFamily R n) (θ : GasSupport R n)
open Classical in
def GasGround.freeBondsWithSupport : Finset (TorusBond (n * R.params.side)) :=
  (G.settingWithFamily γ).free.filter fun b => b ∉ θ.coreBonds
def GasGround.fieldWithSupport (a : θ.coreBonds → UnitQuaternion) : TorusField (n * R.params.side) :=
  StepSettings.frameField R (G.freeBondsWithSupport γ θ) G.coarse
    (StepSettings.frameField R (G.freeBondsWithSupport γ θ) G.coarse (G.baseWithClass γ θ a))
theorem GasGround.continuous_fieldWithSupport : Continuous (G.fieldWithSupport γ θ) :=
  (continuous_frameField _ _).comp ((continuous_frameField _ _).comp (continuous_baseWithClass G))
def GasGround.sitesWithSupport : Finset (TorusSite (n * R.params.side)) :=
  G.recordedSites ∪ (γ.sites ∪ θ.2)
theorem GasGround.mem_support_of_mem_sitesWithSupport {z : TorusSite (n * R.params.side)}
    (hz : z ∈ G.sitesWithSupport γ θ) (h : z ∉ θ.2) : z ∈ (G.settingWithFamily γ).support := by apply _root_.YangMills.Construction.StepGas.GasGround.mem_support_of_mem_sitesInsert <;> assumption
open Classical in
def GasGround.labellingWithSupport (ν : θ.2 → R.labels.Ω) (z : G.sitesWithSupport γ θ) : R.labels.Ω :=
  if h : z.1 ∈ θ.2 then ν ⟨z.1, h⟩
  else (G.settingWithFamily γ).labelling ⟨z.1, G.mem_support_of_mem_sitesWithSupport γ θ z.2 h⟩
theorem GasGround.measurable_labellingWithSupport : Measurable (G.labellingWithSupport γ θ) := by
  classical
  refine measurable_pi_iff.mpr fun z => ?_
  unfold GasGround.labellingWithSupport
  by_cases h : z.1 ∈ θ.2
  · simp only [dif_pos h]
    exact measurable_pi_apply _
  · simp only [dif_neg h]
    exact measurable_const
variable {γ θ}
variable (s : SupportState θ)
theorem GasGround.settingOf_insertClass_field_zero (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False) :
    (G.settingOf (γ.insertClass θ s)).field 0 = G.fieldWithSupport γ θ s.1 := by
  rw [G.field_zero_insertClass s hs hc, G.settingWithFamily_free_insertClass s hs hc]
  rfl
theorem GasGround.settingOf_insertClass_support :
    (G.settingOf (γ.insertClass θ s)).support = G.sitesWithSupport γ θ := by apply _root_.YangMills.Construction.StepGas.GasGround.support_settingOf_insertClass <;> assumption
theorem GasGround.settingOf_insertClass_labelling_apply (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False)
    (z : TorusSite (n * R.params.side)) (hz : z ∈ (G.settingOf (γ.insertClass θ s)).support)
    (hz' : z ∈ G.sitesWithSupport γ θ) :
    (G.settingOf (γ.insertClass θ s)).labelling ⟨z, hz⟩ = G.labellingWithSupport γ θ s.2.1 ⟨z, hz'⟩ := by
  classical
  have hs' : (γ.insertClass θ s).CoresDisjoint := hs.insertClass hc
  have hself : (γ.insertClass θ s).Occupies θ := GasFamily.occupies_insertClass.mpr (Or.inl rfl)
  show (if h : z ∈ (γ.insertClass θ s).sites then (γ.insertClass θ s).labelAt h else
    G.recordedLabel ⟨z, (Finset.mem_union.mp hz).resolve_right h⟩) = _
  unfold GasGround.labellingWithSupport
  by_cases hθ : z ∈ θ.2
  · have hzs : z ∈ (γ.insertClass θ s).sites := by
      rw [GasFamily.sites_insertClass]
      exact Finset.mem_union_right _ hθ
    rw [dif_pos hzs, GasFamily.labelAt_eq_of_mem _ hs' hzs hself hθ, GasFamily.state_insertClass_self]
    simp only [dif_pos hθ]
  · simp only [dif_neg hθ]
    show _ = (if h : z ∈ γ.sites then γ.labelAt h else
      G.recordedLabel ⟨z, (Finset.mem_union.mp (G.mem_support_of_mem_sitesWithSupport γ θ hz' hθ)).resolve_right h⟩)
    by_cases hzγ : z ∈ γ.sites
    · have hzs : z ∈ (γ.insertClass θ s).sites := by
        rw [GasFamily.sites_insertClass]
        exact Finset.mem_union_left _ hzγ
      rw [dif_pos hzs, dif_pos hzγ]
      obtain ⟨θ', hh, hzθ⟩ := GasFamily.exists_of_mem_sites hzγ
      have hne : θ' ≠ θ := fun e => hθ (e ▸ hzθ)
      have hh' : (γ.insertClass θ s).Occupies θ' := GasFamily.occupies_insertClass.mpr (Or.inr hh)
      rw [GasFamily.labelAt_eq_of_mem _ hs' hzs hh' hzθ, GasFamily.labelAt_eq_of_mem _ hs hzγ hh hzθ,
        GasFamily.state_insertClass_of_ne hne hh' hh]
    · have hzs : z ∉ (γ.insertClass θ s).sites := by
        rw [GasFamily.sites_insertClass]
        simp [hzγ, hθ]
      rw [dif_neg hzs, dif_neg hzγ]
theorem dependent_congr_finset {T Ω α : Type} (f : ∀ Y : Finset T, (Y → Ω) → α) {Y Y' : Finset T} (h : Y = Y')
    (ω : Y → Ω) (ω' : Y' → Ω) (hω : ∀ z (hz : z ∈ Y) (hz' : z ∈ Y'), ω ⟨z, hz⟩ = ω' ⟨z, hz'⟩) :
    f Y ω = f Y' ω' := by apply _root_.YangMills.Construction.StepGas.ActivityMeasurable.dependent_congr <;> assumption
theorem lintegral_pi_finset_cast {T Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {U U' : Finset T} (h : U = U')
    (f : (U → Ω) → ℝ≥0∞) :
    ∫⁻ ν, f ν ∂(Measure.pi fun _ : U => μ) =
      ∫⁻ ν', f (fun z => ν' ⟨z.1, h ▸ z.2⟩) ∂(Measure.pi fun _ : U' => μ) := by apply _root_.YangMills.Construction.StepGas.lintegral_pi_congr_finset <;> assumption
end Supports
section LabelIntegrals
variable {R : StepSetup} {n : ℕ} [NeZero n] (G : GasGround R n) (γ : GasFamily R n) (θ : GasSupport R n)
def GasGround.LabelsHullCondition (a : θ.coreBonds → UnitQuaternion) (ν : θ.2 → R.labels.Ω) : Prop :=
  IsHullState R.params R.range (G.fieldWithSupport γ θ a) (G.sitesWithSupport γ θ) ∧
    ∀ X ∈ chainComponents R.range (G.sitesWithSupport γ θ),
      R.clusterFactor (n * R.params.side) (G.fieldWithSupport γ θ a) (G.sitesWithSupport γ θ)
        (G.labellingWithSupport γ θ ν) X ≠ 0
def GasGround.labelWeightValue (a : θ.coreBonds → UnitQuaternion) (ν : θ.2 → R.labels.Ω) : ℝ :=
  (∏ X ∈ chainComponents R.range θ.2, R.clusterFactor (n * R.params.side) (G.fieldWithSupport γ θ a)
      (G.sitesWithSupport γ θ) (G.labellingWithSupport γ θ ν) X) *
    Real.exp (∑ y ∈ sitesNear R.range θ.2, R.siteDensity (n * R.params.side) y (G.fieldWithSupport γ θ a)
      (G.sitesWithSupport γ θ) (G.labellingWithSupport γ θ ν))
open Classical in
def GasGround.labelIntegrandWithSupport (a : θ.coreBonds → UnitQuaternion) (ν : θ.2 → R.labels.Ω) : ℝ≥0∞ :=
  if G.LabelsHullCondition γ θ a ν then ENNReal.ofReal (G.labelWeightValue γ θ a ν) else 0
def GasGround.supportPrice (a : θ.coreBonds → UnitQuaternion) : ℝ :=
  R.coupling * R.params.κ * R.params.threshold ^ 2 *
      ((hotLumpsWithin R.params (G.fieldWithSupport γ θ a) θ.2).card : ℝ) +
    R.params.κ₁ * R.coupling * R.params.threshold ^ 2 *
      (excessLength R.params R.range θ.2 (G.fieldWithSupport γ θ a) : ℝ)
variable {γ θ}
theorem measurableSet_setOf_isHullState (hfit : R.params.Admissible) (r : ℕ)
    (Y : Finset (TorusSite (n * R.params.side))) :
    MeasurableSet {W : TorusField (n * R.params.side) | IsHullState R.params r W Y} := by apply _root_.YangMills.Construction.StepGas.measurableSet_isHullState <;> assumption
theorem GasGround.measurable_labelIntegrandWithSupport (hfit : R.params.Admissible) (hrow : R.HasExpansions)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) :
    Measurable fun p : (θ.coreBonds → UnitQuaternion) × (θ.2 → R.labels.Ω) =>
      G.labelIntegrandWithSupport γ θ p.1 p.2 := by
  classical
  obtain ⟨-, hΦ, hφ⟩ := hrow.2.borel (n * R.params.side) hside (G.sitesWithSupport γ θ)
  have hE : Measurable fun p : (θ.coreBonds → UnitQuaternion) × (θ.2 → R.labels.Ω) =>
      ((G.fieldWithSupport γ θ p.1, G.labellingWithSupport γ θ p.2) :
        TorusField (n * R.params.side) × (G.sitesWithSupport γ θ → R.labels.Ω)) :=
    (((G.continuous_fieldWithSupport γ θ).measurable).comp measurable_fst).prodMk
      ((G.measurable_labellingWithSupport γ θ).comp measurable_snd)
  set S : Set (TorusField (n * R.params.side) × (G.sitesWithSupport γ θ → R.labels.Ω)) :=
    {p | IsHullState R.params R.range p.1 (G.sitesWithSupport γ θ) ∧
      ∀ X ∈ chainComponents R.range (G.sitesWithSupport γ θ),
        R.clusterFactor (n * R.params.side) p.1 (G.sitesWithSupport γ θ) p.2 X ≠ 0} with hS
  have hSm : MeasurableSet S := by
    have h1 : MeasurableSet {p : TorusField (n * R.params.side) × (G.sitesWithSupport γ θ → R.labels.Ω) |
        IsHullState R.params R.range p.1 (G.sitesWithSupport γ θ)} :=
      measurable_fst (measurableSet_setOf_isHullState hfit R.range _)
    have h2 : MeasurableSet {p : TorusField (n * R.params.side) × (G.sitesWithSupport γ θ → R.labels.Ω) |
        ∀ X ∈ chainComponents R.range (G.sitesWithSupport γ θ),
          R.clusterFactor (n * R.params.side) p.1 (G.sitesWithSupport γ θ) p.2 X ≠ 0} := by
      have : {p : TorusField (n * R.params.side) × (G.sitesWithSupport γ θ → R.labels.Ω) |
          ∀ X ∈ chainComponents R.range (G.sitesWithSupport γ θ),
            R.clusterFactor (n * R.params.side) p.1 (G.sitesWithSupport γ θ) p.2 X ≠ 0} =
          ⋂ X ∈ chainComponents R.range (G.sitesWithSupport γ θ),
            (fun p : TorusField (n * R.params.side) × (G.sitesWithSupport γ θ → R.labels.Ω) =>
              R.clusterFactor (n * R.params.side) p.1 (G.sitesWithSupport γ θ) p.2 X) ⁻¹' {0}ᶜ := by
        ext p
        simp
      rw [this]
      exact Finset.measurableSet_biInter _ fun X _ => hΦ X (measurableSet_singleton 0).compl
    exact h1.inter h2
  set g : TorusField (n * R.params.side) × (G.sitesWithSupport γ θ → R.labels.Ω) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((∏ X ∈ chainComponents R.range θ.2,
        R.clusterFactor (n * R.params.side) p.1 (G.sitesWithSupport γ θ) p.2 X) *
      Real.exp (∑ y ∈ sitesNear R.range θ.2,
        (if IsHullState R.params (clusterRange R.coupling) p.1 (G.sitesWithSupport γ θ) ∧
            ∀ X ∈ chainComponents (clusterRange R.coupling) (G.sitesWithSupport γ θ),
              R.clusterFactor (n * R.params.side) p.1 (G.sitesWithSupport γ θ) p.2 X ≠ 0
          then R.siteDensity (n * R.params.side) y p.1 (G.sitesWithSupport γ θ) p.2 else 0))) with hg
  have hgm : Measurable g := by
    refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)
    · exact Finset.measurable_prod _ fun X _ => hΦ X
    · exact Real.measurable_exp.comp (Finset.measurable_sum _ fun y _ => hφ y)
  have hfinal : (fun p : (θ.coreBonds → UnitQuaternion) × (θ.2 → R.labels.Ω) =>
      G.labelIntegrandWithSupport γ θ p.1 p.2) =
      (S.indicator g) ∘ fun p => ((G.fieldWithSupport γ θ p.1, G.labellingWithSupport γ θ p.2) :
        TorusField (n * R.params.side) × (G.sitesWithSupport γ θ → R.labels.Ω)) := by
    funext p
    simp only [Function.comp]
    unfold GasGround.labelIntegrandWithSupport
    by_cases h : G.LabelsHullCondition γ θ p.1 p.2
    · have hmem : ((G.fieldWithSupport γ θ p.1, G.labellingWithSupport γ θ p.2) :
          TorusField (n * R.params.side) × (G.sitesWithSupport γ θ → R.labels.Ω)) ∈ S := h
      rw [if_pos h, Set.indicator_of_mem hmem]
      simp only [hg, GasGround.labelWeightValue]
      congr 3
      refine Finset.sum_congr rfl fun y _ => ?_
      exact (if_pos h).symm
    · have hmem : ((G.fieldWithSupport γ θ p.1, G.labellingWithSupport γ θ p.2) :
          TorusField (n * R.params.side) × (G.sitesWithSupport γ θ → R.labels.Ω)) ∉ S := h
      rw [if_neg h, Set.indicator_of_notMem hmem]
  rw [hfinal]
  exact (hgm.indicator hSm).comp hE
end LabelIntegrals
section BaseChoices
variable {R : StepSetup} {n : ℕ} [NeZero n] (G : GasGround R n) (θ : GasSupport R n)
theorem coresDisjoint_empty : (GasFamily.empty : GasFamily R n).CoresDisjoint := by apply _root_.YangMills.Construction.StepGas.ActivityMeasurable.coresDisjoint_empty <;> assumption
theorem empty_occupies_false : ∀ θ' : GasSupport R n, (GasFamily.empty : GasFamily R n).Occupies θ' →
    ∀ y, y ∈ θ.core → y ∈ θ'.core → False := by apply _root_.YangMills.Construction.StepGas.ActivityMeasurable.empty_no_overlap <;> assumption
def GasGround.singleSupportField (a : θ.coreBonds → UnitQuaternion) : TorusField (n * R.params.side) :=
  StepSettings.frameField R (G.freeBondsWithSupport GasFamily.empty θ) G.coarse (G.baseWithClass GasFamily.empty θ a)
theorem GasGround.continuous_singleSupportField : Continuous (G.singleSupportField θ) :=
  (continuous_frameField _ _).comp (continuous_baseWithClass G)
variable {θ}
theorem GasGround.frameField_single_eq (s : SupportState θ) :
    G.frameField (GasFamily.single θ s) = G.singleSupportField θ s.1 := by
  have hsingle : GasFamily.single θ s = (GasFamily.empty : GasFamily R n).insertClass θ s := rfl
  show (G.settingWithFamily (GasFamily.single θ s)).field 0 = _
  rw [ChartSetting.field_zero, hsingle]
  show StepSettings.frameField R (G.settingWithFamily (GasFamily.empty.insertClass θ s)).free G.coarse
    (G.settingWithFamily (GasFamily.empty.insertClass θ s)).fine = _
  rw [G.settingWithFamily_free_insertClass s coresDisjoint_empty (empty_occupies_false θ),
    G.settingWithFamily_fine_insertClass s coresDisjoint_empty (empty_occupies_false θ)]
  rfl
variable (θ)
theorem toTorusSite_torusSiteInFrame_one (y : TorusSite n) (L : ℕ) [NeZero L] :
    (toTorusSite n (torusSiteInFrame (stepBlockFrame L n) 1 y : (stepBlockFrame L n).Cell) : TorusSite n) = y := by apply _root_.YangMills.Construction.StepGas.toTorusSite_torusSiteInFrame <;> assumption
open Classical in
def GasGround.basesWithOffsets (o : θ.core → BlockOffset R.params.side) : BaseChoice R.params.side n := fun c =>
  if h : toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c ∈ θ.core then
    frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) (o ⟨_, h⟩)
  else G.groundBases c
variable {θ}
theorem GasGround.settingOf_single_bases (s : SupportState θ) :
    (G.settingOf (GasFamily.single θ s)).bases = G.basesWithOffsets θ s.2.2 := by
  classical
  have hsingle : GasFamily.single θ s = (GasFamily.empty : GasFamily R n).insertClass θ s := rfl
  funext c
  show (match (GasFamily.single θ s).baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
    | Sum.inr o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o
    | Sum.inl _ => G.groundBases c) = _
  rw [hsingle, GasFamily.baseAt_insertClass coresDisjoint_empty (empty_occupies_false θ)]
  unfold GasGround.basesWithOffsets
  by_cases h : toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c ∈ θ.core
  · simp only [dif_pos h]
  · simp only [dif_neg h]
    have : (GasFamily.empty : GasFamily R n).baseAt
        (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) = Sum.inl () := by
      unfold GasFamily.baseAt
      rw [dif_neg]
      rintro ⟨θ', h1, -⟩
      simp [GasFamily.Occupies, GasFamily.empty] at h1
    rw [this]
def BaseCondition {F : BlockFrame} (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (y : F.Cell)
    (v : F.Site F.depth) : Prop :=
  ((nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y) → v = cellCentre F.depth y) ∧
    (¬ (nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y) → v ∈ sitesBelow F.depth y ∧
      ∀ B ∈ excludedBoxes J₀ h y, ∀ x ∈ B, ∀ i, x i ≠ v i)
theorem isBaseChoice_iff_baseCondition {F : BlockFrame} {J₀ : ℕ} {h : Finset (Finset (F.Site F.depth))}
    {b : F.Cell → F.Site F.depth} : IsBaseChoice J₀ h b ↔ ∀ y, BaseCondition J₀ h y (b y) := Iff.rfl
open Classical in
theorem mem_baseChoices_iff_baseCondition {W : (stepBlockFrame R.params.side n).GaugeField 0}
    {b : (stepBlockFrame R.params.side n).Cell → (stepBlockFrame R.params.side n).Site 0} :
    b ∈ baseChoices R.params W ↔ ∀ y, BaseCondition R.params.baseDepth
      (hotLumps R.params.grid R.params.threshold (levelSites (stepBlockFrame R.params.side n) 0) W) y (b y) := by
  unfold baseChoices
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact isBaseChoice_iff_baseCondition
theorem GasGround.basesWithOffsets_torusSiteInFrame (o : θ.core → BlockOffset R.params.side) {y : TorusSite n}
    (hy : y ∈ θ.core) :
    G.basesWithOffsets θ o (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) =
      frameBlockSite R.params.side n y (o ⟨y, hy⟩) := by
  classical
  have hc : toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) = y :=
    toTorusSite_torusSiteInFrame_one y R.params.side
  have key : ∀ (y' : TorusSite n) (_ : y' = y) (h' : y' ∈ θ.core),
      frameBlockSite R.params.side n y' (o ⟨y', h'⟩) = frameBlockSite R.params.side n y (o ⟨y, hy⟩) := by
    intro y' e h'
    subst e
    rfl
  unfold GasGround.basesWithOffsets
  rw [dif_pos (by rw [hc]; exact hy)]
  exact key _ hc _
open Classical in
theorem GasGround.sum_prod_baseUniformWeight_le_one (hne : θ.core.Nonempty) (W : TorusField (n * R.params.side)) :
    ∑ o : θ.core → BlockOffset R.params.side,
      ENNReal.ofReal (∏ y ∈ θ.core, baseUniformWeight W (G.basesWithOffsets θ o) y) ≤ 1 := by
  set Wf := readAtLevel (stepBlockFrame R.params.side n) 0 W with hWf
  set h := hotLumps R.params.grid R.params.threshold (levelSites (stepBlockFrame R.params.side n) 0) Wf with hh
  set cell : TorusSite n → (stepBlockFrame R.params.side n).Cell :=
    fun y => torusSiteInFrame (stepBlockFrame R.params.side n) 1 y with hcell
  set A : θ.core → Finset (BlockOffset R.params.side) := fun y =>
    Finset.univ.filter fun o => BaseCondition R.params.baseDepth h (cell y.1) (frameBlockSite R.params.side n y.1 o)
    with hA
  refine sum_le_one_of_le_prod_indicator_inv_card A _ fun o => ?_
  by_cases hb : G.basesWithOffsets θ o ∈ baseChoices R.params Wf
  · have hb' := mem_baseChoices_iff_baseCondition.mp hb
    have hcard : ∀ y : θ.core, (Finset.univ.filter fun o' : BlockOffset R.params.side =>
        Function.update (G.basesWithOffsets θ o) (cell y.1) (frameBlockSite R.params.side n y.1 o') ∈
          baseChoices R.params Wf) = A y := by
      intro y
      ext o'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hA]
      rw [mem_baseChoices_iff_baseCondition]
      constructor
      · intro hall
        have := hall (cell y.1)
        rwa [Function.update_self] at this
      · intro hok c
        by_cases hc : c = cell y.1
        · subst hc
          rwa [Function.update_self]
        · rw [Function.update_of_ne hc]
          exact hb' c
    have hmem : ∀ y : θ.core, o y ∈ A y := by
      intro y
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
      have := hb' (cell y.1)
      rwa [G.basesWithOffsets_torusSiteInFrame o y.2] at this
    have hshare : ∀ y : θ.core, baseUniformWeight W (G.basesWithOffsets θ o) y.1 = 1 / ((A y).card : ℝ) := by
      intro y
      unfold baseUniformWeight
      rw [if_pos hb]
      have := hcard y
      congr 3
    rw [← Finset.prod_coe_sort θ.core, ENNReal.ofReal_prod_of_nonneg (fun y _ => by
      rw [hshare y]
      positivity)]
    refine Finset.prod_le_prod' fun y _ => ?_
    rw [if_pos (hmem y), hshare y, one_div, ENNReal.ofReal_inv_of_pos
      (by exact_mod_cast Finset.card_pos.mpr ⟨_, hmem y⟩), ENNReal.ofReal_natCast]
  · obtain ⟨y₀, hy₀⟩ := hne
    have h0 : baseUniformWeight W (G.basesWithOffsets θ o) y₀ = 0 := by
      unfold baseUniformWeight
      rw [if_neg hb]
    rw [Finset.prod_eq_zero hy₀ h0]
    simp
end BaseChoices
section Marks
variable {R : StepSetup} {n : ℕ} [NeZero n] (G : GasGround R n) {θ : GasSupport R n}
theorem GasGround.supportMarks_mem_unitInterval (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn)
    (W : TorusField (n * R.params.side)) :
    0 ≤ G.supportMarks θ W ∧ G.supportMarks θ W ≤ 1 := by apply _root_.YangMills.Construction.StepGas.GasGround.supportMarks_nonneg_and_le_one <;> assumption
omit [NeZero n] in
theorem frameField_apply_of_notMem_free {free : Finset (TorusBond (n * R.params.side))} {V : TorusField n}
    {B : TorusField (n * R.params.side)} {b : TorusBond (n * R.params.side)} (h : b ∉ free) :
    StepSettings.frameField R free V B b.1 b.2 = B b.1 b.2 := by apply _root_.YangMills.Construction.StepGas.frameField_of_notMem <;> assumption
theorem GasGround.baseWithClass_apply_of_mem {γ : GasFamily R n} {a : θ.coreBonds → UnitQuaternion}
    {b : TorusBond (n * R.params.side)} (h : b ∈ θ.coreBonds) : G.baseWithClass γ θ a b.1 b.2 = a ⟨b, h⟩ := by apply _root_.YangMills.Construction.StepGas.GasGround.baseWithClass_of_mem <;> assumption
theorem GasGround.notMem_freeBondsWithSupport {γ : GasFamily R n} {b : TorusBond (n * R.params.side)}
    (h : b ∈ θ.coreBonds) : b ∉ G.freeBondsWithSupport γ θ := by
  classical
  intro hb
  exact (Finset.mem_filter.mp hb).2 h
theorem GasGround.singleSupportField_apply_of_mem {a : θ.coreBonds → UnitQuaternion}
    {b : TorusBond (n * R.params.side)} (h : b ∈ θ.coreBonds) : G.singleSupportField θ a b.1 b.2 = a ⟨b, h⟩ := by
  unfold GasGround.singleSupportField
  rw [frameField_apply_of_notMem_free (G.notMem_freeBondsWithSupport h), G.baseWithClass_apply_of_mem h]
theorem GasGround.fieldWithSupport_apply_of_mem {γ : GasFamily R n} {a : θ.coreBonds → UnitQuaternion}
    {b : TorusBond (n * R.params.side)} (h : b ∈ θ.coreBonds) : G.fieldWithSupport γ θ a b.1 b.2 = a ⟨b, h⟩ := by
  unfold GasGround.fieldWithSupport
  rw [frameField_apply_of_notMem_free (G.notMem_freeBondsWithSupport h),
    frameField_apply_of_notMem_free (G.notMem_freeBondsWithSupport h), G.baseWithClass_apply_of_mem h]
theorem GasSupport.mem_coreBonds_of_parentBlocks {b : TorusBond (n * R.params.side)}
    (h1 : parentBlock R.params.side b.1 ∈ θ.core)
    (h2 : parentBlock R.params.side (b.1 + TorusFields.unitStep (n * R.params.side) b.2) ∈ θ.core) :
    b ∈ θ.coreBonds := by apply _root_.YangMills.Construction.StepGas.GasSupport.mem_coreBonds_of_ends <;> assumption
theorem GasSupport.mem_coreBonds_of_mem_bad {b : TorusBond (n * R.params.side)} (hb : b ∈ θ.1) (hr : 1 ≤ R.range) :
    b ∈ θ.coreBonds := by apply _root_.YangMills.Construction.GasStep.mem_coreBonds_of_mem <;> assumption
end Marks
section Measurability
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem measurable_baseUniformWeight_apply (hK : BondKernelBorel) (b : BaseChoice R.params.side n) (y : TorusSite n) :
    Measurable fun W : TorusField (n * R.params.side) => baseUniformWeight W b y := by apply _root_.YangMills.Construction.StepGas.ActivityMeasurable.measurable_baseUniformWeight <;> assumption
theorem GasGround.measurable_supportPrice (hfit : R.params.Admissible) (G : GasGround R n) (γ : GasFamily R n)
    (θ : GasSupport R n) : Measurable (G.supportPrice γ θ) := by
  classical
  have hL : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
  have hF : Measurable fun W : TorusField (n * R.params.side) =>
      R.coupling * R.params.κ * R.params.threshold ^ 2 * ((hotLumpsWithin R.params W θ.2).card : ℝ) +
        R.params.κ₁ * R.coupling * R.params.threshold ^ 2 * (excessLength R.params R.range θ.2 W : ℝ) := by
    refine measurable_of_eqOn_torusHotLumps_fibres hfit hL fun W₀ => ⟨fun _ =>
      R.coupling * R.params.κ * R.params.threshold ^ 2 * ((hotLumpsWithin R.params W₀ θ.2).card : ℝ) +
        R.params.κ₁ * R.coupling * R.params.threshold ^ 2 * (excessLength R.params R.range θ.2 W₀ : ℝ),
      measurable_const, fun W h => ?_⟩
    unfold hotLumpsWithin excessLength
    rw [h]
  exact hF.comp (G.continuous_fieldWithSupport γ θ).measurable
theorem coordNorm_zero_eq : coordNorm 0 = 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.coordNorm_zero <;> assumption
end Measurability
section Bounds
variable {R : StepSetup} {n : ℕ} [NeZero n]
section SingleSupport
variable (G : GasGround R n) {γ : GasFamily R n} {θ : GasSupport R n} (s : SupportState θ)
theorem GasGround.clusterFactor_settingOf_insertClass_eq (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False)
    (X : Finset (TorusSite (n * R.params.side))) :
    R.clusterFactor (n * R.params.side) ((G.settingOf (γ.insertClass θ s)).field 0)
        (G.settingOf (γ.insertClass θ s)).support (G.settingOf (γ.insertClass θ s)).labelling X =
      R.clusterFactor (n * R.params.side) (G.fieldWithSupport γ θ s.1) (G.sitesWithSupport γ θ)
        (G.labellingWithSupport γ θ s.2.1) X := by
  rw [G.settingOf_insertClass_field_zero s hs hc]
  exact dependent_congr_finset (fun Y ω => R.clusterFactor (n * R.params.side) (G.fieldWithSupport γ θ s.1) Y ω X)
    (G.settingOf_insertClass_support s) _ _ (G.settingOf_insertClass_labelling_apply s hs hc)
theorem GasGround.siteDensity_settingOf_insertClass_eq (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False)
    (y : TorusSite (n * R.params.side)) :
    R.siteDensity (n * R.params.side) y ((G.settingOf (γ.insertClass θ s)).field 0)
        (G.settingOf (γ.insertClass θ s)).support (G.settingOf (γ.insertClass θ s)).labelling =
      R.siteDensity (n * R.params.side) y (G.fieldWithSupport γ θ s.1) (G.sitesWithSupport γ θ)
        (G.labellingWithSupport γ θ s.2.1) := by
  rw [G.settingOf_insertClass_field_zero s hs hc]
  exact dependent_congr_finset (fun Y ω => R.siteDensity (n * R.params.side) y (G.fieldWithSupport γ θ s.1) Y ω)
    (G.settingOf_insertClass_support s) _ _ (G.settingOf_insertClass_labelling_apply s hs hc)
theorem GasGround.labelsHullCondition_of_isAdmissible (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False) (hρ : 0 < R.ballRadius)
    (hset : (G.settingOf (γ.insertClass θ s)).IsAdmissible) : G.LabelsHullCondition γ θ s.1 s.2.1 := by
  have hzero : (G.settingOf (γ.insertClass θ s)).InBalls 0 := fun b => by
    show coordNorm 0 ≤ R.ballRadius
    rw [coordNorm_zero_eq]
    exact hρ.le
  refine ⟨?_, fun X hX => ?_⟩
  · have := hset.isHull 0 hzero
    rwa [G.settingOf_insertClass_field_zero s hs hc, G.settingOf_insertClass_support s] at this
  · rw [← G.clusterFactor_settingOf_insertClass_eq s hs hc]
    exact hset.factor_ne_zero 0 hzero X (by rw [G.settingOf_insertClass_support s]; exact hX)
theorem GasGround.mem_sitesWithSupport (γ' : GasFamily R n) {z : TorusSite (n * R.params.side)} (hz : z ∈ θ.2) :
    z ∈ G.sitesWithSupport γ' θ := by apply _root_.YangMills.Construction.StepGas.GasGround.mem_sitesInsert <;> assumption
theorem GasGround.clusterFactor_single_eq_withSupport (hrow : R.HasExpansions)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    {X : Finset (TorusSite (n * R.params.side))} (hX : X ∈ chainComponents R.range θ.2) :
    R.clusterFactor (n * R.params.side) (G.singleSupportField θ s.1) (G.sitesWithSupport GasFamily.empty θ)
        (G.labellingWithSupport GasFamily.empty θ s.2.1) X =
      R.clusterFactor (n * R.params.side) (G.fieldWithSupport γ θ s.1) (G.sitesWithSupport γ θ)
        (G.labellingWithSupport γ θ s.2.1) X := by
  classical
  have hsub : X ⊆ θ.2 := subset_of_mem_chainComponents hX
  refine hrow.2.reads_class (n * R.params.side) hside _ _ _ _ _ _ X
    (fun z hz => G.mem_sitesWithSupport _ (hsub hz))
    (fun z hz => G.mem_sitesWithSupport _ (hsub hz)) (fun b h1 h2 => ?_) (fun z hz hz' hzX => ?_)
  · have hbs : b ∈ θ.coreBonds := GasSupport.mem_coreBonds_of_parentBlocks
      (GasSupport.parentBlock_mem_core_of_mem_sites (hsub h1)) (GasSupport.parentBlock_mem_core_of_mem_sites (hsub h2))
    rw [G.singleSupportField_apply_of_mem hbs, G.fieldWithSupport_apply_of_mem hbs]
  · have hzθ := hsub hzX
    unfold GasGround.labellingWithSupport
    simp only [dif_pos hzθ]
theorem GasGround.activity_eq_marks_mul (hrow : R.HasExpansions)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) :
    G.activity θ s = G.supportMarks θ (G.singleSupportField θ s.1) *
      (∏ X ∈ chainComponents R.range θ.2, R.clusterFactor (n * R.params.side) (G.fieldWithSupport γ θ s.1)
        (G.sitesWithSupport γ θ) (G.labellingWithSupport γ θ s.2.1) X) *
      ∏ y ∈ θ.core, baseUniformWeight (G.singleSupportField θ s.1) (G.basesWithOffsets θ s.2.2) y := by
  have e0 : ∀ X ∈ chainComponents R.range θ.2,
      R.clusterFactor (n * R.params.side) (G.frameField (GasFamily.single θ s))
        (G.settingOf (GasFamily.single θ s)).support (G.settingOf (GasFamily.single θ s)).labelling X =
      R.clusterFactor (n * R.params.side) (G.fieldWithSupport γ θ s.1) (G.sitesWithSupport γ θ)
        (G.labellingWithSupport γ θ s.2.1) X := by
    intro X hX
    rw [← G.clusterFactor_single_eq_withSupport s hrow hside hX, G.frameField_single_eq s]
    exact dependent_congr_finset
      (fun Y ω => R.clusterFactor (n * R.params.side) (G.singleSupportField θ s.1) Y ω X)
      (G.settingOf_insertClass_support s) _ _
      (G.settingOf_insertClass_labelling_apply s coresDisjoint_empty (empty_occupies_false θ))
  unfold GasGround.activity
  rw [Finset.prod_congr rfl e0, G.frameField_single_eq s, G.settingOf_single_bases s]
theorem GasGround.exp_classExponent_insertClass (ch : ℝ) (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False) :
    Real.exp ((G.settingOf (γ.insertClass θ s)).classExponent ch θ) =
      Real.exp (∑ y ∈ sitesNear R.range θ.2,
          R.siteDensity (n * R.params.side) y (G.fieldWithSupport γ θ s.1) (G.sitesWithSupport γ θ)
            (G.labellingWithSupport γ θ s.2.1)) *
        Real.exp (G.supportPrice γ θ s.1) * clusterWeight R.params.side ch R.coupling R.range θ := by
  have h1 : (G.settingOf (γ.insertClass θ s)).densityNear θ.2 = ∑ y ∈ sitesNear R.range θ.2,
      R.siteDensity (n * R.params.side) y (G.fieldWithSupport γ θ s.1) (G.sitesWithSupport γ θ)
        (G.labellingWithSupport γ θ s.2.1) :=
    Finset.sum_congr rfl fun y _ => G.siteDensity_settingOf_insertClass_eq s hs hc y
  unfold ChartSetting.classExponent clusterWeight
  rw [h1, G.settingOf_insertClass_field_zero s hs hc, ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold GasGround.supportPrice
  ring
theorem ofReal_mul_le_of_marks_le_one {M F Bp z Es Ep w : ℝ} {mass m₀ J : ℝ≥0∞} (hM : M ≤ 1) (hF : 0 ≤ F)
    (hB : 0 ≤ Bp) (hEs : 0 < Es) (hEp : 0 < Ep) (hw : ENNReal.ofReal w ≤ mass)
    (hm : mass ≤ ENNReal.ofReal (Es * Ep * z) * m₀) (hJ : J = ENNReal.ofReal (F * Es)) :
    ENNReal.ofReal (M * F * Bp) * ENNReal.ofReal w ≤
      (ENNReal.ofReal z * m₀) * (ENNReal.ofReal Bp * J * ENNReal.ofReal Ep) := by
  exact _root_.YangMills.Construction.StepGas.state_bound_arith hM hF hB hEs hEp hw hm hJ
theorem GasGround.activity_mul_le_of_isAdmissible (hrow : R.HasExpansions)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) (hρ : 0 < R.ballRadius)
    (hp : IsCutoff R.ballRadius R.barrierFn) (hr : 1 ≤ R.range) (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False)
    (hfar : ∀ a ∈ θ.2, ∀ b ∈ G.recordedSites ∪ γ.sites, R.range < supDist a b)
    (hmk : θ.1 ⊆ markedBonds R G.cut) (ch w : ℝ) (m₀ : ℝ≥0∞)
    (hset : (G.settingOf (γ.insertClass θ s)).IsAdmissible)
    (hw : ENNReal.ofReal w ≤ settingMass (G.settingOf (γ.insertClass θ s)))
    (hstar : (∀ b ∈ θ.1, 1 - bondMark R G.coarse (G.frameField (GasFamily.single θ s)) b ≠ 0) →
      settingMass (G.settingOf (γ.insertClass θ s)) ≤
        ENNReal.ofReal (Real.exp ((G.settingOf (γ.insertClass θ s)).classExponent ch θ)) * m₀) :
    ENNReal.ofReal (G.activity θ s) * ENNReal.ofReal w ≤
      (ENNReal.ofReal (clusterWeight R.params.side ch R.coupling R.range θ) * m₀) *
        (ENNReal.ofReal (∏ y ∈ θ.core, baseUniformWeight (G.singleSupportField θ s.1) (G.basesWithOffsets θ s.2.2) y) *
          G.labelIntegrandWithSupport γ θ s.1 s.2.1 * ENNReal.ofReal (Real.exp (G.supportPrice γ θ s.1))) := by
  classical
  by_cases hd : G.activity θ s = 0
  · simp [hd]
  have hok := G.labelsHullCondition_of_isAdmissible s hs hc hρ hset
  have hfac := G.activity_eq_marks_mul (γ := γ) s hrow hside
  have hmarks := G.supportMarks_mem_unitInterval (θ := θ) hρ hp (G.singleSupportField θ s.1)
  have hbad : ∀ b ∈ θ.1, 1 - bondMark R G.coarse (G.frameField (GasFamily.single θ s)) b ≠ 0 := by
    intro b hb
    have hm0 : G.supportMarks θ (G.singleSupportField θ s.1) ≠ 0 := fun h0 => hd (by rw [hfac, h0]; ring)
    have hbs : b ∈ θ.coreBonds ∩ markedBonds R G.cut :=
      Finset.mem_inter.mpr ⟨GasSupport.mem_coreBonds_of_mem_bad hb hr, hmk hb⟩
    have := (Finset.prod_ne_zero_iff.mp hm0) b hbs
    rw [if_pos hb] at this
    rwa [G.frameField_single_eq s]
  have hF0 : 0 ≤ ∏ X ∈ chainComponents R.range θ.2,
      R.clusterFactor (n * R.params.side) (G.fieldWithSupport γ θ s.1) (G.sitesWithSupport γ θ)
        (G.labellingWithSupport γ θ s.2.1) X :=
    Finset.prod_nonneg fun X hX =>
      hrow.2.factor_nonneg (n * R.params.side) hside _ _ _ X
  have hBp0 : 0 ≤ ∏ y ∈ θ.core, baseUniformWeight (G.singleSupportField θ s.1) (G.basesWithOffsets θ s.2.2) y :=
    Finset.prod_nonneg fun y _ => by
      unfold baseUniformWeight
      split_ifs <;> positivity
  have hm := hstar hbad
  rw [G.exp_classExponent_insertClass s ch hs hc] at hm
  rw [hfac]
  refine ofReal_mul_le_of_marks_le_one hmarks.2 hF0 hBp0 (Real.exp_pos _) (Real.exp_pos _) hw hm ?_
  unfold GasGround.labelIntegrandWithSupport
  rw [if_pos hok]
  rfl
end SingleSupport
theorem GasGround.activity_mul_weight_update_le (G : GasGround R n) (σ : G.Config) (i : G.GasSpin) (ch : ℝ)
    (v : G.SpinState i) (hrow : R.HasExpansions) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn) (hr : 1 ≤ R.range)
    (hs : (G.familyOf σ).CoresDisjoint)
    (hc : ∀ θ', (G.familyOf σ).Occupies θ' → ∀ y, y ∈ i.1.core → y ∈ θ'.core → False)
    (hfar : ∀ a ∈ i.1.2, ∀ b ∈ G.recordedSites ∪ (G.familyOf σ).sites, R.range < supDist a b)
    (hcfg : ∀ σ' : G.Config, G.pairConstraint.IsAdmissible σ' → (G.settingOf (G.familyOf σ')).IsAdmissible)
    (hstar : (G.settingOf ((G.familyOf σ).insertClass i.1 v.1)).IsAdmissible →
      (∀ b ∈ i.1.1, 1 - bondMark R G.coarse (G.frameField (GasFamily.single i.1 v.1)) b ≠ 0) →
      settingMass (G.settingOf ((G.familyOf σ).insertClass i.1 v.1)) ≤
        ENNReal.ofReal (Real.exp ((G.settingOf ((G.familyOf σ).insertClass i.1 v.1)).classExponent ch i.1)) *
          settingMass (G.settingOf (G.familyOf σ))) :
    ENNReal.ofReal (G.activity i.1 v.1) * ENNReal.ofReal (G.weight (Function.update σ i (Sum.inr v))) ≤
      (ENNReal.ofReal (clusterWeight R.params.side ch R.coupling R.range i.1) *
          settingMass (G.settingOf (G.familyOf σ))) *
        (ENNReal.ofReal (∏ y ∈ i.1.core,
            baseUniformWeight (G.singleSupportField i.1 v.1.1) (G.basesWithOffsets i.1 v.1.2.2) y) *
          G.labelIntegrandWithSupport (G.familyOf σ) i.1 v.1.1 v.1.2.1 *
          ENNReal.ofReal (Real.exp (G.supportPrice (G.familyOf σ) i.1 v.1.1))) := by
  classical
  by_cases hadm' : G.pairConstraint.IsAdmissible (Function.update σ i (Sum.inr v))
  swap
  · have hw : G.weight (Function.update σ i (Sum.inr v)) = 0 := by
      unfold GasGround.weight
      rw [if_neg hadm']
    simp [hw]
  have hset : (G.settingOf ((G.familyOf σ).insertClass i.1 v.1)).IsAdmissible := by
    have := hcfg _ hadm'
    rwa [G.familyOf_update σ i v] at this
  have hw : ENNReal.ofReal (G.weight (Function.update σ i (Sum.inr v))) ≤
      settingMass (G.settingOf ((G.familyOf σ).insertClass i.1 v.1)) := by
    unfold GasGround.weight
    rw [if_pos hadm', G.familyOf_update σ i v]
    exact ENNReal.ofReal_toReal_le
  have hmk : i.1.1 ⊆ markedBonds R G.cut := fun b hb => (Finset.mem_filter.mp (i.2.bad_subset_free hb)).1
  exact G.activity_mul_le_of_isAdmissible v.1 hrow hside hρ hp hr hs hc hfar hmk ch _ _ hset hw (hstar hset)
end Bounds
section Scored
variable {R : StepSetup} {n : ℕ} [NeZero n] (G : GasGround R n) (γ : GasFamily R n) (θ : GasSupport R n)
def GasGround.scoredLabelIntegrand (s : R.labels.Ω → ℝ) (a : θ.coreBonds → UnitQuaternion) (ν : θ.2 → R.labels.Ω) :
    ℝ≥0∞ :=
  G.labelIntegrandWithSupport γ θ a ν * ENNReal.ofReal (Real.exp (∑ z : θ.2, s (ν z)))
variable {γ θ}
theorem sum_finset_subtype_cast {T Ω : Type} {U U' : Finset T} (h : U = U') (s : Ω → ℝ) (ν : U' → Ω) :
    ∑ y : U, s (ν ⟨y.1, h ▸ y.2⟩) = ∑ y : U', s (ν y) := by
  subst h
  rfl
theorem GasGround.ofReal_exp_supportPrice_mul_scored_le_one {s : R.labels.Ω → ℝ}
    (hsc : WeightedResponses.PriceBoundsScore R.params R.coupling R.labels R.clusterFactor R.siteDensity s)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hfar : ∀ a ∈ θ.2, ∀ b ∈ G.recordedSites ∪ γ.sites, R.range < supDist a b) (a : θ.coreBonds → UnitQuaternion) :
    ENNReal.ofReal (Real.exp (G.supportPrice γ θ a)) *
      ∫⁻ ν, G.scoredLabelIntegrand γ θ s a ν ∂(Measure.pi fun _ : θ.2 => R.labels.μ) ≤ 1 := by
  classical
  by_cases hex : ∃ ν₀, G.LabelsHullCondition γ θ a ν₀
  · obtain ⟨ν₀, hhull, hΦ⟩ := hex
    set P := chainComponents R.range θ.2 with hPdef
    have hP : P.biUnion id = θ.2 := biUnion_chainComponents
    have hY : G.sitesWithSupport γ θ = θ.2 ∪ (G.recordedSites ∪ γ.sites) := by
      ext z
      simp only [GasGround.sitesWithSupport, Finset.mem_union]
      tauto
    have hPsub : P ⊆ chainComponents R.range (G.sitesWithSupport γ θ) := by
      intro X hX
      rw [hY]
      exact mem_chainComponents_union_of_separated hfar hX
    have key := hsc.price (n * R.params.side) hside (G.fieldWithSupport γ θ a) (G.sitesWithSupport γ θ)
      (G.labellingWithSupport γ θ ν₀) P hhull hPsub (fun X hX => hΦ X (Finset.mem_sdiff.mp hX).1)
    rw [lintegral_pi_finset_cast R.labels.μ hP] at key
    have hle : ∫⁻ ν, G.scoredLabelIntegrand γ θ s a ν ∂(Measure.pi fun _ : θ.2 => R.labels.μ) ≤
        ENNReal.ofReal (Real.exp (-G.supportPrice γ θ a)) := by
      refine le_trans (lintegral_mono fun ν => ?_) (le_trans key (le_of_eq ?_))
      · have hg : glueLabel (G.sitesWithSupport γ θ) (P.biUnion id) (G.labellingWithSupport γ θ ν₀)
            (fun z => ν ⟨z.1, hP ▸ z.2⟩) = G.labellingWithSupport γ θ ν := by
          funext z
          unfold glueLabel GasGround.labellingWithSupport
          by_cases hz : z.1 ∈ θ.2
          · have hz' : z.1 ∈ P.biUnion id := hP ▸ hz
            simp only [dif_pos hz, dif_pos hz']
          · have hz' : z.1 ∉ P.biUnion id := fun h => hz (hP ▸ h)
            simp only [dif_neg hz, dif_neg hz']
        show G.scoredLabelIntegrand γ θ s a ν ≤ _
        rw [hg]
        unfold GasGround.scoredLabelIntegrand GasGround.labelIntegrandWithSupport
        split_ifs with h1 h2
        · obtain ⟨X, hX, h0⟩ := h2
          exact absurd h0 (h1.2 X (hPsub hX))
        · have hset : (Finset.univ.filter fun y : TorusSite (n * R.params.side) =>
              ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange R.coupling : ℝ) / 4) =
                sitesNear R.range θ.2 := by
            rw [hP]
            rfl
          rw [hset, sum_finset_subtype_cast hP s ν, ← ENNReal.ofReal_mul' (Real.exp_pos _).le]
          rfl
        · simp
        · simp
      · congr 2
        unfold GasGround.supportPrice hotLumpsWithin
        rw [hP]
        have hrr : clusterRange R.coupling = R.range := rfl
        rw [hrr]
        ring
    calc ENNReal.ofReal (Real.exp (G.supportPrice γ θ a)) *
          ∫⁻ ν, G.scoredLabelIntegrand γ θ s a ν ∂(Measure.pi fun _ : θ.2 => R.labels.μ)
        ≤ ENNReal.ofReal (Real.exp (G.supportPrice γ θ a)) *
            ENNReal.ofReal (Real.exp (-G.supportPrice γ θ a)) := by
          gcongr
      _ = 1 := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          simp
  · have h0 : ∀ ν, G.scoredLabelIntegrand γ θ s a ν = 0 := fun ν => by
      unfold GasGround.scoredLabelIntegrand GasGround.labelIntegrandWithSupport
      rw [if_neg fun h => hex ⟨ν, h⟩, zero_mul]
    simp [h0]
theorem GasGround.measurable_scoredLabelIntegrand (hfit : R.params.Admissible) (hrow : R.HasExpansions)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) {s : R.labels.Ω → ℝ} (hs : Measurable s) :
    Measurable fun p : (θ.coreBonds → UnitQuaternion) × (θ.2 → R.labels.Ω) => G.scoredLabelIntegrand γ θ s p.1 p.2 := by
  unfold GasGround.scoredLabelIntegrand
  refine (G.measurable_labelIntegrandWithSupport hfit hrow hside).mul (ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp (Finset.measurable_sum _ fun z _ => hs.comp ?_)))
  exact (measurable_pi_apply z).comp measurable_snd
end Scored
end StepGas
namespace ResponseInTheExpansion
open StepGas StepSettings StepCosts RenormalizationStepParameters StepFloors TorusFields TorusLumps Dobrushin WeightedResponses
  BlockAverages LumpContours ColdStepAtMirrorFrames
theorem clusterScoreIntegralBound_holds (hS : ClusterExpansionOfAStep.InsertClassMassBound) (hMass : SettingMassEqIntegral)
    (hFac : ActivityIsMeasurable) (hFl : EventuallyFloorConditions) (hK : BondKernelBorel)
    (hCfg : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) :
    clusterScoreIntegralBound := by
  classical
  obtain ⟨rtS, hrtS, hS⟩ := hS
  obtain ⟨rtM, hrtM, hM⟩ := hMass
  refine ⟨fun c => min (rtS c) (rtM c), fun c => lt_min (hrtS c) (hrtM c), fun T hT hrt K => ?_⟩
  obtain ⟨yS, hyS⟩ := hS T hT (hrt.trans (min_le_left _ _))
  obtain ⟨yM, hyM⟩ := hM T hT (hrt.trans (min_le_right _ _))
  obtain ⟨yC, hyC⟩ := hCfg T hT
  have hL0 : (0 : ℝ) < (T.side : ℝ) + 1 := by positivity
  obtain ⟨yF, hyF⟩ := hFl T hT ((T.side : ℝ) + 1) 1 hL0 one_pos
  refine ⟨max (max (max (max yS yC) yM) (max yF T.floorMin)) (200 * T.B),
    fun y hy R A _ hA n _ G hG i σ hadm0 => ?_⟩
  have hyA : max (max (max yS yC) yM) (max yF T.floorMin) ≤ y := le_trans (le_max_left _ _) hy
  have hyB : 200 * T.B ≤ y := le_trans (le_max_right _ _) hy
  have hy0 : max yS yC ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hyA
  have hy1 : yS ≤ y := le_trans (le_max_left _ _) hy0
  have hy5 : yC ≤ y := le_trans (le_max_right _ _) hy0
  have hy2 : yM ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hyA
  have hy3 : yF ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hyA
  have hy4 : T.floorMin ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hyA
  have hR := hA.onFamily
  have hxx : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hA.abs_sub_le).2
    have h2 := hR.le_coupling
    linarith
  have hfl := hyF R.coupling (hy3.trans hR.le_coupling)
  have hfit : R.params.Admissible := by
    rw [hR.params_eq]
    exact hT.fits y hy4
  have hrow : R.HasExpansions := hR.isStep.1
  have hLeq : R.params.side = T.side := by
    rw [hR.params_eq]
    rfl
  have hneq : R.params.n₀ = T.n₀ := by
    rw [hR.params_eq]
    rfl
  have hLr : R.params.side + 1 ≤ R.range := by
    have h6 := hfl.range_ge
    have : ((T.side + 1 : ℕ) : ℝ) ≤ (clusterRange R.coupling : ℝ) := by
      push_cast
      exact h6
    have h7 : T.side + 1 ≤ clusterRange R.coupling := by exact_mod_cast this
    rw [hLeq]
    exact h7
  have hρ : 0 < R.ballRadius := by
    unfold StepSetup.ballRadius
    have := hfit.σ_pos
    positivity
  have hp : IsCutoff R.ballRadius R.barrierFn := by
    have e : R.ballRadius = T.ballRadius := by
      unfold StepSetup.ballRadius ParameterAssignment.ballRadius
      rw [hR.params_eq]
      rfl
    rw [e, hR.barrierFn_eq]
    exact hT.cut
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne R.params.side)
  have hn : R.params.n₀ ≤ n := by
    rcases hG with h | h
    · exact h.n₀_le
    · have h2 := h.isBlockSide.2
      nlinarith
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by nlinarith⟩
  have hsc := hA.admissible.price
  have core : ∀ σ : G.Config, G.pairConstraint.IsAdmissible σ → σ i = Sum.inl () →
      (∀ j, σ j = Sum.inl () ∨ i.1.FarApart j.1) →
      ∫⁻ v : G.SpinState i, ENNReal.ofReal (Real.exp (spinScore A i (Sum.inr v))) *
          ENNReal.ofReal (G.weight (Function.update σ i (Sum.inr v))) ∂(G.spinStateMeasure i) ≤
        ENNReal.ofReal (clusterWeight R.params.side T.gasRate R.coupling R.range i.1) *
          ENNReal.ofReal (G.weight σ) := by
    intro σ hadm hσi hap
    have hset : (G.settingOf (G.familyOf σ)).IsAdmissible := hyC y hy5 R hR hxx n G hG σ hadm
    have hsep := G.coresDisjoint_familyOf hadm (by omega)
    have hc : ∀ θ', (G.familyOf σ).Occupies θ' → ∀ y, y ∈ i.1.core → y ∈ θ'.core → False := by
      intro θ' h y h1 h2
      obtain ⟨j, rfl, hj⟩ := G.exists_spin_of_occupies h
      rcases hap j with e | e
      · exact hj e
      · exact e.false_of_mem_cores (by omega) h1 h2
    have hfar : ∀ a ∈ i.1.2, ∀ b ∈ G.recordedSites ∪ (G.familyOf σ).sites, R.range < supDist a b := by
      intro a ha b hb
      have has : a ∈ i.1.sites := Finset.mem_union_right _ ha
      rcases Finset.mem_union.mp hb with hb | hb
      · have := i.2.far_from_anchor a has b (Finset.mem_union_right _ hb)
        omega
      · obtain ⟨θ', h, hz⟩ := GasFamily.exists_of_mem_sites hb
        obtain ⟨j, rfl, hj⟩ := G.exists_spin_of_occupies h
        rcases hap j with e | e
        · exact absurd e hj
        · have := e a has b (Finset.mem_union_right _ hz)
          omega
    obtain ⟨-, -, hmeq⟩ := hyM y hy2 R hR n (by omega) _ hset
    have hne : settingMass (G.settingOf (G.familyOf σ)) ≠ ⊤ := by
      rw [hmeq]
      exact ENNReal.ofReal_ne_top
    have hweight : ENNReal.ofReal (G.weight σ) = settingMass (G.settingOf (G.familyOf σ)) := by
      unfold GasGround.weight
      rw [if_pos hadm, ENNReal.ofReal_toReal hne]
    rw [hweight]
    set E := ENNReal.ofReal (clusterWeight R.params.side T.gasRate R.coupling R.range i.1) *
      settingMass (G.settingOf (G.familyOf σ)) with hE
    set Bs : (i.1.coreBonds → UnitQuaternion) → (i.1.core → BlockOffset R.params.side) → ℝ≥0∞ := fun a o =>
      ENNReal.ofReal (∏ y ∈ i.1.core, baseUniformWeight (G.singleSupportField i.1 a) (G.basesWithOffsets i.1 o) y)
      with hBs
    set Q : (i.1.coreBonds → UnitQuaternion) → ℝ≥0∞ := fun a =>
      ENNReal.ofReal (Real.exp (G.supportPrice (G.familyOf σ) i.1 a)) with hQ
    have hBm : ∀ o, Measurable fun a => Bs a o := fun o =>
      ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun y _ =>
        (measurable_baseUniformWeight_apply hK _ y).comp (G.continuous_singleSupportField i.1).measurable)
    have hQm : Measurable Q :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (GasGround.measurable_supportPrice hfit G _ _))
    have hJm := G.measurable_scoredLabelIntegrand (γ := G.familyOf σ) (θ := i.1) hfit hrow hside hsc.borel
    have hcore : i.1.core.Nonempty := by
      obtain ⟨z, hz⟩ := i.2.isCluster.1
      exact ⟨_, GasSupport.parentBlock_mem_core hz⟩
    have hH1 : ∫⁻ p : SupportState i.1,
        Bs p.1 p.2.2 * G.scoredLabelIntegrand (G.familyOf σ) i.1 A.score p.1 p.2.1 * Q p.1
        ∂(supportStateMeasure i.1) ≤ 1 :=
      lintegral_prod_three_le_one _ _ Bs (G.scoredLabelIntegrand (G.familyOf σ) i.1 A.score) Q hBm hJm hQm
        (fun a => G.sum_prod_baseUniformWeight_le_one hcore _)
        (fun a => G.ofReal_exp_supportPrice_mul_scored_le_one hsc hside hfar a)
    have hHm : Measurable fun p : SupportState i.1 =>
        Bs p.1 p.2.2 * G.scoredLabelIntegrand (G.familyOf σ) i.1 A.score p.1 p.2.1 * Q p.1 := by
      have hB2 : Measurable fun q : (i.1.coreBonds → UnitQuaternion) × (i.1.core → BlockOffset R.params.side) =>
          Bs q.1 q.2 :=
        measurable_from_prod_countable_left hBm
      exact ((hB2.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).mul
        (hJm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))).mul (hQm.comp measurable_fst)
    have hdm : Measurable fun v : G.SpinState i => ENNReal.ofReal (G.activity i.1 v.1) :=
      ENNReal.measurable_ofReal.comp (hFac R hfit hrow hp n G i hG)
    unfold GasGround.spinStateMeasure
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hdm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    calc ∫⁻ v, ((fun v : G.SpinState i => ENNReal.ofReal (G.activity i.1 v.1)) *
          fun v => ENNReal.ofReal (Real.exp (spinScore A i (Sum.inr v))) *
            ENNReal.ofReal (G.weight (Function.update σ i (Sum.inr v)))) v
          ∂((supportStateMeasure i.1).comap Subtype.val)
        ≤ ∫⁻ v : G.SpinState i, (fun p : SupportState i.1 =>
            E * (Bs p.1 p.2.2 * G.scoredLabelIntegrand (G.familyOf σ) i.1 A.score p.1 p.2.1 * Q p.1)) v.1
          ∂((supportStateMeasure i.1).comap Subtype.val) := by
          refine lintegral_mono fun v => ?_
          have hb := G.activity_mul_weight_update_le σ i T.gasRate v hrow hside hρ hp (by omega) hsep hc hfar
            (hyC y hy5 R hR hxx n G hG) fun h1 h2 => hyS y hy1 R hR n G σ i v.1 hG hadm hset hσi hap h1 h2
          show ENNReal.ofReal (G.activity i.1 v.1) *
              (ENNReal.ofReal (Real.exp (∑ z : i.1.2, A.score (v.1.2.1 z))) *
                ENNReal.ofReal (G.weight (Function.update σ i (Sum.inr v)))) ≤
            E * (Bs v.1.1 v.1.2.2 * (G.labelIntegrandWithSupport (G.familyOf σ) i.1 v.1.1 v.1.2.1 *
              ENNReal.ofReal (Real.exp (∑ z : i.1.2, A.score (v.1.2.1 z)))) * Q v.1.1)
          calc _ = (ENNReal.ofReal (G.activity i.1 v.1) *
                ENNReal.ofReal (G.weight (Function.update σ i (Sum.inr v)))) *
                ENNReal.ofReal (Real.exp (∑ z : i.1.2, A.score (v.1.2.1 z))) := by ring
            _ ≤ (E * (Bs v.1.1 v.1.2.2 * G.labelIntegrandWithSupport (G.familyOf σ) i.1 v.1.1 v.1.2.1 * Q v.1.1)) *
                ENNReal.ofReal (Real.exp (∑ z : i.1.2, A.score (v.1.2.1 z))) := by gcongr
            _ = _ := by ring
      _ ≤ ∫⁻ p : SupportState i.1,
            E * (Bs p.1 p.2.2 * G.scoredLabelIntegrand (G.familyOf σ) i.1 A.score p.1 p.2.1 * Q p.1)
          ∂(supportStateMeasure i.1) := lintegral_comap_subtype_val_le _ _ (hHm.const_mul E)
      _ = E * ∫⁻ p : SupportState i.1,
            Bs p.1 p.2.2 * G.scoredLabelIntegrand (G.familyOf σ) i.1 A.score p.1 p.2.1 * Q p.1
          ∂(supportStateMeasure i.1) := lintegral_const_mul _ hHm
      _ ≤ E * 1 := by gcongr
      _ = E := mul_one _
  set σ₀ : G.Config := Function.update σ i (Sum.inl ()) with hσ₀
  have habs : G.pairConstraint.vacant i = Sum.inl () := rfl
  have hadm : G.pairConstraint.IsAdmissible σ₀ := by
    intro j k hjk
    by_cases hj : j = i
    · subst hj
      exact Or.inl (by simp [hσ₀])
    · by_cases hk : k = i
      · subst hk
        exact Or.inr (Or.inl (by simp [hσ₀]))
      · simpa [hσ₀, Function.update_of_ne hj, Function.update_of_ne hk] using hadm0 j k hjk
  have hupd : ∀ v, Function.update σ i v = Function.update σ₀ i v := fun v => by
    simp [hσ₀]
  have hnot : ¬ i.1.Touches ∅ := by
    unfold GasSupport.Touches
    simp
  have href : G.referenceMeasure ∅ i = withNoneMeasure (G.spinStateMeasure i) := by
    unfold GasGround.referenceMeasure GasGround.referenceMeasureOff
    rw [if_neg hnot]
  have e1 : MeasurableEmbedding (Sum.inl : Unit → G.SpinValue i) :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩
  have e2 : MeasurableEmbedding (Sum.inr : G.SpinState i → G.SpinValue i) :=
    ⟨Sum.inr_injective, measurable_inr, fun _ hs => hs.inr_image⟩
  have hset : MeasurableSet ({Sum.inl ()} : Set (G.SpinValue i)) := by
    have : ({Sum.inl ()} : Set (G.SpinValue i)) = Sum.inl '' (Set.univ : Set Unit) := by
      ext v
      rcases v with u | v <;> simp
    rw [this]
    exact e1.measurableSet_image.mpr MeasurableSet.univ
  rw [habs, href, hupd (Sum.inl ())]
  unfold withNoneMeasure
  rw [Measure.restrict_add, lintegral_add_measure]
  have h1 : ∫⁻ v in {(Sum.inl () : G.SpinValue i)}ᶜ, ENNReal.ofReal (Real.exp (spinScore A i v)) *
      G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(Measure.map Sum.inl (Measure.dirac ())) =
        0 := by
    rw [← lintegral_indicator hset.compl, e1.lintegral_map, lintegral_dirac]
    simp
  have h2 : ∫⁻ v in {(Sum.inl () : G.SpinValue i)}ᶜ, ENNReal.ofReal (Real.exp (spinScore A i v)) *
      G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(Measure.map Sum.inr (G.spinStateMeasure i)) ≤
      ∫⁻ v : G.SpinState i, ENNReal.ofReal (Real.exp (spinScore A i (Sum.inr v))) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (Sum.inr v)) ∂(G.spinStateMeasure i) := by
    rw [← lintegral_indicator hset.compl, e2.lintegral_map]
    refine lintegral_mono fun v => ?_
    simp
  rw [h1, zero_add]
  refine h2.trans ?_
  have hd0 : G.pairConstraint.weightDensity G.weight σ₀ = ENNReal.ofReal (G.weight σ₀) := by
    unfold PairConstraint.weightDensity
    rw [if_pos hadm]
  have hσ₀i : Function.update σ₀ i (Sum.inl ()) = σ₀ := by
    simp [hσ₀]
  rw [hσ₀i, hd0]
  by_cases hcomp : ∀ j, σ₀ j = Sum.inl () ∨ i.1.FarApart j.1
  · refine le_trans (lintegral_mono fun v => ?_) (core σ₀ hadm (by simp [hσ₀]) hcomp)
    rw [hupd]
    gcongr
    unfold PairConstraint.weightDensity
    split_ifs
    · exact le_rfl
    · exact zero_le
  · push_neg at hcomp
    obtain ⟨j, hj1, hj2⟩ := hcomp
    have hji : j ≠ i := by
      rintro rfl
      exact hj1 (by simp [hσ₀])
    have h0 : ∀ v : G.SpinState i,
        G.pairConstraint.weightDensity G.weight (Function.update σ i (Sum.inr v)) = 0 := by
      intro v
      unfold PairConstraint.weightDensity
      rw [if_neg]
      intro hadm'
      have hij : i ≠ j := hji.symm
      rcases hadm' i j hij with e | e | e
      · simp at e
      · apply hj1
        rw [Function.update_of_ne hji] at e
        simpa [hσ₀, Function.update_of_ne hji] using e
      · exact hj2 e
    simp [h0]
end ResponseInTheExpansion
end YangMills.Construction
end
