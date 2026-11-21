import YangMills.Construction.ClusterExpansionOfAStep.ClassesBesideAFarSet
import YangMills.Construction.ClusterExpansionOfAStep.ConfigurationsOfTheGasAreSettings
import YangMills.Construction.ClusterExpansionOfAStep.FactorOfAClassIsBorelProof
import YangMills.Construction.ClusterExpansionOfAStep.SettingWithAClassProofForm
import YangMills.Construction.ClusterExpansionOfAStep.SizeOfAClass
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction.StepGas
open BlockAverages LumpContours ColdStepAtMirrorFrames StepSettings TorusLumps TorusFields RenormalizationStepParameters StepCosts
theorem lintegral_comap_subtypeVal_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (P : α → Prop)
    {g : α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ v : {a // P a}, g v.1 ∂(μ.comap (Subtype.val : {a // P a} → α)) ≤ ∫⁻ a, g a ∂μ := by
  classical
  by_cases h : Function.Injective (Subtype.val : {a // P a} → α) ∧
      ∀ s : Set {a // P a}, MeasurableSet s → NullMeasurableSet (Subtype.val '' s : Set α) μ
  · have hle : (μ.comap (Subtype.val : {a // P a} → α)).map Subtype.val ≤ μ := by
      refine Measure.le_iff.mpr fun B hB => ?_
      rw [Measure.map_apply measurable_subtype_coe hB, Measure.comap_apply₀ _ _ h.1 h.2
        (hB.preimage measurable_subtype_coe).nullMeasurableSet]
      exact measure_mono (Set.image_preimage_subset _ _)
    calc ∫⁻ v : {a // P a}, g v.1 ∂(μ.comap (Subtype.val : {a // P a} → α))
        = ∫⁻ a, g a ∂((μ.comap (Subtype.val : {a // P a} → α)).map Subtype.val) :=
          (lintegral_map hg measurable_subtype_coe).symm
      _ ≤ ∫⁻ a, g a ∂μ := lintegral_mono' hle le_rfl
  · rw [Measure.comap, dif_neg h]
    simp
theorem lintegral_prod_three_le {A N B : Type} [MeasurableSpace A] [MeasurableSpace N] [MeasurableSpace B]
    [Fintype B] [MeasurableSingletonClass B] (μA : Measure A) [IsProbabilityMeasure μA] (μN : Measure N)
    [SFinite μN] (w : A → B → ℝ≥0∞) (J : A → N → ℝ≥0∞) (Q : A → ℝ≥0∞) (hw : ∀ b, Measurable fun a => w a b)
    (hJ : Measurable fun p : A × N => J p.1 p.2) (hQ : Measurable Q) (hsum : ∀ a, ∑ b, w a b ≤ 1)
    (hint : ∀ a, Q a * ∫⁻ ν, J a ν ∂μN ≤ 1) :
    ∫⁻ p : A × N × B, w p.1 p.2.2 * J p.1 p.2.1 * Q p.1 ∂(μA.prod (μN.prod Measure.count)) ≤ 1 := by
  have hw2 : Measurable fun q : A × B => w q.1 q.2 := measurable_from_prod_countable_left hw
  have hm : Measurable fun p : A × N × B => w p.1 p.2.2 * J p.1 p.2.1 * Q p.1 :=
    ((hw2.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).mul
      (hJ.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))).mul (hQ.comp measurable_fst)
  rw [lintegral_prod _ hm.aemeasurable]
  have hin : ∀ a, ∫⁻ q : N × B, w a q.2 * J a q.1 * Q a ∂(μN.prod Measure.count) ≤ 1 := by
    intro a
    have hma : Measurable fun q : N × B => w a q.2 * J a q.1 * Q a :=
      hm.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod _ hma.aemeasurable]
    have hq : ∀ ν, ∫⁻ b, w a b * J a ν * Q a ∂Measure.count ≤ J a ν * Q a := by
      intro ν
      rw [lintegral_count, tsum_fintype, ← Finset.sum_mul, ← Finset.sum_mul]
      calc (∑ b, w a b) * J a ν * Q a ≤ 1 * J a ν * Q a := by gcongr; exact hsum a
        _ = J a ν * Q a := by rw [one_mul]
    calc ∫⁻ ν, ∫⁻ b, w a b * J a ν * Q a ∂Measure.count ∂μN
        ≤ ∫⁻ ν, J a ν * Q a ∂μN := lintegral_mono hq
      _ = Q a * ∫⁻ ν, J a ν ∂μN := by
          simp_rw [mul_comm (J a _) (Q a)]
          exact lintegral_const_mul _ (hJ.comp (measurable_const.prodMk measurable_id))
      _ ≤ 1 := hint a
  calc ∫⁻ a, ∫⁻ q : N × B, w a q.2 * J a q.1 * Q a ∂(μN.prod Measure.count) ∂μA
      ≤ ∫⁻ _a, 1 ∂μA := lintegral_mono hin
    _ = 1 := by simp
theorem sum_le_one_of_le_prod_uniform {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : I → Finset O) (f : (I → O) → ℝ≥0∞)
    (hf : ∀ o, f o ≤ ∏ i, (if o i ∈ A i then ((A i).card : ℝ≥0∞)⁻¹ else 0)) : ∑ o, f o ≤ 1 := by
  calc ∑ o, f o ≤ ∑ o, ∏ i, (if o i ∈ A i then ((A i).card : ℝ≥0∞)⁻¹ else 0) :=
        Finset.sum_le_sum fun o _ => hf o
    _ = ∏ i, ∑ a, (if a ∈ A i then ((A i).card : ℝ≥0∞)⁻¹ else 0) := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ ≤ 1 := by
        refine Finset.prod_le_one' fun i _ => ?_
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        exact ENNReal.mul_inv_le_one _
section Insertion
variable {R : StepSetup} {n : ℕ} [NeZero n] (G : GasGround R n) (γ : GasFamily R n) (θ : GasSupport R n)
open Classical in
def GasGround.freeInsert : Finset (TorusBond (n * R.params.side)) :=
  (G.settingWithFamily γ).free.filter fun b => b ∉ θ.coreBonds
def GasGround.fieldInsert (a : θ.coreBonds → UnitQuaternion) : TorusField (n * R.params.side) :=
  StepSettings.frameField R (G.freeInsert γ θ) G.coarse
    (StepSettings.frameField R (G.freeInsert γ θ) G.coarse (G.baseWithClass γ θ a))
theorem GasGround.continuous_fieldInsert : Continuous (G.fieldInsert γ θ) :=
  (continuous_frameField _ _).comp ((continuous_frameField _ _).comp (continuous_baseWithClass G))
def GasGround.sitesInsert : Finset (TorusSite (n * R.params.side)) := G.recordedSites ∪ (γ.sites ∪ θ.2)
theorem GasGround.mem_support_of_mem_sitesInsert {z : TorusSite (n * R.params.side)}
    (hz : z ∈ G.sitesInsert γ θ) (h : z ∉ θ.2) : z ∈ (G.settingWithFamily γ).support := by
  show z ∈ G.recordedSites ∪ γ.sites
  simp only [GasGround.sitesInsert, Finset.mem_union] at hz ⊢
  tauto
open Classical in
def GasGround.labelsInsert (ν : θ.2 → R.labels.Ω) (z : G.sitesInsert γ θ) : R.labels.Ω :=
  if h : z.1 ∈ θ.2 then ν ⟨z.1, h⟩
  else (G.settingWithFamily γ).labelling ⟨z.1, G.mem_support_of_mem_sitesInsert γ θ z.2 h⟩
theorem GasGround.measurable_labelsInsert : Measurable (G.labelsInsert γ θ) := by
  classical
  refine measurable_pi_iff.mpr fun z => ?_
  unfold GasGround.labelsInsert
  by_cases h : z.1 ∈ θ.2
  · simp only [dif_pos h]
    exact measurable_pi_apply _
  · simp only [dif_neg h]
    exact measurable_const
variable {γ θ}
variable (s : SupportState θ)
theorem GasGround.field_zero_settingOf_insertClass (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False) :
    (G.settingOf (γ.insertClass θ s)).field 0 = G.fieldInsert γ θ s.1 := by
  rw [G.field_zero_insertClass s hs hc, G.settingWithFamily_free_insertClass s hs hc]
  rfl
theorem GasGround.support_settingOf_insertClass :
    (G.settingOf (γ.insertClass θ s)).support = G.sitesInsert γ θ := by
  show G.recordedSites ∪ (γ.insertClass θ s).sites = _
  rw [GasFamily.sites_insertClass]
  rfl
theorem GasGround.labelling_settingOf_insertClass (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False)
    (z : TorusSite (n * R.params.side)) (hz : z ∈ (G.settingOf (γ.insertClass θ s)).support)
    (hz' : z ∈ G.sitesInsert γ θ) :
    (G.settingOf (γ.insertClass θ s)).labelling ⟨z, hz⟩ = G.labelsInsert γ θ s.2.1 ⟨z, hz'⟩ := by
  classical
  have hs' : (γ.insertClass θ s).CoresDisjoint := hs.insertClass hc
  have hself : (γ.insertClass θ s).Occupies θ := GasFamily.occupies_insertClass.mpr (Or.inl rfl)
  show (if h : z ∈ (γ.insertClass θ s).sites then (γ.insertClass θ s).labelAt h else
    G.recordedLabel ⟨z, (Finset.mem_union.mp hz).resolve_right h⟩) = _
  unfold GasGround.labelsInsert
  by_cases hθ : z ∈ θ.2
  · have hzs : z ∈ (γ.insertClass θ s).sites := by
      rw [GasFamily.sites_insertClass]
      exact Finset.mem_union_right _ hθ
    rw [dif_pos hzs, GasFamily.labelAt_eq_of_mem _ hs' hzs hself hθ, GasFamily.state_insertClass_self]
    simp only [dif_pos hθ]
  · simp only [dif_neg hθ]
    show _ = (if h : z ∈ γ.sites then γ.labelAt h else
      G.recordedLabel ⟨z, (Finset.mem_union.mp (G.mem_support_of_mem_sitesInsert γ θ hz' hθ)).resolve_right h⟩)
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
theorem dependent_congr {T Ω α : Type} (f : ∀ Y : Finset T, (Y → Ω) → α) {Y Y' : Finset T} (h : Y = Y')
    (ω : Y → Ω) (ω' : Y' → Ω) (hω : ∀ z (hz : z ∈ Y) (hz' : z ∈ Y'), ω ⟨z, hz⟩ = ω' ⟨z, hz'⟩) :
    f Y ω = f Y' ω' := by apply _root_.YangMills.Construction.StepGas.ActivityMeasurable.dependent_congr <;> assumption
theorem lintegral_pi_congr_finset {T Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {U U' : Finset T}
    (h : U = U') (f : (U → Ω) → ℝ≥0∞) :
    ∫⁻ ν, f ν ∂(Measure.pi fun _ : U => μ) =
      ∫⁻ ν', f (fun z => ν' ⟨z.1, h ▸ z.2⟩) ∂(Measure.pi fun _ : U' => μ) := by
  subst h
  rfl
end Insertion
section LabelIntegral
variable {R : StepSetup} {n : ℕ} [NeZero n] (G : GasGround R n) (γ : GasFamily R n) (θ : GasSupport R n)
def GasGround.LabelsAdmissible (a : θ.coreBonds → UnitQuaternion) (ν : θ.2 → R.labels.Ω) : Prop :=
  IsHullState R.params R.range (G.fieldInsert γ θ a) (G.sitesInsert γ θ) ∧
    ∀ X ∈ chainComponents R.range (G.sitesInsert γ θ),
      R.clusterFactor (n * R.params.side) (G.fieldInsert γ θ a) (G.sitesInsert γ θ) (G.labelsInsert γ θ ν) X ≠ 0
def GasGround.labelValue (a : θ.coreBonds → UnitQuaternion) (ν : θ.2 → R.labels.Ω) : ℝ :=
  (∏ X ∈ chainComponents R.range θ.2,
      R.clusterFactor (n * R.params.side) (G.fieldInsert γ θ a) (G.sitesInsert γ θ) (G.labelsInsert γ θ ν) X) *
    Real.exp (∑ y ∈ sitesNear R.range θ.2,
      R.siteDensity (n * R.params.side) y (G.fieldInsert γ θ a) (G.sitesInsert γ θ) (G.labelsInsert γ θ ν))
open Classical in
def GasGround.labelIntegrand (a : θ.coreBonds → UnitQuaternion) (ν : θ.2 → R.labels.Ω) : ℝ≥0∞ :=
  if G.LabelsAdmissible γ θ a ν then ENNReal.ofReal (G.labelValue γ θ a ν) else 0
def GasGround.clusterPrice (a : θ.coreBonds → UnitQuaternion) : ℝ :=
  R.coupling * R.params.κ * R.params.threshold ^ 2 *
      ((hotLumpsWithin R.params (G.fieldInsert γ θ a) θ.2).card : ℝ) +
    R.params.κ₁ * R.coupling * R.params.threshold ^ 2 *
      (excessLength R.params R.range θ.2 (G.fieldInsert γ θ a) : ℝ)
variable {γ θ}
theorem GasGround.clusterPrice_mul_lintegral_le_one (hrow : R.HasExpansions)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hfar : ∀ a ∈ θ.2, ∀ b ∈ G.recordedSites ∪ γ.sites, R.range < supDist a b)
    (a : θ.coreBonds → UnitQuaternion) :
    ENNReal.ofReal (Real.exp (G.clusterPrice γ θ a)) *
      ∫⁻ ν, G.labelIntegrand γ θ a ν ∂(Measure.pi fun _ : θ.2 => R.labels.μ) ≤ 1 := by
  classical
  by_cases hex : ∃ ν₀, G.LabelsAdmissible γ θ a ν₀
  · obtain ⟨ν₀, hhull, hΦ⟩ := hex
    set P := chainComponents R.range θ.2 with hPdef
    have hP : P.biUnion id = θ.2 := biUnion_chainComponents
    have hY : G.sitesInsert γ θ = θ.2 ∪ (G.recordedSites ∪ γ.sites) := by
      ext z
      simp only [GasGround.sitesInsert, Finset.mem_union]
      tauto
    have hPsub : P ⊆ chainComponents R.range (G.sitesInsert γ θ) := by
      intro X hX
      rw [hY]
      exact mem_chainComponents_union_of_separated hfar hX
    have key := hrow.2.price (n * R.params.side) hside (G.fieldInsert γ θ a) (G.sitesInsert γ θ)
      (G.labelsInsert γ θ ν₀) P hhull hPsub (fun X hX => hΦ X (Finset.mem_sdiff.mp hX).1)
    rw [lintegral_pi_congr_finset R.labels.μ hP] at key
    have hle : ∫⁻ ν, G.labelIntegrand γ θ a ν ∂(Measure.pi fun _ : θ.2 => R.labels.μ) ≤
        ENNReal.ofReal (Real.exp (-G.clusterPrice γ θ a)) := by
      refine le_trans (lintegral_mono fun ν => ?_) (le_trans key (le_of_eq ?_))
      · have hg : glueLabel (G.sitesInsert γ θ) (P.biUnion id) (G.labelsInsert γ θ ν₀)
            (fun z => ν ⟨z.1, hP ▸ z.2⟩) = G.labelsInsert γ θ ν := by
          funext z
          unfold glueLabel GasGround.labelsInsert
          by_cases hz : z.1 ∈ θ.2
          · have hz' : z.1 ∈ P.biUnion id := hP ▸ hz
            simp only [dif_pos hz, dif_pos hz']
          · have hz' : z.1 ∉ P.biUnion id := fun h => hz (hP ▸ h)
            simp only [dif_neg hz, dif_neg hz']
        show G.labelIntegrand γ θ a ν ≤ _
        rw [hg]
        unfold GasGround.labelIntegrand
        split_ifs with h1 h2
        · obtain ⟨X, hX, h0⟩ := h2
          exact absurd h0 (h1.2 X (hPsub hX))
        · have hset : (Finset.univ.filter fun y : TorusSite (n * R.params.side) =>
              ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange R.coupling : ℝ) / 4) =
                sitesNear R.range θ.2 := by
            rw [hP]
            rfl
          rw [hset]
          rfl
        · exact zero_le
        · exact zero_le
      · congr 2
        unfold GasGround.clusterPrice hotLumpsWithin
        rw [hP]
        have hrr : clusterRange R.coupling = R.range := rfl
        rw [hrr]
        ring
    calc ENNReal.ofReal (Real.exp (G.clusterPrice γ θ a)) *
          ∫⁻ ν, G.labelIntegrand γ θ a ν ∂(Measure.pi fun _ : θ.2 => R.labels.μ)
        ≤ ENNReal.ofReal (Real.exp (G.clusterPrice γ θ a)) *
            ENNReal.ofReal (Real.exp (-G.clusterPrice γ θ a)) := by
          gcongr
      _ = 1 := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          simp
  · have h0 : ∀ ν, G.labelIntegrand γ θ a ν = 0 := fun ν => by
      unfold GasGround.labelIntegrand
      rw [if_neg fun h => hex ⟨ν, h⟩]
    simp [h0]
theorem measurableSet_isHullState (hfit : R.params.Admissible) (r : ℕ) (Y : Finset (TorusSite (n * R.params.side))) :
    MeasurableSet {W : TorusField (n * R.params.side) | IsHullState R.params r W Y} := by
  classical
  have hL : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
  have : {W : TorusField (n * R.params.side) | IsHullState R.params r W Y} =
      ⋃ H ∈ {H : Finset (Finset (TorusSite (n * R.params.side))) |
          ∃ W₀, torusHotLumps R.params W₀ = H ∧ IsHullState R.params r W₀ Y},
        {W | torusHotLumps R.params W = H} := by
    ext W
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro h
      exact ⟨_, ⟨W, rfl, h⟩, rfl⟩
    · rintro ⟨H, ⟨W₀, rfl, h₀⟩, hW⟩
      unfold IsHullState torusHotSites at h₀ ⊢
      rw [hW]
      exact h₀
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun H _ => measurableSet_torusHotLumps_eq hfit hL H
theorem GasGround.measurable_labelIntegrand (hfit : R.params.Admissible) (hrow : R.HasExpansions)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) :
    Measurable fun p : (θ.coreBonds → UnitQuaternion) × (θ.2 → R.labels.Ω) =>
      G.labelIntegrand γ θ p.1 p.2 := by
  classical
  obtain ⟨-, hΦ, hφ⟩ := hrow.2.borel (n * R.params.side) hside (G.sitesInsert γ θ)
  have hE : Measurable fun p : (θ.coreBonds → UnitQuaternion) × (θ.2 → R.labels.Ω) =>
      ((G.fieldInsert γ θ p.1, G.labelsInsert γ θ p.2) :
        TorusField (n * R.params.side) × (G.sitesInsert γ θ → R.labels.Ω)) :=
    (((G.continuous_fieldInsert γ θ).measurable).comp measurable_fst).prodMk
      ((G.measurable_labelsInsert γ θ).comp measurable_snd)
  set S : Set (TorusField (n * R.params.side) × (G.sitesInsert γ θ → R.labels.Ω)) :=
    {p | IsHullState R.params R.range p.1 (G.sitesInsert γ θ) ∧
      ∀ X ∈ chainComponents R.range (G.sitesInsert γ θ),
        R.clusterFactor (n * R.params.side) p.1 (G.sitesInsert γ θ) p.2 X ≠ 0} with hS
  have hSm : MeasurableSet S := by
    have h1 : MeasurableSet {p : TorusField (n * R.params.side) × (G.sitesInsert γ θ → R.labels.Ω) |
        IsHullState R.params R.range p.1 (G.sitesInsert γ θ)} :=
      measurable_fst (measurableSet_isHullState hfit R.range _)
    have h2 : MeasurableSet {p : TorusField (n * R.params.side) × (G.sitesInsert γ θ → R.labels.Ω) |
        ∀ X ∈ chainComponents R.range (G.sitesInsert γ θ),
          R.clusterFactor (n * R.params.side) p.1 (G.sitesInsert γ θ) p.2 X ≠ 0} := by
      have : {p : TorusField (n * R.params.side) × (G.sitesInsert γ θ → R.labels.Ω) |
          ∀ X ∈ chainComponents R.range (G.sitesInsert γ θ),
            R.clusterFactor (n * R.params.side) p.1 (G.sitesInsert γ θ) p.2 X ≠ 0} =
          ⋂ X ∈ chainComponents R.range (G.sitesInsert γ θ),
            (fun p : TorusField (n * R.params.side) × (G.sitesInsert γ θ → R.labels.Ω) =>
              R.clusterFactor (n * R.params.side) p.1 (G.sitesInsert γ θ) p.2 X) ⁻¹' {0}ᶜ := by
        ext p
        simp
      rw [this]
      exact Finset.measurableSet_biInter _ fun X _ => hΦ X (measurableSet_singleton 0).compl
    exact h1.inter h2
  set g : TorusField (n * R.params.side) × (G.sitesInsert γ θ → R.labels.Ω) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((∏ X ∈ chainComponents R.range θ.2,
        R.clusterFactor (n * R.params.side) p.1 (G.sitesInsert γ θ) p.2 X) *
      Real.exp (∑ y ∈ sitesNear R.range θ.2,
        (if IsHullState R.params (clusterRange R.coupling) p.1 (G.sitesInsert γ θ) ∧
            ∀ X ∈ chainComponents (clusterRange R.coupling) (G.sitesInsert γ θ),
              R.clusterFactor (n * R.params.side) p.1 (G.sitesInsert γ θ) p.2 X ≠ 0
          then R.siteDensity (n * R.params.side) y p.1 (G.sitesInsert γ θ) p.2 else 0))) with hg
  have hgm : Measurable g := by
    refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)
    · exact Finset.measurable_prod _ fun X _ => hΦ X
    · exact Real.measurable_exp.comp (Finset.measurable_sum _ fun y _ => hφ y)
  have hfinal : (fun p : (θ.coreBonds → UnitQuaternion) × (θ.2 → R.labels.Ω) =>
      G.labelIntegrand γ θ p.1 p.2) =
      (S.indicator g) ∘ fun p => ((G.fieldInsert γ θ p.1, G.labelsInsert γ θ p.2) :
        TorusField (n * R.params.side) × (G.sitesInsert γ θ → R.labels.Ω)) := by
    funext p
    simp only [Function.comp]
    unfold GasGround.labelIntegrand
    by_cases h : G.LabelsAdmissible γ θ p.1 p.2
    · have hmem : ((G.fieldInsert γ θ p.1, G.labelsInsert γ θ p.2) :
          TorusField (n * R.params.side) × (G.sitesInsert γ θ → R.labels.Ω)) ∈ S := h
      rw [if_pos h, Set.indicator_of_mem hmem]
      simp only [hg, GasGround.labelValue]
      congr 3
      refine Finset.sum_congr rfl fun y _ => ?_
      exact (if_pos h).symm
    · have hmem : ((G.fieldInsert γ θ p.1, G.labelsInsert γ θ p.2) :
          TorusField (n * R.params.side) × (G.sitesInsert γ θ → R.labels.Ω)) ∉ S := h
      rw [if_neg h, Set.indicator_of_notMem hmem]
  rw [hfinal]
  exact (hgm.indicator hSm).comp hE
end LabelIntegral
section BaseWeights
variable {R : StepSetup} {n : ℕ} [NeZero n] (G : GasGround R n) (θ : GasSupport R n)
theorem GasFamily.coresDisjoint_empty : (GasFamily.empty : GasFamily R n).CoresDisjoint := by apply _root_.YangMills.Construction.StepGas.ActivityMeasurable.coresDisjoint_empty <;> assumption
theorem GasFamily.cores_disjoint_empty : ∀ θ' : GasSupport R n, (GasFamily.empty : GasFamily R n).Occupies θ' →
    ∀ y, y ∈ θ.core → y ∈ θ'.core → False := by apply _root_.YangMills.Construction.StepGas.ActivityMeasurable.empty_no_overlap <;> assumption
def GasGround.fieldSingle (a : θ.coreBonds → UnitQuaternion) : TorusField (n * R.params.side) :=
  StepSettings.frameField R (G.freeInsert GasFamily.empty θ) G.coarse (G.baseWithClass GasFamily.empty θ a)
theorem GasGround.continuous_fieldSingle : Continuous (G.fieldSingle θ) :=
  (continuous_frameField _ _).comp (continuous_baseWithClass G)
variable {θ}
theorem GasGround.frameField_single (s : SupportState θ) :
    G.frameField (GasFamily.single θ s) = G.fieldSingle θ s.1 := by
  have hsingle : GasFamily.single θ s = (GasFamily.empty : GasFamily R n).insertClass θ s := rfl
  show (G.settingWithFamily (GasFamily.single θ s)).field 0 = _
  rw [ChartSetting.field_zero, hsingle]
  show StepSettings.frameField R (G.settingWithFamily (GasFamily.empty.insertClass θ s)).free G.coarse
    (G.settingWithFamily (GasFamily.empty.insertClass θ s)).fine = _
  rw [G.settingWithFamily_free_insertClass s GasFamily.coresDisjoint_empty (GasFamily.cores_disjoint_empty θ),
    G.settingWithFamily_fine_insertClass s GasFamily.coresDisjoint_empty (GasFamily.cores_disjoint_empty θ)]
  rfl
variable (θ)
theorem toTorusSite_torusSiteInFrame (y : TorusSite n) (L : ℕ) [NeZero L] :
    (toTorusSite n (torusSiteInFrame (stepBlockFrame L n) 1 y : (stepBlockFrame L n).Cell) : TorusSite n) = y := by
  funext k
  unfold toTorusSite torusSiteInFrame
  rw [BlockOffsets.siteCoords_siteOfCoords_one]
  simp [ZMod.intCast_mod]
open Classical in
def GasGround.basesSingle (o : θ.core → BlockOffset R.params.side) : BaseChoice R.params.side n := fun c =>
  if h : toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c ∈ θ.core then
    frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) (o ⟨_, h⟩)
  else G.groundBases c
variable {θ}
theorem GasGround.bases_settingOf_single (s : SupportState θ) :
    (G.settingOf (GasFamily.single θ s)).bases = G.basesSingle θ s.2.2 := by
  classical
  have hsingle : GasFamily.single θ s = (GasFamily.empty : GasFamily R n).insertClass θ s := rfl
  funext c
  show (match (GasFamily.single θ s).baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
    | Sum.inr o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o
    | Sum.inl _ => G.groundBases c) = _
  rw [hsingle, GasFamily.baseAt_insertClass GasFamily.coresDisjoint_empty (GasFamily.cores_disjoint_empty θ)]
  unfold GasGround.basesSingle
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
def BaseAdmissible {F : BlockFrame} (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (y : F.Cell)
    (v : F.Site F.depth) : Prop :=
  ((nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y) → v = cellCentre F.depth y) ∧
    (¬ (nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y) → v ∈ sitesBelow F.depth y ∧
      ∀ B ∈ excludedBoxes J₀ h y, ∀ x ∈ B, ∀ i, x i ≠ v i)
theorem isBaseChoice_iff_baseAdmissible {F : BlockFrame} {J₀ : ℕ} {h : Finset (Finset (F.Site F.depth))}
    {b : F.Cell → F.Site F.depth} : IsBaseChoice J₀ h b ↔ ∀ y, BaseAdmissible J₀ h y (b y) := Iff.rfl
open Classical in
theorem mem_baseChoices_iff {W : (stepBlockFrame R.params.side n).GaugeField 0}
    {b : (stepBlockFrame R.params.side n).Cell → (stepBlockFrame R.params.side n).Site 0} :
    b ∈ baseChoices R.params W ↔ ∀ y, BaseAdmissible R.params.baseDepth
      (LumpContours.hotLumps R.params.grid R.params.threshold (levelSites (stepBlockFrame R.params.side n) 0) W)
      y (b y) := by
  unfold baseChoices
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact isBaseChoice_iff_baseAdmissible
theorem GasGround.basesSingle_torusSiteInFrame (o : θ.core → BlockOffset R.params.side) {y : TorusSite n}
    (hy : y ∈ θ.core) :
    G.basesSingle θ o (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) =
      frameBlockSite R.params.side n y (o ⟨y, hy⟩) := by
  classical
  have hc : toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) = y :=
    toTorusSite_torusSiteInFrame y R.params.side
  have key : ∀ (y' : TorusSite n) (_ : y' = y) (h' : y' ∈ θ.core),
      frameBlockSite R.params.side n y' (o ⟨y', h'⟩) = frameBlockSite R.params.side n y (o ⟨y, hy⟩) := by
    intro y' e h'
    subst e
    rfl
  unfold GasGround.basesSingle
  rw [dif_pos (by rw [hc]; exact hy)]
  exact key _ hc _
open Classical in
theorem GasGround.sum_baseUniformWeight_le_one (hne : θ.core.Nonempty) (W : TorusField (n * R.params.side)) :
    ∑ o : θ.core → BlockOffset R.params.side,
      ENNReal.ofReal (∏ y ∈ θ.core, baseUniformWeight W (G.basesSingle θ o) y) ≤ 1 := by
  set Wf := readAtLevel (stepBlockFrame R.params.side n) 0 W with hWf
  set h := LumpContours.hotLumps R.params.grid R.params.threshold
    (levelSites (stepBlockFrame R.params.side n) 0) Wf with hh
  set cell : TorusSite n → (stepBlockFrame R.params.side n).Cell :=
    fun y => torusSiteInFrame (stepBlockFrame R.params.side n) 1 y with hcell
  set A : θ.core → Finset (BlockOffset R.params.side) := fun y =>
    Finset.univ.filter fun o =>
      BaseAdmissible R.params.baseDepth h (cell y.1) (frameBlockSite R.params.side n y.1 o) with hA
  refine sum_le_one_of_le_prod_uniform A _ fun o => ?_
  by_cases hb : G.basesSingle θ o ∈ baseChoices R.params Wf
  · have hb' := mem_baseChoices_iff.mp hb
    have hcard : ∀ y : θ.core, (Finset.univ.filter fun o' : BlockOffset R.params.side =>
        Function.update (G.basesSingle θ o) (cell y.1) (frameBlockSite R.params.side n y.1 o') ∈
          baseChoices R.params Wf) = A y := by
      intro y
      ext o'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hA]
      rw [mem_baseChoices_iff]
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
      rwa [G.basesSingle_torusSiteInFrame o y.2] at this
    have hshare : ∀ y : θ.core, baseUniformWeight W (G.basesSingle θ o) y.1 = 1 / ((A y).card : ℝ) := by
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
    have h0 : baseUniformWeight W (G.basesSingle θ o) y₀ = 0 := by
      unfold baseUniformWeight
      rw [if_neg hb]
    rw [Finset.prod_eq_zero hy₀ h0]
    simp
end BaseWeights
section Cutoffs
theorem nonneg_of_isCutoff {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 ≤ u)
    (h1 : u < ρ) : 0 ≤ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoff_nonneg_of_lt <;> assumption
theorem cutoffFactor_nonneg_and_le_one {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ}
    (h0 : 0 ≤ u) : 0 ≤ cutoffFactor ρ p u ∧ cutoffFactor ρ p u ≤ 1 := by
  unfold cutoffFactor
  split_ifs with h
  · refine ⟨(Real.exp_pos _).le, ?_⟩
    rw [Real.exp_le_one_iff]
    linarith [nonneg_of_isCutoff hρ hp h0 h]
  · exact ⟨le_rfl, zero_le_one⟩
variable {R : StepSetup} {n : ℕ} [NeZero n] (G : GasGround R n) {θ : GasSupport R n}
theorem GasGround.supportMarks_nonneg_and_le_one (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn)
    (W : TorusField (n * R.params.side)) :
    0 ≤ G.supportMarks θ W ∧ G.supportMarks θ W ≤ 1 := by
  classical
  have hm : ∀ b, 0 ≤ bondMark R G.coarse W b ∧ bondMark R G.coarse W b ≤ 1 := fun b =>
    cutoffFactor_nonneg_and_le_one hρ hp (norm_nonneg _)
  have hf : ∀ b ∈ θ.coreBonds ∩ markedBonds R G.cut,
      0 ≤ (if b ∈ θ.1 then 1 - bondMark R G.coarse W b else bondMark R G.coarse W b) ∧
        (if b ∈ θ.1 then 1 - bondMark R G.coarse W b else bondMark R G.coarse W b) ≤ 1 := by
    intro b _
    have := hm b
    split_ifs
    · constructor <;> linarith
    · exact this
  unfold GasGround.supportMarks
  exact ⟨Finset.prod_nonneg fun b hb => (hf b hb).1, Finset.prod_le_one (fun b hb => (hf b hb).1)
    fun b hb => (hf b hb).2⟩
omit [NeZero n] in
theorem frameField_of_notMem {free : Finset (TorusBond (n * R.params.side))} {V : TorusField n}
    {B : TorusField (n * R.params.side)} {b : TorusBond (n * R.params.side)} (h : b ∉ free) :
    StepSettings.frameField R free V B b.1 b.2 = B b.1 b.2 := by
  classical
  unfold StepSettings.frameField
  exact if_neg h
theorem GasGround.baseWithClass_of_mem {γ : GasFamily R n} {a : θ.coreBonds → UnitQuaternion}
    {b : TorusBond (n * R.params.side)} (h : b ∈ θ.coreBonds) :
    G.baseWithClass γ θ a b.1 b.2 = a ⟨b, h⟩ := by
  classical
  unfold GasGround.baseWithClass
  exact dif_pos h
theorem GasGround.notMem_freeInsert {γ : GasFamily R n} {b : TorusBond (n * R.params.side)} (h : b ∈ θ.coreBonds) :
    b ∉ G.freeInsert γ θ := by
  classical
  intro hb
  exact (Finset.mem_filter.mp hb).2 h
theorem GasGround.fieldSingle_of_mem {a : θ.coreBonds → UnitQuaternion} {b : TorusBond (n * R.params.side)}
    (h : b ∈ θ.coreBonds) : G.fieldSingle θ a b.1 b.2 = a ⟨b, h⟩ := by
  unfold GasGround.fieldSingle
  rw [frameField_of_notMem (G.notMem_freeInsert h), G.baseWithClass_of_mem h]
theorem GasGround.fieldInsert_of_mem {γ : GasFamily R n} {a : θ.coreBonds → UnitQuaternion}
    {b : TorusBond (n * R.params.side)} (h : b ∈ θ.coreBonds) : G.fieldInsert γ θ a b.1 b.2 = a ⟨b, h⟩ := by
  unfold GasGround.fieldInsert
  rw [frameField_of_notMem (G.notMem_freeInsert h), frameField_of_notMem (G.notMem_freeInsert h),
    G.baseWithClass_of_mem h]
theorem GasSupport.mem_coreBonds_of_ends {b : TorusBond (n * R.params.side)}
    (h1 : parentBlock R.params.side b.1 ∈ θ.core)
    (h2 : parentBlock R.params.side (b.1 + TorusFields.unitStep (n * R.params.side) b.2) ∈ θ.core) :
    b ∈ θ.coreBonds := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩
theorem GasSupport.mem_coreBonds_of_bad {b : TorusBond (n * R.params.side)} (hb : b ∈ θ.1) (hr : 1 ≤ R.range) :
    b ∈ θ.coreBonds := by apply _root_.YangMills.Construction.GasStep.mem_coreBonds_of_mem <;> assumption
end Cutoffs
section Measurability
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem measurable_baseUniformWeight (hK : BondKernelBorel) (b : BaseChoice R.params.side n) (y : TorusSite n) :
    Measurable fun W : TorusField (n * R.params.side) => baseUniformWeight W b y := by apply _root_.YangMills.Construction.StepGas.ActivityMeasurable.measurable_baseUniformWeight <;> assumption
theorem GasGround.measurable_clusterPrice (hfit : R.params.Admissible) (G : GasGround R n) (γ : GasFamily R n)
    (θ : GasSupport R n) : Measurable (G.clusterPrice γ θ) := by
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
  exact hF.comp (G.continuous_fieldInsert γ θ).measurable
theorem coordNorm_zero : coordNorm 0 = 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.coordNorm_zero <;> assumption
end Measurability
section MainBound
variable {R : StepSetup} {n : ℕ} [NeZero n]
section Pointwise
variable (G : GasGround R n) {γ : GasFamily R n} {θ : GasSupport R n} (s : SupportState θ)
theorem GasGround.clusterFactor_settingOf_insertClass (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False)
    (X : Finset (TorusSite (n * R.params.side))) :
    R.clusterFactor (n * R.params.side) ((G.settingOf (γ.insertClass θ s)).field 0)
        (G.settingOf (γ.insertClass θ s)).support (G.settingOf (γ.insertClass θ s)).labelling X =
      R.clusterFactor (n * R.params.side) (G.fieldInsert γ θ s.1) (G.sitesInsert γ θ)
        (G.labelsInsert γ θ s.2.1) X := by
  rw [G.field_zero_settingOf_insertClass s hs hc]
  exact dependent_congr (fun Y ω => R.clusterFactor (n * R.params.side) (G.fieldInsert γ θ s.1) Y ω X)
    (G.support_settingOf_insertClass s) _ _ (G.labelling_settingOf_insertClass s hs hc)
theorem GasGround.siteDensity_settingOf_insertClass (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False)
    (y : TorusSite (n * R.params.side)) :
    R.siteDensity (n * R.params.side) y ((G.settingOf (γ.insertClass θ s)).field 0)
        (G.settingOf (γ.insertClass θ s)).support (G.settingOf (γ.insertClass θ s)).labelling =
      R.siteDensity (n * R.params.side) y (G.fieldInsert γ θ s.1) (G.sitesInsert γ θ)
        (G.labelsInsert γ θ s.2.1) := by
  rw [G.field_zero_settingOf_insertClass s hs hc]
  exact dependent_congr (fun Y ω => R.siteDensity (n * R.params.side) y (G.fieldInsert γ θ s.1) Y ω)
    (G.support_settingOf_insertClass s) _ _ (G.labelling_settingOf_insertClass s hs hc)
theorem GasGround.labelsAdmissible_of_isAdmissible (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False) (hρ : 0 < R.ballRadius)
    (hset : (G.settingOf (γ.insertClass θ s)).IsAdmissible) : G.LabelsAdmissible γ θ s.1 s.2.1 := by
  have hzero : (G.settingOf (γ.insertClass θ s)).InBalls 0 := fun b => by
    show coordNorm 0 ≤ R.ballRadius
    rw [coordNorm_zero]
    exact hρ.le
  refine ⟨?_, fun X hX => ?_⟩
  · have := hset.isHull 0 hzero
    rwa [G.field_zero_settingOf_insertClass s hs hc, G.support_settingOf_insertClass s] at this
  · rw [← G.clusterFactor_settingOf_insertClass s hs hc]
    exact hset.factor_ne_zero 0 hzero X (by rw [G.support_settingOf_insertClass s]; exact hX)
theorem GasGround.mem_sitesInsert (γ' : GasFamily R n) {z : TorusSite (n * R.params.side)} (hz : z ∈ θ.2) :
    z ∈ G.sitesInsert γ' θ := by
  simp only [GasGround.sitesInsert, Finset.mem_union]
  exact Or.inr (Or.inr hz)
theorem GasGround.clusterFactor_single_eq (hrow : R.HasExpansions)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    {X : Finset (TorusSite (n * R.params.side))} (hX : X ∈ chainComponents R.range θ.2) :
    R.clusterFactor (n * R.params.side) (G.fieldSingle θ s.1) (G.sitesInsert GasFamily.empty θ)
        (G.labelsInsert GasFamily.empty θ s.2.1) X =
      R.clusterFactor (n * R.params.side) (G.fieldInsert γ θ s.1) (G.sitesInsert γ θ)
        (G.labelsInsert γ θ s.2.1) X := by
  classical
  have hsub : X ⊆ θ.2 := subset_of_mem_chainComponents hX
  refine hrow.2.reads_class (n * R.params.side) hside _ _ _ _ _ _ X
    (fun z hz => G.mem_sitesInsert _ (hsub hz))
    (fun z hz => G.mem_sitesInsert _ (hsub hz)) (fun b h1 h2 => ?_) (fun z hz hz' hzX => ?_)
  · have hbs : b ∈ θ.coreBonds := GasSupport.mem_coreBonds_of_ends
      (GasSupport.parentBlock_mem_core_of_mem_sites (hsub h1))
      (GasSupport.parentBlock_mem_core_of_mem_sites (hsub h2))
    rw [G.fieldSingle_of_mem hbs, G.fieldInsert_of_mem hbs]
  · have hzθ := hsub hzX
    unfold GasGround.labelsInsert
    simp only [dif_pos hzθ]
theorem GasGround.activity_eq (hrow : R.HasExpansions) (hside : IsBlockTorusSide R.params (n * R.params.side)) :
    G.activity θ s = G.supportMarks θ (G.fieldSingle θ s.1) *
      (∏ X ∈ chainComponents R.range θ.2, R.clusterFactor (n * R.params.side) (G.fieldInsert γ θ s.1)
        (G.sitesInsert γ θ) (G.labelsInsert γ θ s.2.1) X) *
      ∏ y ∈ θ.core, baseUniformWeight (G.fieldSingle θ s.1) (G.basesSingle θ s.2.2) y := by
  have e0 : ∀ X ∈ chainComponents R.range θ.2,
      R.clusterFactor (n * R.params.side) (G.frameField (GasFamily.single θ s))
        (G.settingOf (GasFamily.single θ s)).support (G.settingOf (GasFamily.single θ s)).labelling X =
      R.clusterFactor (n * R.params.side) (G.fieldInsert γ θ s.1) (G.sitesInsert γ θ)
        (G.labelsInsert γ θ s.2.1) X := by
    intro X hX
    rw [← G.clusterFactor_single_eq s hrow hside hX, G.frameField_single s]
    exact dependent_congr (fun Y ω => R.clusterFactor (n * R.params.side) (G.fieldSingle θ s.1) Y ω X)
      (G.support_settingOf_insertClass s) _ _
      (G.labelling_settingOf_insertClass s GasFamily.coresDisjoint_empty (GasFamily.cores_disjoint_empty θ))
  unfold GasGround.activity
  rw [Finset.prod_congr rfl e0, G.frameField_single s, G.bases_settingOf_single s]
theorem GasGround.exp_classExponent_eq (ch : ℝ) (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False) :
    Real.exp ((G.settingOf (γ.insertClass θ s)).classExponent ch θ) =
      Real.exp (∑ y ∈ sitesNear R.range θ.2,
          R.siteDensity (n * R.params.side) y (G.fieldInsert γ θ s.1) (G.sitesInsert γ θ)
            (G.labelsInsert γ θ s.2.1)) *
        Real.exp (G.clusterPrice γ θ s.1) * clusterWeight R.params.side ch R.coupling R.range θ := by
  have h1 : (G.settingOf (γ.insertClass θ s)).densityNear θ.2 = ∑ y ∈ sitesNear R.range θ.2,
      R.siteDensity (n * R.params.side) y (G.fieldInsert γ θ s.1) (G.sitesInsert γ θ)
        (G.labelsInsert γ θ s.2.1) :=
    Finset.sum_congr rfl fun y _ => G.siteDensity_settingOf_insertClass s hs hc y
  unfold ChartSetting.classExponent clusterWeight
  rw [h1, G.field_zero_settingOf_insertClass s hs hc, ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold GasGround.clusterPrice
  ring
theorem state_bound_arith {M F Bp z Es Ep w : ℝ} {mass m₀ J : ℝ≥0∞} (hM : M ≤ 1) (hF : 0 ≤ F) (hB : 0 ≤ Bp)
    (hEs : 0 < Es) (hEp : 0 < Ep) (hw : ENNReal.ofReal w ≤ mass)
    (hm : mass ≤ ENNReal.ofReal (Es * Ep * z) * m₀) (hJ : J = ENNReal.ofReal (F * Es)) :
    ENNReal.ofReal (M * F * Bp) * ENNReal.ofReal w ≤
      (ENNReal.ofReal z * m₀) * (ENNReal.ofReal Bp * J * ENNReal.ofReal Ep) := by
  have hmain : M * F * Bp ≤ F * Bp := by
    have := mul_le_mul_of_nonneg_right hM (mul_nonneg hF hB)
    linarith [mul_assoc M F Bp]
  calc ENNReal.ofReal (M * F * Bp) * ENNReal.ofReal w
      ≤ ENNReal.ofReal (F * Bp) * mass := mul_le_mul' (ENNReal.ofReal_le_ofReal hmain) hw
    _ ≤ ENNReal.ofReal (F * Bp) * (ENNReal.ofReal (Es * Ep * z) * m₀) := by gcongr
    _ = _ := by
        rw [hJ, ENNReal.ofReal_mul hF, ENNReal.ofReal_mul hF,
          ENNReal.ofReal_mul (mul_nonneg hEs.le hEp.le), ENNReal.ofReal_mul hEs.le]
        ring
theorem GasGround.activity_mul_mass_le (hrow : R.HasExpansions) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn) (hr : 1 ≤ R.range) (hs : γ.CoresDisjoint)
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
        (ENNReal.ofReal (∏ y ∈ θ.core, baseUniformWeight (G.fieldSingle θ s.1) (G.basesSingle θ s.2.2) y) *
          G.labelIntegrand γ θ s.1 s.2.1 * ENNReal.ofReal (Real.exp (G.clusterPrice γ θ s.1))) := by
  classical
  by_cases hd : G.activity θ s = 0
  · simp [hd]
  have hok := G.labelsAdmissible_of_isAdmissible s hs hc hρ hset
  have hfac := G.activity_eq (γ := γ) s hrow hside
  have hmarks := G.supportMarks_nonneg_and_le_one (θ := θ) hρ hp (G.fieldSingle θ s.1)
  have hbad : ∀ b ∈ θ.1, 1 - bondMark R G.coarse (G.frameField (GasFamily.single θ s)) b ≠ 0 := by
    intro b hb
    have hm0 : G.supportMarks θ (G.fieldSingle θ s.1) ≠ 0 := fun h0 => hd (by rw [hfac, h0]; ring)
    have hbs : b ∈ θ.coreBonds ∩ markedBonds R G.cut :=
      Finset.mem_inter.mpr ⟨GasSupport.mem_coreBonds_of_bad hb hr, hmk hb⟩
    have := (Finset.prod_ne_zero_iff.mp hm0) b hbs
    rw [if_pos hb] at this
    rwa [G.frameField_single s]
  have hF0 : 0 ≤ ∏ X ∈ chainComponents R.range θ.2,
      R.clusterFactor (n * R.params.side) (G.fieldInsert γ θ s.1) (G.sitesInsert γ θ) (G.labelsInsert γ θ s.2.1) X :=
    Finset.prod_nonneg fun X hX =>
      hrow.2.factor_nonneg (n * R.params.side) hside _ _ _ X
  have hBp0 : 0 ≤ ∏ y ∈ θ.core, baseUniformWeight (G.fieldSingle θ s.1) (G.basesSingle θ s.2.2) y :=
    Finset.prod_nonneg fun y _ => by
      unfold baseUniformWeight
      split_ifs <;> positivity
  have hm := hstar hbad
  rw [G.exp_classExponent_eq s ch hs hc] at hm
  rw [hfac]
  refine state_bound_arith hmarks.2 hF0 hBp0 (Real.exp_pos _) (Real.exp_pos _) hw hm ?_
  unfold GasGround.labelIntegrand
  rw [if_pos hok]
  rfl
end Pointwise
theorem GasGround.activity_mul_weight_le (G : GasGround R n) (σ : G.Config) (i : G.GasSpin) (ch : ℝ)
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
            baseUniformWeight (G.fieldSingle i.1 v.1.1) (G.basesSingle i.1 v.1.2.2) y) *
          G.labelIntegrand (G.familyOf σ) i.1 v.1.1 v.1.2.1 *
          ENNReal.ofReal (Real.exp (G.clusterPrice (G.familyOf σ) i.1 v.1.1))) := by
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
  exact G.activity_mul_mass_le v.1 hrow hside hρ hp hr hs hc hfar hmk ch _ _ hset hw (hstar hset)
end MainBound
theorem clusterIntegralLeWeight_holds (hS : ClusterExpansionOfAStep.InsertClassMassBound) (hMass : SettingMassEqIntegral)
    (hFac : ActivityIsMeasurable) (hFl : StepFloors.EventuallyFloorConditions)
    (hK : BondKernelBorel) (hCfg : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) :
    ClusterIntegralLeWeight := by
  classical
  obtain ⟨rtS, hrtS, hS⟩ := hS
  obtain ⟨rtM, hrtM, hM⟩ := hMass
  refine ⟨fun c => min (rtS c) (rtM c), fun c => lt_min (hrtS c) (hrtM c), fun T hT hrt => ?_⟩
  obtain ⟨yS, hyS⟩ := hS T hT (hrt.trans (min_le_left _ _))
  obtain ⟨yM, hyM⟩ := hM T hT (hrt.trans (min_le_right _ _))
  obtain ⟨yC, hyC⟩ := hCfg T hT
  have hL0 : (0 : ℝ) < (T.side : ℝ) + 1 := by positivity
  obtain ⟨yF, hyF⟩ := hFl T hT ((T.side : ℝ) + 1) 1 hL0 one_pos
  refine ⟨max (max (max yS yC) yM) (max yF T.floorMin), fun y hy R hR hxx n _ G σ i hG hadm hset hσi hap => ?_⟩
  have hy0 : max yS yC ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hy1 : yS ≤ y := le_trans (le_max_left _ _) hy0
  have hy5 : yC ≤ y := le_trans (le_max_right _ _) hy0
  have hy2 : yM ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hy3 : yF ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hy4 : T.floorMin ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
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
    ENNReal.ofReal (∏ y ∈ i.1.core, baseUniformWeight (G.fieldSingle i.1 a) (G.basesSingle i.1 o) y) with hBs
  set Q : (i.1.coreBonds → UnitQuaternion) → ℝ≥0∞ :=
    fun a => ENNReal.ofReal (Real.exp (G.clusterPrice (G.familyOf σ) i.1 a)) with hQ
  have hBm : ∀ o, Measurable fun a => Bs a o := fun o =>
    ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun y _ =>
      (measurable_baseUniformWeight hK _ y).comp (G.continuous_fieldSingle i.1).measurable)
  have hQm : Measurable Q :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (GasGround.measurable_clusterPrice hfit G _ _))
  have hJm := G.measurable_labelIntegrand (γ := G.familyOf σ) (θ := i.1) hfit hrow hside
  have hcore : i.1.core.Nonempty := by
    obtain ⟨z, hz⟩ := i.2.isCluster.1
    exact ⟨_, GasSupport.parentBlock_mem_core hz⟩
  have hH1 : ∫⁻ p : SupportState i.1, Bs p.1 p.2.2 * G.labelIntegrand (G.familyOf σ) i.1 p.1 p.2.1 * Q p.1
      ∂(supportStateMeasure i.1) ≤ 1 :=
    lintegral_prod_three_le _ _ Bs (G.labelIntegrand (G.familyOf σ) i.1) Q hBm hJm hQm
      (fun a => G.sum_baseUniformWeight_le_one hcore _)
      (fun a => G.clusterPrice_mul_lintegral_le_one hrow hside hfar a)
  have hHm : Measurable fun p : SupportState i.1 =>
      Bs p.1 p.2.2 * G.labelIntegrand (G.familyOf σ) i.1 p.1 p.2.1 * Q p.1 := by
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
        fun v => ENNReal.ofReal (G.weight (Function.update σ i (Sum.inr v)))) v
        ∂((supportStateMeasure i.1).comap Subtype.val)
      ≤ ∫⁻ v : G.SpinState i, (fun p : SupportState i.1 =>
          E * (Bs p.1 p.2.2 * G.labelIntegrand (G.familyOf σ) i.1 p.1 p.2.1 * Q p.1)) v.1
        ∂((supportStateMeasure i.1).comap Subtype.val) := by
        refine lintegral_mono fun v => ?_
        exact G.activity_mul_weight_le σ i T.gasRate v hrow hside hρ hp (by omega) hsep hc hfar
          (hyC y hy5 R hR hxx n G hG)
          fun h1 h2 => hyS y hy1 R hR n G σ i v.1 hG hadm hset hσi hap h1 h2
    _ ≤ ∫⁻ p : SupportState i.1, E * (Bs p.1 p.2.2 * G.labelIntegrand (G.familyOf σ) i.1 p.1 p.2.1 * Q p.1)
        ∂(supportStateMeasure i.1) := lintegral_comap_subtypeVal_le _ _ (hHm.const_mul E)
    _ = E * ∫⁻ p : SupportState i.1, Bs p.1 p.2.2 * G.labelIntegrand (G.familyOf σ) i.1 p.1 p.2.1 * Q p.1
        ∂(supportStateMeasure i.1) := lintegral_const_mul _ hHm
    _ ≤ E * 1 := by gcongr
    _ = E := mul_one _
end YangMills.Construction.StepGas
end
