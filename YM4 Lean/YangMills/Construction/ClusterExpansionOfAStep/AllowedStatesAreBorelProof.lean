import YangMills.Construction.ClusterExpansionOfAStep.AdmissionReadsVOnItsHullProof
import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesAreBorel
import YangMills.Construction.ClusterExpansionOfAStep.FactorOfAClassIsBorelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings StepGas StepCosts
namespace SingleSupportStates
variable {R : StepSetup} {n : ℕ} [NeZero n] (G : GasGround R n) (θ : GasSupport R n)
theorem coresDisjoint_empty : (GasFamily.empty : GasFamily R n).CoresDisjoint := by apply _root_.YangMills.Construction.StepGas.ActivityMeasurable.coresDisjoint_empty <;> assumption
theorem not_occupies_empty : ∀ θ' : GasSupport R n, (GasFamily.empty : GasFamily R n).Occupies θ' →
    ∀ y, y ∈ θ.core → y ∈ θ'.core → False := by apply _root_.YangMills.Construction.StepGas.ActivityMeasurable.empty_no_overlap <;> assumption
open Classical in
def singleFreeBonds : Finset (TorusBond (n * R.params.side)) :=
  (G.settingWithFamily GasFamily.empty).free.filter fun b => b ∉ θ.coreBonds
def singleField (a : θ.coreBonds → UnitQuaternion) : TorusField (n * R.params.side) :=
  frameField R (singleFreeBonds G θ) G.coarse (G.baseWithClass GasFamily.empty θ a)
theorem continuous_singleField : Continuous (singleField G θ) :=
  (continuous_frameField _ _).comp (continuous_baseWithClass G)
def singleSites : Finset (TorusSite (n * R.params.side)) :=
  G.recordedSites ∪ ((GasFamily.empty : GasFamily R n).sites ∪ θ.2)
theorem mem_support_of_not_mem {z : TorusSite (n * R.params.side)} (hz : z ∈ singleSites G θ) (h : z ∉ θ.2) :
    z ∈ (G.settingWithFamily GasFamily.empty).support := by apply _root_.YangMills.Construction.StepGas.ActivityMeasurable.mem_ground_support <;> assumption
open Classical in
def singleLabelling (ν : θ.2 → R.labels.Ω) (z : singleSites G θ) : R.labels.Ω :=
  if h : z.1 ∈ θ.2 then ν ⟨z.1, h⟩
  else (G.settingWithFamily GasFamily.empty).labelling ⟨z.1, mem_support_of_not_mem G θ z.2 h⟩
theorem measurable_singleLabelling : Measurable (singleLabelling G θ) := by
  classical
  refine measurable_pi_iff.mpr fun z => ?_
  unfold singleLabelling
  by_cases h : z.1 ∈ θ.2
  · simp only [dif_pos h]
    exact measurable_pi_apply _
  · simp only [dif_neg h]
    exact measurable_const
open Classical in
def singleBases (o : θ.core → BlockOffset R.params.side) : BaseChoice R.params.side n := fun c =>
  if h : toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c ∈ θ.core then
    frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) (o ⟨_, h⟩)
  else G.groundBases c
variable {θ}
variable (s : SupportState θ)
theorem frameField_single : G.frameField (GasFamily.single θ s) = singleField G θ s.1 := by
  have hsingle : GasFamily.single θ s = (GasFamily.empty : GasFamily R n).insertClass θ s := rfl
  show (G.settingWithFamily (GasFamily.single θ s)).field 0 = _
  rw [ChartSetting.field_zero, hsingle]
  show frameField R (G.settingWithFamily (GasFamily.empty.insertClass θ s)).free G.coarse
    (G.settingWithFamily (GasFamily.empty.insertClass θ s)).fine = _
  rw [G.settingWithFamily_free_insertClass s coresDisjoint_empty (not_occupies_empty θ),
    G.settingWithFamily_fine_insertClass s coresDisjoint_empty (not_occupies_empty θ)]
  rfl
theorem support_single : (G.settingOf (GasFamily.single θ s)).support = singleSites G θ := by apply _root_.YangMills.Construction.StepGas.ActivityMeasurable.support_single <;> assumption
theorem labelling_single (z : TorusSite (n * R.params.side)) (hz : z ∈ (G.settingOf (GasFamily.single θ s)).support)
    (hz' : z ∈ singleSites G θ) :
    (G.settingOf (GasFamily.single θ s)).labelling ⟨z, hz⟩ = singleLabelling G θ s.2.1 ⟨z, hz'⟩ := by
  classical
  have hs' : ((GasFamily.empty : GasFamily R n).insertClass θ s).CoresDisjoint :=
    coresDisjoint_empty.insertClass (not_occupies_empty θ)
  have hself : ((GasFamily.empty : GasFamily R n).insertClass θ s).Occupies θ :=
    GasFamily.occupies_insertClass.mpr (Or.inl rfl)
  show (if h : z ∈ ((GasFamily.empty : GasFamily R n).insertClass θ s).sites then
    ((GasFamily.empty : GasFamily R n).insertClass θ s).labelAt h else
    G.recordedLabel ⟨z, (Finset.mem_union.mp hz).resolve_right h⟩) = _
  unfold singleLabelling
  by_cases hθ : z ∈ θ.2
  · have hzs : z ∈ ((GasFamily.empty : GasFamily R n).insertClass θ s).sites := by
      rw [GasFamily.sites_insertClass]
      exact Finset.mem_union_right _ hθ
    rw [dif_pos hzs, GasFamily.labelAt_eq_of_mem _ hs' hzs hself hθ, GasFamily.state_insertClass_self]
    simp only [dif_pos hθ]
  · simp only [dif_neg hθ]
    have hne : z ∉ (GasFamily.empty : GasFamily R n).sites := by
      intro h
      obtain ⟨θ', hh, -⟩ := GasFamily.exists_of_mem_sites h
      simp [GasFamily.Occupies, GasFamily.empty] at hh
    have hzs : z ∉ ((GasFamily.empty : GasFamily R n).insertClass θ s).sites := by
      rw [GasFamily.sites_insertClass]
      simp [hne, hθ]
    show _ = (if h : z ∈ (GasFamily.empty : GasFamily R n).sites then (GasFamily.empty : GasFamily R n).labelAt h else
      G.recordedLabel ⟨z, (Finset.mem_union.mp (mem_support_of_not_mem G θ hz' hθ)).resolve_right h⟩)
    rw [dif_neg hne, dif_neg hzs]
theorem bases_single : (G.settingOf (GasFamily.single θ s)).bases = singleBases G θ s.2.2 := by
  classical
  have hsingle : GasFamily.single θ s = (GasFamily.empty : GasFamily R n).insertClass θ s := rfl
  funext c
  show (match (GasFamily.single θ s).baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
    | Sum.inr o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o
    | Sum.inl _ => G.groundBases c) = _
  rw [hsingle, GasFamily.baseAt_insertClass coresDisjoint_empty (not_occupies_empty θ)]
  unfold singleBases
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
theorem dependent_congr {T Ω α : Type} (f : ∀ Y : Finset T, (Y → Ω) → α) {Y Y' : Finset T} (h : Y = Y')
    (ω : Y → Ω) (ω' : Y' → Ω) (hω : ∀ z (hz : z ∈ Y) (hz' : z ∈ Y'), ω ⟨z, hz⟩ = ω' ⟨z, hz'⟩) :
    f Y ω = f Y' ω' := by apply _root_.YangMills.Construction.StepGas.ActivityMeasurable.dependent_congr <;> assumption
theorem measurable_bondMark (hC : ChartCoordMeasurable) (hp : IsCutoff R.ballRadius R.barrierFn)
    (V : TorusField n) (b : TorusBond (n * R.params.side)) :
    Measurable fun W : TorusField (n * R.params.side) => bondMark R V W b := by apply _root_.YangMills.Construction.StepGas.ActivityMeasurable.measurable_bondMark <;> assumption
theorem measurable_baseUniformWeight (hK : BondKernelBorel) (b : BaseChoice R.params.side n) (y : TorusSite n) :
    Measurable fun W : TorusField (n * R.params.side) => baseUniformWeight W b y := by apply _root_.YangMills.Construction.StepGas.ActivityMeasurable.measurable_baseUniformWeight <;> assumption
theorem measurableSet_isHullState {m : ℕ} [NeZero m] {ℓ : StepParameters} (hfit : ℓ.Admissible)
    (hLn : ℓ.side ∣ m) (r : ℕ) (Y : Finset (TorusSite m)) :
    MeasurableSet {W : TorusField m | IsHullState ℓ r W Y} := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurableSet_isHullState <;> assumption
theorem measurableSet_isAllowed (hC : ChartCoordMeasurable) (hK : BondKernelBorel)
    (hfit : R.params.Admissible) (hrow : R.HasExpansions) (hp : IsCutoff R.ballRadius R.barrierFn)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) (θ : GasSupport R n) :
    MeasurableSet {s : SupportState θ | G.IsAllowed θ s} := by
  classical
  obtain ⟨-, hΦ, -⟩ := hrow.2.borel (n * R.params.side) hside (singleSites G θ)
  have hf : Measurable fun s : SupportState θ => singleField G θ s.1 :=
    (continuous_singleField G θ).measurable.comp measurable_fst
  have hl : Measurable fun s : SupportState θ => singleLabelling G θ s.2.1 :=
    (measurable_singleLabelling G θ).comp (measurable_fst.comp measurable_snd)
  have e : {s : SupportState θ | G.IsAllowed θ s} =
      ((fun s : SupportState θ => singleField G θ s.1) ⁻¹'
          {W | IsHullState R.params R.range W (singleSites G θ)}) ∩
        ((⋂ X ∈ chainComponents R.range θ.2, {s : SupportState θ |
            R.clusterFactor (n * R.params.side) (singleField G θ s.1) (singleSites G θ)
              (singleLabelling G θ s.2.1) X ≠ 0}) ∩
          ((⋂ b ∈ θ.coreBonds ∩ markedBonds R G.cut, {s : SupportState θ |
              b ∉ θ.1 → bondMark R G.coarse (singleField G θ s.1) b ≠ 0}) ∩
            ⋂ y ∈ θ.core, {s : SupportState θ |
              baseUniformWeight (singleField G θ s.1) (singleBases G θ s.2.2) y ≠ 0})) := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter]
    unfold GasGround.IsAllowed
    rw [frameField_single G s, bases_single G s]
    have hΦe : ∀ X, R.clusterFactor (n * R.params.side) (singleField G θ s.1)
        (G.settingOf (GasFamily.single θ s)).support (G.settingOf (GasFamily.single θ s)).labelling X =
        R.clusterFactor (n * R.params.side) (singleField G θ s.1) (singleSites G θ)
          (singleLabelling G θ s.2.1) X := fun X =>
      dependent_congr (fun Y ω => R.clusterFactor (n * R.params.side) (singleField G θ s.1) Y ω X)
        (support_single G s) _ _ (labelling_single G s)
    simp only [hΦe]
    rw [support_single G s]
  rw [e]
  refine (hf (measurableSet_isHullState hfit (Dvd.intro_left n rfl) _ _)).inter
    (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))
  · refine Finset.measurableSet_biInter _ fun X _ => ?_
    exact (measurableSet_singleton (0 : ℝ)).compl.preimage ((hΦ X).comp (hf.prodMk hl))
  · refine Finset.measurableSet_biInter _ fun b _ => ?_
    by_cases hb : b ∈ θ.1
    · have : {s : SupportState θ | b ∉ θ.1 → bondMark R G.coarse (singleField G θ s.1) b ≠ 0} = Set.univ := by
        ext s
        simp [hb]
      rw [this]
      exact MeasurableSet.univ
    · have : {s : SupportState θ | b ∉ θ.1 → bondMark R G.coarse (singleField G θ s.1) b ≠ 0} =
          (fun s : SupportState θ => bondMark R G.coarse (singleField G θ s.1) b) ⁻¹' {0}ᶜ := by
        ext s
        simp [hb]
      rw [this]
      exact (measurableSet_singleton (0 : ℝ)).compl.preimage ((measurable_bondMark hC hp G.coarse b).comp hf)
  · refine Finset.measurableSet_biInter _ fun y _ => ?_
    have hm0 : ∀ o : θ.core → BlockOffset R.params.side, Measurable fun a : θ.coreBonds → UnitQuaternion =>
        baseUniformWeight (singleField G θ a) (singleBases G θ o) y := fun o => by
      have h := measurable_baseUniformWeight (R := R) hK (singleBases G θ o) y
      exact h.comp (continuous_singleField G θ).measurable
    have hm : Measurable fun q : (θ.coreBonds → UnitQuaternion) × (θ.core → BlockOffset R.params.side) =>
        baseUniformWeight (singleField G θ q.1) (singleBases G θ q.2) y :=
      measurable_from_prod_countable_left hm0
    have hq : Measurable fun s : SupportState θ =>
        ((s.1, s.2.2) : (θ.coreBonds → UnitQuaternion) × (θ.core → BlockOffset R.params.side)) :=
      measurable_fst.prodMk (measurable_snd.comp measurable_snd)
    have h9 := hm.comp hq
    simp only [Function.comp_def] at h9
    have h10 : {s : SupportState θ | baseUniformWeight (singleField G θ s.1) (singleBases G θ s.2.2) y ≠ 0} =
        (fun s : SupportState θ => baseUniformWeight (singleField G θ s.1) (singleBases G θ s.2.2) y) ⁻¹'
          {0}ᶜ := by
      ext s
      simp
    rw [h10]
    exact (measurableSet_singleton (0 : ℝ)).compl.preimage h9
end SingleSupportStates
theorem allowedStatesMeasurable (hC : ChartCoordMeasurable) (hK : BondKernelBorel) :
    AllowedStatesMeasurable := by
  intro R hfit hrow hp n _ G i hG
  have hside : IsBlockTorusSide R.params (n * R.params.side) := by
    refine ⟨Dvd.intro_left n rfl, ?_⟩
    have hL : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
    rcases hG with hc | hh
    · rw [Nat.mul_comm]
      exact Nat.mul_le_mul_right _ hc.n₀_le
    · exact hh.isBlockSide.2.trans (Nat.le_mul_of_pos_right _ hL)
  exact SingleSupportStates.measurableSet_isAllowed G hC hK hfit hrow hp hside i.1
end YangMills.Construction.ClusterExpansionOfAStep
end
