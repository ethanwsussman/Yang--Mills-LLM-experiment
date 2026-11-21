import YangMills.Construction.ClusterExpansionOfAStep.ChartCoordinateIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfTheGas
import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import Mathlib
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsBorel
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.StepGas
open ColdStepAtMirrorFrames StepSettings
def ActivityIsMeasurable : Prop :=
  ∀ (R : StepSetup), R.params.Admissible → R.HasExpansions → IsCutoff R.ballRadius R.barrierFn →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n) (i : G.GasSpin), G.IsAdmissibleGround →
    Measurable fun v : G.SpinState i => G.activity i.1 v.1
end YangMills.Construction.StepGas
end

noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps StepSettings StepCosts ColdStepAtMirrorFrames
namespace StepGas
namespace ActivityMeasurable
variable {R : StepSetup} {n : ℕ} [NeZero n] (G : GasGround R n) (θ : GasSupport R n)
theorem coresDisjoint_empty : (GasFamily.empty : GasFamily R n).CoresDisjoint := by
  intro θ₁ θ₂ h
  simp [GasFamily.Occupies, GasFamily.empty] at h
theorem empty_no_overlap : ∀ θ' : GasSupport R n, (GasFamily.empty : GasFamily R n).Occupies θ' →
    ∀ y, y ∈ θ.core → y ∈ θ'.core → False := by
  intro θ₁ h
  simp [GasFamily.Occupies, GasFamily.empty] at h
open Classical in
def singleFree : Finset (TorusBond (n * R.params.side)) :=
  (G.settingWithFamily GasFamily.empty).free.filter fun b => b ∉ θ.coreBonds
def singleField (a : θ.coreBonds → UnitQuaternion) : TorusField (n * R.params.side) :=
  frameField R (singleFree G θ) G.coarse (G.baseWithClass GasFamily.empty θ a)
theorem continuous_singleField : Continuous (singleField G θ) :=
  (continuous_frameField _ _).comp (continuous_baseWithClass G)
def singleSites : Finset (TorusSite (n * R.params.side)) :=
  G.recordedSites ∪ ((GasFamily.empty : GasFamily R n).sites ∪ θ.2)
theorem mem_ground_support {z : TorusSite (n * R.params.side)} (hz : z ∈ singleSites G θ) (h : z ∉ θ.2) :
    z ∈ (G.settingWithFamily GasFamily.empty).support := by
  show z ∈ G.recordedSites ∪ (GasFamily.empty : GasFamily R n).sites
  simp only [singleSites, Finset.mem_union] at hz ⊢
  tauto
open Classical in
def singleLabelling (ν : θ.2 → R.labels.Ω) (z : singleSites G θ) : R.labels.Ω :=
  if h : z.1 ∈ θ.2 then ν ⟨z.1, h⟩
  else (G.settingWithFamily GasFamily.empty).labelling ⟨z.1, mem_ground_support G θ z.2 h⟩
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
  rw [G.settingWithFamily_free_insertClass s coresDisjoint_empty (empty_no_overlap θ),
    G.settingWithFamily_fine_insertClass s coresDisjoint_empty (empty_no_overlap θ)]
  rfl
theorem support_single : (G.settingOf (GasFamily.single θ s)).support = singleSites G θ := by
  have hsingle : GasFamily.single θ s = (GasFamily.empty : GasFamily R n).insertClass θ s := rfl
  show G.recordedSites ∪ (GasFamily.single θ s).sites = _
  rw [hsingle, GasFamily.sites_insertClass]
  rfl
theorem labelling_single (z : TorusSite (n * R.params.side)) (hz : z ∈ (G.settingOf (GasFamily.single θ s)).support)
    (hz' : z ∈ singleSites G θ) :
    (G.settingOf (GasFamily.single θ s)).labelling ⟨z, hz⟩ = singleLabelling G θ s.2.1 ⟨z, hz'⟩ := by
  classical
  have hs' : ((GasFamily.empty : GasFamily R n).insertClass θ s).CoresDisjoint :=
    coresDisjoint_empty.insertClass (empty_no_overlap θ)
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
      G.recordedLabel ⟨z, (Finset.mem_union.mp (mem_ground_support G θ hz' hθ)).resolve_right h⟩)
    rw [dif_neg hne, dif_neg hzs]
theorem bases_single : (G.settingOf (GasFamily.single θ s)).bases = singleBases G θ s.2.2 := by
  classical
  have hsingle : GasFamily.single θ s = (GasFamily.empty : GasFamily R n).insertClass θ s := rfl
  funext c
  show (match (GasFamily.single θ s).baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
    | Sum.inr o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o
    | Sum.inl _ => G.groundBases c) = _
  rw [hsingle, GasFamily.baseAt_insertClass coresDisjoint_empty (empty_no_overlap θ)]
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
    f Y ω = f Y' ω' := by
  subst h
  congr 1
  funext z
  exact hω z.1 z.2 z.2
theorem activity_eq : G.activity θ s = G.supportMarks θ (singleField G θ s.1) *
      (∏ X ∈ chainComponents R.range θ.2,
        R.clusterFactor (n * R.params.side) (singleField G θ s.1) (singleSites G θ) (singleLabelling G θ s.2.1) X) *
      ∏ y ∈ θ.core, baseUniformWeight (singleField G θ s.1) (singleBases G θ s.2.2) y := by
  have e0 : ∀ X ∈ chainComponents R.range θ.2,
      R.clusterFactor (n * R.params.side) (G.frameField (GasFamily.single θ s))
        (G.settingOf (GasFamily.single θ s)).support (G.settingOf (GasFamily.single θ s)).labelling X =
      R.clusterFactor (n * R.params.side) (singleField G θ s.1) (singleSites G θ) (singleLabelling G θ s.2.1) X := by
    intro X _
    rw [frameField_single G s]
    exact dependent_congr (fun Y ω => R.clusterFactor (n * R.params.side) (singleField G θ s.1) Y ω X)
      (support_single G s) _ _ (labelling_single G s)
  unfold GasGround.activity
  rw [Finset.prod_congr rfl e0, frameField_single G s, bases_single G s]
theorem quaternion_norm_eq_sqrt (q : ℍ[ℝ]) :
    ‖q‖ = Real.sqrt (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) := by
  rw [← Quaternion.normSq_def', Quaternion.normSq_eq_norm_mul_self, Real.sqrt_mul_self (norm_nonneg _)]
theorem measurable_bondMark (hC : ChartCoordMeasurable) (hp : IsCutoff R.ballRadius R.barrierFn) (V : TorusField n)
    (b : TorusBond (n * R.params.side)) : Measurable fun W : TorusField (n * R.params.side) => bondMark R V W b := by
  classical
  obtain ⟨h0, h1, h2, h3⟩ := hC R.params n b
  have hV : Measurable fun W : TorusField (n * R.params.side) =>
      ((V, W) : TorusField n × TorusField (n * R.params.side)) :=
    measurable_const.prodMk measurable_id
  set c : ℍ[ℝ] := ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ])
    with hc
  have hu : Measurable fun W : TorusField (n * R.params.side) =>
      ‖((chartCoord R.params V W b : imaginaryQuaternions) : ℍ[ℝ]) - c‖ := by
    have e : (fun W : TorusField (n * R.params.side) =>
        ‖((chartCoord R.params V W b : imaginaryQuaternions) : ℍ[ℝ]) - c‖) = fun W =>
        Real.sqrt ((((chartCoord R.params V W b : imaginaryQuaternions) : ℍ[ℝ]).re - c.re) ^ 2 +
          (((chartCoord R.params V W b : imaginaryQuaternions) : ℍ[ℝ]).imI - c.imI) ^ 2 +
          (((chartCoord R.params V W b : imaginaryQuaternions) : ℍ[ℝ]).imJ - c.imJ) ^ 2 +
          (((chartCoord R.params V W b : imaginaryQuaternions) : ℍ[ℝ]).imK - c.imK) ^ 2) := by
      funext W
      rw [quaternion_norm_eq_sqrt]
      simp
    rw [e]
    have g0 := (h0.comp hV).sub_const c.re
    have g1 := (h1.comp hV).sub_const c.imI
    have g2 := (h2.comp hV).sub_const c.imJ
    have g3 := (h3.comp hV).sub_const c.imK
    exact (((g0.pow_const 2).add (g1.pow_const 2)).add (g2.pow_const 2)).add (g3.pow_const 2) |>.sqrt
  have hc' : ContinuousOn (fun u => Real.exp (-R.barrierFn u)) (Set.Ico 0 R.ballRadius) :=
    Real.continuous_exp.comp_continuousOn hp.smooth.continuousOn.neg
  have hg : Measurable ((Set.Ico 0 R.ballRadius).piecewise (fun u => Real.exp (-R.barrierFn u))
      fun _ => (0 : ℝ)) :=
    hc'.measurable_piecewise continuousOn_const measurableSet_Ico
  have e : (fun W : TorusField (n * R.params.side) => bondMark R V W b) = fun W =>
      ((Set.Ico 0 R.ballRadius).piecewise (fun u => Real.exp (-R.barrierFn u)) fun _ => (0 : ℝ))
        ‖((chartCoord R.params V W b : imaginaryQuaternions) : ℍ[ℝ]) - c‖ := by
    funext W
    unfold bondMark cutoffFactor
    by_cases h : ‖((chartCoord R.params V W b : imaginaryQuaternions) : ℍ[ℝ]) - c‖ < R.ballRadius
    · rw [if_pos h, Set.piecewise_eq_of_mem _ _ _ (show _ ∈ Set.Ico 0 R.ballRadius from ⟨norm_nonneg _, h⟩)]
    · rw [if_neg h, Set.piecewise_eq_of_notMem _ _ _ (fun hm => h hm.2)]
  rw [e]
  exact hg.comp hu
theorem measurable_supportMarks (hC : ChartCoordMeasurable) (hp : IsCutoff R.ballRadius R.barrierFn)
    (θ : GasSupport R n) : Measurable (G.supportMarks θ) := by
  classical
  unfold GasGround.supportMarks
  refine Finset.measurable_prod _ fun b _ => ?_
  by_cases h : b ∈ θ.1
  · simp only [if_pos h]
    exact measurable_const.sub (measurable_bondMark hC hp G.coarse b)
  · simp only [if_neg h]
    exact measurable_bondMark hC hp G.coarse b
theorem measurable_baseUniformWeight (hK : BondKernelBorel) (b : BaseChoice R.params.side n) (y : TorusSite n) :
    Measurable fun W : TorusField (n * R.params.side) => baseUniformWeight W b y := by
  classical
  have hsets := (hK R.params R.coupling n).2.2.2.1
  intro S _
  have : (fun W : TorusField (n * R.params.side) => baseUniformWeight W b y) ⁻¹' S =
      ⋃ A ∈ {A | ∃ W : TorusField (n * R.params.side),
          baseChoices R.params (fineLevelField R.params n W) = A ∧ baseUniformWeight W b y ∈ S},
        {W | baseChoices R.params (fineLevelField R.params n W) = A} := by
    ext W
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro h
      exact ⟨_, ⟨W, rfl, h⟩, rfl⟩
    · rintro ⟨A, ⟨W₀, hW₀, h₀⟩, hW⟩
      have hs : baseUniformWeight W b y = baseUniformWeight W₀ b y := by
        unfold baseUniformWeight
        have e : baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) =
            baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W₀) :=
          hW.trans hW₀.symm
        rw [e]
      rwa [hs]
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun A _ => hsets A
theorem measurable_baseWeightProd (hK : BondKernelBorel) (θ : GasSupport R n) (o : θ.core → BlockOffset R.params.side) :
    Measurable fun a : θ.coreBonds → UnitQuaternion =>
      ∏ y ∈ θ.core, baseUniformWeight (singleField G θ a) (singleBases G θ o) y := by
  refine Finset.measurable_prod _ fun y _ => ?_
  have h := measurable_baseUniformWeight (R := R) hK (singleBases G θ o) y
  exact h.comp (continuous_singleField G θ).measurable
def baseWeightProd (θ : GasSupport R n)
    (q : (θ.coreBonds → UnitQuaternion) × (θ.core → BlockOffset R.params.side)) : ℝ :=
  ∏ y ∈ θ.core, baseUniformWeight (singleField G θ q.1) (singleBases G θ q.2) y
theorem measurable_baseWeightProd_pair (hK : BondKernelBorel) (θ : GasSupport R n) :
    Measurable (baseWeightProd G θ) :=
  measurable_from_prod_countable_left (measurable_baseWeightProd G hK θ)
theorem measurable_activity (hC : ChartCoordMeasurable) (hK : BondKernelBorel)
    (hrow : R.HasExpansions) (hp : IsCutoff R.ballRadius R.barrierFn)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) (θ : GasSupport R n) :
    Measurable fun s : SupportState θ => G.activity θ s := by
  classical
  obtain ⟨-, hΦ, -⟩ := hrow.2.borel (n * R.params.side) hside (singleSites G θ)
  have hf : Measurable fun s : SupportState θ => singleField G θ s.1 :=
    (continuous_singleField G θ).measurable.comp measurable_fst
  have hl : Measurable fun s : SupportState θ => singleLabelling G θ s.2.1 :=
    (measurable_singleLabelling G θ).comp (measurable_fst.comp measurable_snd)
  have h1 : Measurable fun s : SupportState θ => G.supportMarks θ (singleField G θ s.1) :=
    (measurable_supportMarks G hC hp θ).comp hf
  have h2 : Measurable fun s : SupportState θ =>
      ∏ X ∈ chainComponents R.range θ.2,
        R.clusterFactor (n * R.params.side) (singleField G θ s.1) (singleSites G θ) (singleLabelling G θ s.2.1) X :=
    Finset.measurable_prod _ fun X _ => (hΦ X).comp (hf.prodMk hl)
  have hq : Measurable fun s : SupportState θ =>
      ((s.1, s.2.2) : (θ.coreBonds → UnitQuaternion) × (θ.core → BlockOffset R.params.side)) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have h3 : Measurable fun s : SupportState θ => baseWeightProd G θ (s.1, s.2.2) :=
    (measurable_baseWeightProd_pair G hK θ).comp hq
  have e : (fun s : SupportState θ => G.activity θ s) = fun s => G.supportMarks θ (singleField G θ s.1) *
      (∏ X ∈ chainComponents R.range θ.2,
        R.clusterFactor (n * R.params.side) (singleField G θ s.1) (singleSites G θ) (singleLabelling G θ s.2.1) X) *
      baseWeightProd G θ (s.1, s.2.2) := funext (activity_eq G)
  rw [e]
  exact (h1.mul h2).mul h3
end ActivityMeasurable
theorem activityIsMeasurable_proof (hC : ChartCoordMeasurable) (hK : BondKernelBorel) :
    ActivityIsMeasurable := by
  intro R _ hrow hp n _ G i hG
  have hside : IsBlockTorusSide R.params (n * R.params.side) := by
    refine ⟨Dvd.intro_left n rfl, ?_⟩
    have hL : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
    rcases hG with hc | hh
    · rw [Nat.mul_comm]
      exact Nat.mul_le_mul_right _ hc.n₀_le
    · exact hh.isBlockSide.2.trans (Nat.le_mul_of_pos_right _ hL)
  exact (ActivityMeasurable.measurable_activity G hC hK hrow hp hside i.1).comp measurable_subtype_coe
end StepGas
end YangMills.Construction
end
