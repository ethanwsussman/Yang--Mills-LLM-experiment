import YangMills.Construction.ClusterExpansionOfAStep.CaseOfAStepHasOneState
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfGivenShapes
import YangMills.Construction.ClusterExpansionOfAStep.WeightsOfAStepAreBorel
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open LumpContours TorusFields TorusLumps StepSettings StepCosts BlockPlaces
open BlockAverages hiding unitStep
variable {R : StepSetup} {n : ℕ} [NeZero n]
section Shape
variable (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
  (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
open Classical in
def hullShape (y : TorusSite n) : Option (BlockShape R.params.side) :=
  if y ∈ storedBlocks R.params.side R.range bad Yt C then
    some (decide (y ∈ C), fun q => decide ((blockSite y q.1, q.2) ∈ bad),
      Finset.univ.filter (fun o => blockSite y o ∈ Yt), baseOffset R b y,
      Finset.univ.filter fun q => parentBlock R.params.side
        (blockSite (L := R.params.side) y q.1 + unitStep (n * R.params.side) q.2) ∈
        storedBlocks R.params.side R.range bad Yt C)
  else none
abbrev hullSites : Finset (TorusSite n) := coarseHull R.params.side R.range R.nextRange bad Yt C
theorem labelShape_coarseStateOf (W : TorusField (n * R.params.side)) (ωt : Yt → R.labels.Ω)
    (y : hullSites (R := R) C bad Yt) :
    labelShape ((coarseStateOf R C W Yt ωt bad b).2 y) = hullShape (R := R) C bad Yt b y := by
  classical
  simp only [coarseStateOf, hullShape]
  by_cases hy : (y : TorusSite n) ∈ storedBlocks R.params.side R.range bad Yt C
  · simp only [hy, if_true, labelShape, BlockLabels.shape, blockConfigAt, Option.some.injEq,
      Prod.mk.injEq, true_and]
    refine ⟨?_, ?_⟩
    · ext o
      by_cases ho : blockSite (y : TorusSite n) o ∈ Yt <;> simp [ho]
    · ext c
      by_cases hc : parentBlock R.params.side
          (blockSite (L := R.params.side) (y : TorusSite n) c.1 + unitStep (n * R.params.side) c.2) ∈
        storedBlocks R.params.side R.range bad Yt C <;> simp [hc]
  · simp only [hy, if_false, labelShape]
abbrev hullShapes : hullSites (R := R) C bad Yt → Option (BlockShape R.params.side) :=
  fun y => hullShape (R := R) C bad Yt b y
theorem coarseStateOf_shapeState
    (p : ShapeLabelData R.labels.Ω (hullShapes (R := R) C bad Yt b) ×
      ShapeLinkData (hullShapes (R := R) C bad Yt b))
    (hsh : ∀ y, labelShape (labelsOfShapes (hullShapes (R := R) C bad Yt b) p y) =
      hullShapes (R := R) C bad Yt b y)
    (W : TorusField (n * R.params.side))
    (ν : (shapeState (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p).unlabelled Yt →
      R.labels.Ω) :
    coarseStateOf R C
      ((shapeState (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p).fieldWithStoredLinks W) Yt
      ((shapeState (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p).fillLabels Yt ν) bad b =
      shapeState (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p := by
  classical
  refine congrArg (Sigma.mk (hullSites (R := R) C bad Yt)) (funext fun y => ?_)
  by_cases hy : (y : TorusSite n) ∈ storedBlocks R.params.side R.range bad Yt C
  · rw [if_pos hy]
    rcases labelOfShape_cases (hullShapes (R := R) C bad Yt b y)
        (fun o => p.1 ⟨y, o⟩, fun c => p.2 ⟨y, c⟩) with ⟨h1, h2⟩ | ⟨s, h1, h2⟩
    · simp only [hullShapes, hullShape, if_pos hy] at h1
      cases h1
    · have h1' : labelsOfShapes (hullShapes (R := R) C bad Yt b) p y = Sum.inr s := h1
      rw [h1']
      congr 1
      have hs := hsh y
      rw [h1'] at hs
      simp only [labelShape, hullShapes, hullShape, if_pos hy, Option.some.injEq] at hs
      have hst : (shapeState (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p).markAt y =
          some s :=
        markAt_of_inr (q := (shapeState (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p))
          y.2 h1'
      have e1 : s.isCore = decide ((y : TorusSite n) ∈ C) := congrArg Prod.fst hs
      have e2 := congrArg (fun t : BlockShape R.params.side => t.2.1) hs
      have e3 := congrArg (fun t : BlockShape R.params.side => t.2.2.1) hs
      have e4 := congrArg (fun t : BlockShape R.params.side => t.2.2.2.1) hs
      have e5 := congrArg (fun t : BlockShape R.params.side => t.2.2.2.2) hs
      refine blockConfig_ext e1.symm e2.symm ?_ e4.symm ?_
      · funext o
        have ho : s.siteLabel o ≠ Sum.inl () ↔ blockSite (y : TorusSite n) o ∈ Yt := by
          have := Finset.ext_iff.mp e3 o
          simpa [BlockLabels.shape] using this
        simp only [blockConfigAt]
        by_cases h : blockSite (y : TorusSite n) o ∈ Yt
        · rw [dif_pos h]
          have hz : blockSite (y : TorusSite n) o ∈
              (shapeState (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p).labelSet :=
            mem_labelSet.mpr (by rw [labelAt_blockSite hst]; exact ho.mpr h)
          rw [fillLabels_of_mem (shapeState (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p)
            Yt ν _ h hz]
          have h3 := labelAt_eq_inr_labeling
            (shapeState (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p) ⟨_, hz⟩
          simp only at h3
          rw [labelAt_blockSite hst] at h3
          exact h3.symm
        · rw [dif_neg h]
          by_contra h3
          exact h (ho.mp fun h4 => h3 h4.symm)
      · funext c
        have hc : s.linkValue c ≠ Sum.inl () ↔
            parentBlock R.params.side
              (blockSite (L := R.params.side) (y : TorusSite n) c.1 + unitStep (n * R.params.side) c.2) ∈
              storedBlocks R.params.side R.range bad Yt C := by
          have := Finset.ext_iff.mp e5 c
          simpa [BlockLabels.shape] using this
        simp only [blockConfigAt]
        by_cases h : parentBlock R.params.side
            (blockSite (L := R.params.side) (y : TorusSite n) c.1 + unitStep (n * R.params.side) c.2) ∈
            storedBlocks R.params.side R.range bad Yt C
        · rw [if_pos h]
          rcases hg : s.linkValue c with ⟨⟩ | g
          · exact absurd hg (hc.mpr h)
          · simp only [CoarseState.fieldWithStoredLinks]
            rw [parentBlock_blockSite, hst]
            simp [siteOffset_blockSite, hg]
        · rw [if_neg h]
          by_contra h3
          exact h (hc.mp fun h4 => h3 h4.symm)
  · rw [if_neg hy]
    have hs := hsh y
    have hn : hullShapes (R := R) C bad Yt b y = none := by
      simp only [hullShapes, hullShape, if_neg hy]
    rw [hn] at hs
    rcases hl : labelsOfShapes (hullShapes (R := R) C bad Yt b) p y with ⟨⟩ | s
    · rfl
    · rw [hl] at hs
      cases hs
end Shape
section Inner
variable (C : Finset (TorusSite n)) (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side)))
  (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
def partialWeightIntegral (A : Finset (TorusSite (n * R.params.side))) (S : Finset (TorusBond (n * R.params.side)))
    (r : (A → R.labels.Ω) × (S → UnitQuaternion)) : ENNReal :=
  ∫⁻ W, ∫⁻ ν : (Yt \ A : Finset _) → R.labels.Ω,
    configurationWeight R C V bad Yt b (overwriteBonds S (r.2, W)) (joinOnSubset Yt A (r.1, ν))
    ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
theorem fieldWithStoredLinks_shapeState_eq_overwriteBonds (Y : Finset (TorusSite n))
    (σ : Y → Option (BlockShape R.params.side))
    (p : ShapeLabelData R.labels.Ω σ × ShapeLinkData σ) (W : TorusField (n * R.params.side)) :
    (shapeState Y σ p).fieldWithStoredLinks W =
      overwriteBonds (shapeLinkBonds Y σ) (fun c => p.2 ((shapeLinkEquiv Y σ).symm c), W) := by
  funext x i
  rw [fieldWithStoredLinks_shapeState]
  rfl
theorem fillLabels_shapeState_eq_joinOnSubset (Y : Finset (TorusSite n))
    (σ : Y → Option (BlockShape R.params.side))
    (p : ShapeLabelData R.labels.Ω σ × ShapeLinkData σ) (ν : (shapeState Y σ p).unlabelled Yt → R.labels.Ω)
    (ν' : (Yt \ shapeLabelSites Y σ : Finset _) → R.labels.Ω) (hν : ∀ z hz hz', ν ⟨z, hz⟩ = ν' ⟨z, hz'⟩) :
    (shapeState Y σ p).fillLabels Yt ν =
      joinOnSubset Yt (shapeLabelSites Y σ) (fun z => p.1 ((shapeLabelEquiv Y σ).symm z), ν') := by
  classical
  funext z
  have hS := labelSet_shapeState Y σ p
  by_cases hz : (z : TorusSite (n * R.params.side)) ∈ shapeLabelSites Y σ
  · have hz' : (z : TorusSite (n * R.params.side)) ∈ (shapeState Y σ p).labelSet := hS ▸ hz
    have e : joinOnSubset Yt (shapeLabelSites Y σ) (fun z => p.1 ((shapeLabelEquiv Y σ).symm z), ν') z =
        p.1 ((shapeLabelEquiv Y σ).symm ⟨z, hz⟩) := dif_pos hz
    rw [e]
    obtain ⟨z, hzY⟩ := z
    rw [fillLabels_of_mem (shapeState Y σ p) Yt ν z hzY hz']
    obtain ⟨x, hx⟩ := (shapeLabelEquiv Y σ).surjective ⟨z, hz⟩
    have hz2 : z = blockSite (x.1 : TorusSite n) x.2.1 := (congrArg Subtype.val hx).symm
    subst hz2
    rw [labeling_shapeState Y σ p x hz']
    exact congrArg p.1 ((shapeLabelEquiv Y σ).symm_apply_eq.mpr hx.symm).symm
  · have hr : (z : TorusSite (n * R.params.side)) ∈ (shapeState Y σ p).unlabelled Yt := by
      rw [unlabelled_eq_sdiff, hS]
      exact Finset.mem_sdiff.mpr ⟨z.2, hz⟩
    have e : joinOnSubset Yt (shapeLabelSites Y σ) (fun z => p.1 ((shapeLabelEquiv Y σ).symm z), ν') z =
        ν' ⟨z, Finset.mem_sdiff.mpr ⟨z.2, hz⟩⟩ := dif_neg hz
    rw [e]
    obtain ⟨z, hzY⟩ := z
    rw [fillLabels_of_mem_unlabelled (shapeState Y σ p) Yt ν z hzY hr]
    exact hν z hr _
theorem configurationMass_shapeState
    (p : ShapeLabelData R.labels.Ω (hullShapes (R := R) C bad Yt b) ×
      ShapeLinkData (hullShapes (R := R) C bad Yt b))
    (hsh : ∀ y, labelShape (labelsOfShapes (hullShapes (R := R) C bad Yt b) p y) =
      hullShapes (R := R) C bad Yt b y) :
    configurationMass R C V bad Yt b
        (shapeState (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p) =
      partialWeightIntegral C V bad Yt b
        (shapeLabelSites (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b))
        (shapeLinkBonds (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b))
        (fun z => p.1 ((shapeLabelEquiv _ _).symm z), fun c => p.2 ((shapeLinkEquiv _ _).symm c)) := by
  classical
  unfold configurationMass partialWeightIntegral
  refine lintegral_congr fun W => ?_
  have hf := fieldWithStoredLinks_shapeState_eq_overwriteBonds _ _ p W
  have hr : (shapeState (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p).unlabelled Yt =
      Yt \ shapeLabelSites (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) := by
    rw [unlabelled_eq_sdiff, labelSet_shapeState]
  refine lintegral_pi_congr_finset R.labels.μ hr _ _ fun ν ν' hν => ?_
  have hl := fillLabels_shapeState_eq_joinOnSubset Yt _ _ p ν ν' hν
  have hst := coarseStateOf_shapeState C bad Yt b p hsh W ν
  rw [← hf, ← hl]
  unfold configurationWeight
  by_cases hh : IsHullState R.params R.range
    ((shapeState (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p).fieldWithStoredLinks W) Yt
  · rw [if_pos ⟨hh, hst⟩, if_pos hh]
  · rw [if_neg fun h => hh h.1, if_neg hh]
theorem measurable_partialWeightIntegral
    (hG : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      configurationWeight R C V bad Yt b p.1 p.2) (A : Finset (TorusSite (n * R.params.side))) (hA : A ⊆ Yt)
    (S : Finset (TorusBond (n * R.params.side))) :
    Measurable (partialWeightIntegral (R := R) C V bad Yt b A S) := by
  exact measurable_lintegral_joint (X₁ := A → R.labels.Ω) (X₂ := S → UnitQuaternion)
    (G := configurationWeight R C V bad Yt b) (fieldHaar (n * R.params.side))
    (Measure.pi fun _ : (Yt \ A : Finset _) => R.labels.μ) (measurePreserving_overwriteBonds S).measurable
    (measurePreserving_joinOnSubset Yt A hA R.labels.μ).measurable hG
end Inner
variable (hS : CoarseLabelMeasureByShapes) (hw : ConfigurationWeightMeasurable)
include hS hw
theorem configurationMass_supported_on_coarseHull (hR : R.IsWellPosed) (hn : R.params.n₀ ≤ n)
    (C : Finset (TorusSite n)) (V : TorusField n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    (∀ q : CoarseState R n, q.1 ≠ coarseHull R.params.side R.range R.nextRange bad Yt C →
      configurationMass R C V bad Yt b q = 0) ∧
    Measurable (fun ω => configurationMass R C V bad Yt b
      ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩) ∧
    ∫⁻ ω, configurationMass R C V bad Yt b ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩
        ∂(Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side) =
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ωt
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  classical
  have hh := hS R.labels.Ω R.labels.μ R.params.side
  have hsb : StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side) := hh.2.1 inferInstance
  obtain ⟨hfill, hinj, hrange, hlaw⟩ :=
    hh.2.2.2 (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b)
  have hemb : MeasurableEmbedding (labelsOfShapes (Ω := R.labels.Ω) (hullShapes (R := R) C bad Yt b)) :=
    Measurable.measurableEmbedding hfill hinj
  have hI : MeasurableSet {ω : hullSites (R := R) C bad Yt → CoarseLabel R.labels.Ω R.params.side |
      ∀ y, labelShape (ω y) = hullShapes (R := R) C bad Yt b y} := by
    rw [← hrange]
    exact hemb.measurableSet_range
  have hsh : ∀ p y, labelShape (labelsOfShapes (Ω := R.labels.Ω) (hullShapes (R := R) C bad Yt b) p y) =
      hullShapes (R := R) C bad Yt b y := by
    intro p
    have : labelsOfShapes (Ω := R.labels.Ω) (hullShapes (R := R) C bad Yt b) p ∈
        {ω : hullSites (R := R) C bad Yt → CoarseLabel R.labels.Ω R.params.side |
          ∀ y, labelShape (ω y) = hullShapes (R := R) C bad Yt b y} := by
      rw [← hrange]
      exact mem_range_self p
    exact this
  have hzero : ∀ (q : CoarseState R n), (∀ W ν, ¬ (IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
      coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q)) →
      configurationMass R C V bad Yt b q = 0 := by
    intro q hq
    have h0 : ∀ W, (∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
        (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
            coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q then
          ENNReal.ofReal (stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) else 0)
        ∂(Measure.pi fun _ => R.labels.μ)) = 0 := by
      intro W
      rw [lintegral_congr fun ν => if_neg (hq W ν)]
      simp
    unfold configurationMass
    rw [lintegral_congr h0]
    simp
  have hoff : ∀ ω : hullSites (R := R) C bad Yt → CoarseLabel R.labels.Ω R.params.side,
      ω ∉ {ω : hullSites (R := R) C bad Yt → CoarseLabel R.labels.Ω R.params.side |
        ∀ y, labelShape (ω y) = hullShapes (R := R) C bad Yt b y} →
      configurationMass R C V bad Yt b ⟨hullSites (R := R) C bad Yt, ω⟩ = 0 := by
    intro ω hω
    refine hzero _ fun W ν h => hω ?_
    intro y
    have h3 := eq_of_heq (Sigma.mk.inj h.2).2
    rw [← h3]
    exact labelShape_coarseStateOf C bad Yt b _ _ y
  have hAYt : shapeLabelSites (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) ⊆ Yt := by
    intro z hz
    simp only [shapeLabelSites, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨y, hy, hm⟩ := hz
    by_cases hyz : (y : TorusSite n) ∈ storedBlocks R.params.side R.range bad Yt C
    · simp only [hullShapes, hullShape, if_pos hyz, storedOffsets, Finset.mem_filter, Finset.mem_univ,
        true_and] at hm
      rwa [← hy, blockSite_parentBlock_siteOffset] at hm
    · simp only [hullShapes, hullShape, if_neg hyz, storedOffsets] at hm
      exact absurd hm (Finset.notMem_empty _)
  have hG := hw R hR n hn C V bad Yt b
  have hHa := measurable_partialWeightIntegral C V bad Yt b hG _ hAYt
    (shapeLinkBonds (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b))
  have hH : ∀ p, configurationMass R C V bad Yt b
        ⟨hullSites (R := R) C bad Yt, labelsOfShapes (hullShapes (R := R) C bad Yt b) p⟩ =
      partialWeightIntegral C V bad Yt b
        (shapeLabelSites (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b))
        (shapeLinkBonds (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b))
        (fun z => p.1 ((shapeLabelEquiv _ _).symm z), fun c => p.2 ((shapeLinkEquiv _ _).symm c)) :=
    fun p => configurationMass_shapeState C V bad Yt b p (hsh p)
  have hmp1 := measurePreserving_comp_equiv R.labels.μ
    (shapeLabelEquiv (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b)).symm
  have hmp2 := measurePreserving_comp_equiv (haarUnit : Measure UnitQuaternion)
    (shapeLinkEquiv (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b)).symm
  have hmp := hmp1.prod hmp2
  have hext : (fun ω => configurationMass R C V bad Yt b ⟨hullSites (R := R) C bad Yt, ω⟩) =
      Function.extend (labelsOfShapes (Ω := R.labels.Ω) (hullShapes (R := R) C bad Yt b))
        (fun p => partialWeightIntegral C V bad Yt b _ _ (Prod.map (fun a z => a ((shapeLabelEquiv _ _).symm z))
          (fun a c => a ((shapeLinkEquiv _ _).symm c)) p)) 0 := by
    funext ω
    by_cases hω : ω ∈ range (labelsOfShapes (Ω := R.labels.Ω) (hullShapes (R := R) C bad Yt b))
    · obtain ⟨p, rfl⟩ := hω
      rw [hinj.extend_apply]
      exact hH p
    · rw [Function.extend_apply' _ _ _ (by simpa using hω)]
      exact hoff ω (by rwa [← hrange])
  refine ⟨fun q hq => hzero q fun W ν h => hq (by rw [← h.2]; rfl), ?_, ?_⟩
  · show Measurable (fun ω => configurationMass R C V bad Yt b ⟨hullSites (R := R) C bad Yt, ω⟩)
    rw [hext]
    exact hemb.measurable_extend (hHa.comp hmp.measurable) measurable_const
  · have hFm : Measurable (fun ω => configurationMass R C V bad Yt b ⟨hullSites (R := R) C bad Yt, ω⟩) := by
      rw [hext]
      exact hemb.measurable_extend (hHa.comp hmp.measurable) measurable_const
    have hind : (fun ω => configurationMass R C V bad Yt b ⟨hullSites (R := R) C bad Yt, ω⟩) =
        {ω : hullSites (R := R) C bad Yt → CoarseLabel R.labels.Ω R.params.side |
          ∀ y, labelShape (ω y) = hullShapes (R := R) C bad Yt b y}.indicator
          (fun ω => configurationMass R C V bad Yt b ⟨hullSites (R := R) C bad Yt, ω⟩) := by
      funext ω
      by_cases hω : ω ∈ {ω : hullSites (R := R) C bad Yt → CoarseLabel R.labels.Ω R.params.side |
          ∀ y, labelShape (ω y) = hullShapes (R := R) C bad Yt b y}
      · rw [indicator_of_mem hω]
      · rw [indicator_of_notMem hω]
        exact hoff ω hω
    show ∫⁻ ω, configurationMass R C V bad Yt b ⟨hullSites (R := R) C bad Yt, ω⟩ ∂_ = _
    rw [hind, lintegral_indicator hI, hlaw, hemb.lintegral_map]
    have h1 : ∀ p, configurationMass R C V bad Yt b
          ⟨hullSites (R := R) C bad Yt, labelsOfShapes (hullShapes (R := R) C bad Yt b) p⟩ =
        partialWeightIntegral C V bad Yt b _ _ (Prod.map (fun a z => a ((shapeLabelEquiv _ _).symm z))
          (fun a c => a ((shapeLinkEquiv _ _).symm c)) p) := hH
    simp_rw [h1]
    rw [hmp.lintegral_comp hHa]
    exact lintegral_joint (G := configurationWeight R C V bad Yt b)
      (measurePreserving_overwriteBonds
        (shapeLinkBonds (hullSites (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b)))
      (measurePreserving_joinOnSubset Yt _ hAYt R.labels.μ) hG
theorem configurationSupportedOnCoarseHull_holds : ConfigurationSupportedOnCoarseHull := by
  intro R hR n _ hn C V bad Yt b
  exact configurationMass_supported_on_coarseHull hS hw hR hn C V bad Yt b
end YangMills.Construction.ClusterExpansionOfAStep
end
