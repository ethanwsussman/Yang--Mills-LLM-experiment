import YangMills.Construction.ClusterExpansionOfAStep.CaseOfAStepHasOneStateProof
import YangMills.Construction.ResponseInTheExpansion.CasesOfAStepCarryAFunction
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.StepSettings YangMills.Construction.TorusLumps YangMills.Construction.TorusFields YangMills.Construction.BlockPlaces YangMills.Construction.ClusterExpansionOfAStep YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.StepCosts
variable {R : StepSetup} {n : ℕ} [NeZero n]
section Shape
variable (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
  (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
open Classical in
private def blockShapeOf (y : TorusSite n) : Option (BlockShape R.params.side) :=
  if y ∈ storedBlocks R.params.side R.range bad Yt C then
    some (decide (y ∈ C), fun q => decide ((blockSite y q.1, q.2) ∈ bad),
      Finset.univ.filter (fun o => blockSite y o ∈ Yt), baseOffset R b y,
      Finset.univ.filter fun q => parentBlock R.params.side (blockSite (L := R.params.side) y q.1 + TorusFields.unitStep (n * R.params.side) q.2) ∈
        storedBlocks R.params.side R.range bad Yt C)
  else none
private abbrev hullSet : Finset (TorusSite n) := coarseHull R.params.side R.range R.nextRange bad Yt C
private theorem labelShape_coarseStateOf (W : TorusField (n * R.params.side)) (ωt : Yt → R.labels.Ω)
    (y : hullSet (R := R) C bad Yt) :
    labelShape ((coarseStateOf R C W Yt ωt bad b).2 y) = blockShapeOf (R := R) C bad Yt b y := by
  classical
  simp only [coarseStateOf, blockShapeOf]
  by_cases hy : (y : TorusSite n) ∈ storedBlocks R.params.side R.range bad Yt C
  · simp only [hy, if_true, labelShape, BlockLabels.shape, blockConfigAt, Option.some.injEq, Prod.mk.injEq, true_and]
    refine ⟨?_, ?_⟩
    · ext o
      by_cases ho : blockSite (y : TorusSite n) o ∈ Yt <;> simp [ho]
    · ext c
      by_cases hc : parentBlock R.params.side (blockSite (L := R.params.side) (y : TorusSite n) c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈
        storedBlocks R.params.side R.range bad Yt C <;> simp [hc]
  · simp only [hy, if_false, labelShape]
private abbrev hullShapes : hullSet (R := R) C bad Yt → Option (BlockShape R.params.side) :=
  fun y => blockShapeOf (R := R) C bad Yt b y
private theorem coarseStateOf_shapeState (p : ShapeLabelData R.labels.Ω (hullShapes (R := R) C bad Yt b) × ShapeLinkData (hullShapes (R := R) C bad Yt b))
    (hsh : ∀ y, labelShape (labelsOfShapes (hullShapes (R := R) C bad Yt b) p y) = hullShapes (R := R) C bad Yt b y)
    (W : TorusField (n * R.params.side)) (ν : (shapeState (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p).unlabelled Yt → R.labels.Ω) :
    coarseStateOf R C ((shapeState (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p).fieldWithStoredLinks W) Yt
      ((shapeState (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p).fillLabels Yt ν) bad b =
      shapeState (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p := by
  classical
  refine congrArg (Sigma.mk (hullSet (R := R) C bad Yt)) (funext fun y => ?_)
  by_cases hy : (y : TorusSite n) ∈ storedBlocks R.params.side R.range bad Yt C
  · rw [if_pos hy]
    rcases labelOfShape_cases (hullShapes (R := R) C bad Yt b y) (fun o => p.1 ⟨y, o⟩, fun c => p.2 ⟨y, c⟩) with
      ⟨h1, h2⟩ | ⟨s, h1, h2⟩
    · simp only [hullShapes, blockShapeOf, if_pos hy] at h1
      cases h1
    · have h1' : labelsOfShapes (hullShapes (R := R) C bad Yt b) p y = Sum.inr s := h1
      rw [h1']
      congr 1
      have hs := hsh y
      rw [h1'] at hs
      simp only [labelShape, hullShapes, blockShapeOf, if_pos hy, Option.some.injEq] at hs
      have hst : (shapeState (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p).markAt y = some s := markAt_of_inr (q := (shapeState (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p)) y.2 h1'
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
          have hz : blockSite (y : TorusSite n) o ∈ (shapeState (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p).labelSet :=
            mem_labelSet.mpr (by rw [labelAt_blockSite hst]; exact ho.mpr h)
          rw [fillLabels_of_mem (shapeState (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p) Yt ν _ h hz]
          have h3 := labelAt_eq_inr_labeling (shapeState (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p) ⟨_, hz⟩
          simp only at h3
          rw [labelAt_blockSite hst] at h3
          exact h3.symm
        · rw [dif_neg h]
          by_contra h3
          exact h (ho.mp fun h4 => h3 h4.symm)
      · funext c
        have hc : s.linkValue c ≠ Sum.inl () ↔
            parentBlock R.params.side (blockSite (L := R.params.side) (y : TorusSite n) c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈
              storedBlocks R.params.side R.range bad Yt C := by
          have := Finset.ext_iff.mp e5 c
          simpa [BlockLabels.shape] using this
        simp only [blockConfigAt]
        by_cases h : parentBlock R.params.side (blockSite (L := R.params.side) (y : TorusSite n) c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈
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
      simp only [hullShapes, blockShapeOf, if_neg hy]
    rw [hn] at hs
    rcases hl : labelsOfShapes (hullShapes (R := R) C bad Yt b) p y with ⟨⟩ | s
    · rfl
    · rw [hl] at hs
      cases hs
end Shape
section Inner
variable (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
  (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
open Classical in
private def stateMass (G : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal) (q : CoarseState R n) : ENNReal :=
  ∫⁻ W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
      (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧ coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q then
        G (q.fieldWithStoredLinks W) (q.fillLabels Yt ν) else 0)
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
private def heldIntegral (G : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal) (A : Finset (TorusSite (n * R.params.side)))
    (S : Finset (TorusBond (n * R.params.side))) (r : (A → R.labels.Ω) × (S → UnitQuaternion)) : ENNReal :=
  ∫⁻ W, ∫⁻ ν : (Yt \ A : Finset _) → R.labels.Ω,
    G (overwriteBonds S (r.2, W)) (joinOnSubset Yt A (r.1, ν))
    ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
private theorem fieldWithStoredLinks_eq_overwrite (Y : Finset (TorusSite n)) (σ : Y → Option (BlockShape R.params.side))
    (p : ShapeLabelData R.labels.Ω σ × ShapeLinkData σ) (W : TorusField (n * R.params.side)) :
    (shapeState Y σ p).fieldWithStoredLinks W = overwriteBonds (shapeLinkBonds Y σ) (fun c => p.2 ((shapeLinkEquiv Y σ).symm c), W) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.fieldWithStoredLinks_shapeState_eq_overwriteBonds <;> assumption
private theorem fillLabels_eq_join (Y : Finset (TorusSite n)) (σ : Y → Option (BlockShape R.params.side))
    (p : ShapeLabelData R.labels.Ω σ × ShapeLinkData σ) (ν : (shapeState Y σ p).unlabelled Yt → R.labels.Ω)
    (ν' : (Yt \ shapeLabelSites Y σ : Finset _) → R.labels.Ω) (hν : ∀ z hz hz', ν ⟨z, hz⟩ = ν' ⟨z, hz'⟩) :
    (shapeState Y σ p).fillLabels Yt ν =
      joinOnSubset Yt (shapeLabelSites Y σ) (fun z => p.1 ((shapeLabelEquiv Y σ).symm z), ν') := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.fillLabels_shapeState_eq_joinOnSubset <;> assumption
private theorem stateMass_shapeState (G : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal)
    (hoffG : ∀ W ωt, ¬ IsHullState R.params R.range W Yt → G W ωt = 0)
    (p : ShapeLabelData R.labels.Ω (hullShapes (R := R) C bad Yt b) × ShapeLinkData (hullShapes (R := R) C bad Yt b))
    (hsh : ∀ y, labelShape (labelsOfShapes (hullShapes (R := R) C bad Yt b) p y) = hullShapes (R := R) C bad Yt b y) :
    stateMass C bad Yt b G (shapeState (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p) =
      heldIntegral Yt G (shapeLabelSites (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b))
        (shapeLinkBonds (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b))
        (fun z => p.1 ((shapeLabelEquiv _ _).symm z), fun c => p.2 ((shapeLinkEquiv _ _).symm c)) := by
  classical
  unfold stateMass heldIntegral
  refine lintegral_congr fun W => ?_
  have hf := fieldWithStoredLinks_eq_overwrite (R := R) _ _ p W
  have hr : (shapeState (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p).unlabelled Yt =
      Yt \ shapeLabelSites (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) := by
    rw [unlabelled_eq_sdiff, labelSet_shapeState]
  refine lintegral_pi_congr_finset R.labels.μ hr _ _ fun ν ν' hν => ?_
  have hl := fillLabels_eq_join Yt _ _ p ν ν' hν
  have hst := coarseStateOf_shapeState C bad Yt b p hsh W ν
  rw [← hf, ← hl]
  by_cases hh : IsHullState R.params R.range ((shapeState (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) p).fieldWithStoredLinks W) Yt
  · rw [if_pos ⟨hh, hst⟩]
  · rw [if_neg fun h => hh h.1, hoffG _ _ hh]
private theorem measurable_heldIntegral {G : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal}
    (hG : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => G p.1 p.2)
    (A : Finset (TorusSite (n * R.params.side))) (hA : A ⊆ Yt)
    (S : Finset (TorusBond (n * R.params.side))) : Measurable (heldIntegral (R := R) Yt G A S) := by
  exact measurable_lintegral_joint (X₁ := A → R.labels.Ω) (X₂ := S → UnitQuaternion) (G := G) (fieldHaar (n * R.params.side))
    (Measure.pi fun _ : (Yt \ A : Finset _) => R.labels.μ) (measurePreserving_overwriteBonds S).measurable
    (measurePreserving_joinOnSubset Yt A hA R.labels.μ).measurable hG
private theorem heldIntegral_eq_zero_of {G G' : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal}
    (hG : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => G p.1 p.2)
    (hz : ∀ W ωt, G W ωt = 0 → G' W ωt = 0) (A : Finset (TorusSite (n * R.params.side))) (hA : A ⊆ Yt)
    (S : Finset (TorusBond (n * R.params.side))) (r : (A → R.labels.Ω) × (S → UnitQuaternion))
    (h : heldIntegral (R := R) Yt G A S r = 0) :
    heldIntegral (R := R) Yt G' A S r = 0 := by
  have hf := (measurePreserving_overwriteBonds (m := n * R.params.side) S).measurable
  have hu := (measurePreserving_joinOnSubset Yt A hA R.labels.μ).measurable
  have hM : Measurable fun x : TorusField (n * R.params.side) × ((Yt \ A : Finset _) → R.labels.Ω) =>
      G (overwriteBonds S (r.2, x.1)) (joinOnSubset Yt A (r.1, x.2)) :=
    hG.comp ((hf.comp (measurable_const.prodMk measurable_fst)).prodMk
      (hu.comp (measurable_const.prodMk measurable_snd)))
  have hin : Measurable fun W : TorusField (n * R.params.side) => ∫⁻ ν : (Yt \ A : Finset _) → R.labels.Ω,
      G (overwriteBonds S (r.2, W)) (joinOnSubset Yt A (r.1, ν)) ∂(Measure.pi fun _ => R.labels.μ) :=
    hM.lintegral_prod_right'
  unfold heldIntegral at h ⊢
  have h1 := (lintegral_eq_zero_iff hin).mp h
  have h2 : (fun W : TorusField (n * R.params.side) => ∫⁻ ν : (Yt \ A : Finset _) → R.labels.Ω,
      G' (overwriteBonds S (r.2, W)) (joinOnSubset Yt A (r.1, ν)) ∂(Measure.pi fun _ => R.labels.μ)) =ᵐ[fieldHaar (n * R.params.side)]
      fun _ => 0 := by
    filter_upwards [h1] with W hW
    have hMW : Measurable fun ν : (Yt \ A : Finset _) → R.labels.Ω =>
        G (overwriteBonds S (r.2, W)) (joinOnSubset Yt A (r.1, ν)) :=
      hM.comp (measurable_const.prodMk measurable_id)
    have h3 := (lintegral_eq_zero_iff hMW).mp hW
    have h4 : (fun ν : (Yt \ A : Finset _) → R.labels.Ω => G' (overwriteBonds S (r.2, W)) (joinOnSubset Yt A (r.1, ν))) =ᵐ[Measure.pi fun _ => R.labels.μ]
        fun _ => 0 := by
      filter_upwards [h3] with ν hν
      exact hz _ _ hν
    rw [lintegral_congr_ae h4]
    simp
  rw [lintegral_congr_ae h2]
  simp
private theorem stateMass_eq_zero_of_not_reached (G : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal) (q : CoarseState R n)
    (hq : ∀ W ν, ¬ (IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
      coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q)) : stateMass C bad Yt b G q = 0 := by
  classical
  have h0 : ∀ W, (∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
      (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧ coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q then
        G (q.fieldWithStoredLinks W) (q.fillLabels Yt ν) else 0)
      ∂(Measure.pi fun _ => R.labels.μ)) = 0 := by
    intro W
    rw [lintegral_congr fun ν => if_neg (hq W ν)]
    simp
  unfold stateMass
  rw [lintegral_congr h0]
  simp
private theorem stateMass_eq_zero_of_not_shape (G : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal)
    (ω : hullSet (R := R) C bad Yt → CoarseLabel R.labels.Ω R.params.side)
    (hω : ω ∉ {ω : hullSet (R := R) C bad Yt → CoarseLabel R.labels.Ω R.params.side |
      ∀ y, labelShape (ω y) = hullShapes (R := R) C bad Yt b y}) :
    stateMass C bad Yt b G ⟨hullSet (R := R) C bad Yt, ω⟩ = 0 := by
  refine stateMass_eq_zero_of_not_reached C bad Yt b G _ fun W ν h => hω ?_
  intro y
  have h3 := eq_of_heq (Sigma.mk.inj h.2).2
  rw [← h3]
  exact labelShape_coarseStateOf C bad Yt b _ _ y
private theorem shapeLabelSites_subset : shapeLabelSites (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b) ⊆ Yt := by
  classical
  intro z hz
  simp only [shapeLabelSites, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  obtain ⟨y, hy, hm⟩ := hz
  by_cases hyz : (y : TorusSite n) ∈ storedBlocks R.params.side R.range bad Yt C
  · simp only [hullShapes, blockShapeOf, if_pos hyz, storedOffsets, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    rwa [← hy, blockSite_parentBlock_siteOffset] at hm
  · simp only [hullShapes, blockShapeOf, if_neg hyz, storedOffsets] at hm
    exact absurd hm (Finset.notMem_empty _)
variable (hS : CoarseLabelMeasureByShapes)
include hS
private theorem labelShape_labelsOfShapes (p : ShapeLabelData R.labels.Ω (hullShapes (R := R) C bad Yt b) × ShapeLinkData (hullShapes (R := R) C bad Yt b))
    (y : hullSet (R := R) C bad Yt) :
    labelShape (labelsOfShapes (Ω := R.labels.Ω) (hullShapes (R := R) C bad Yt b) p y) = hullShapes (R := R) C bad Yt b y := by
  obtain ⟨hfill, hinj, hrange, hlaw⟩ := (hS R.labels.Ω R.labels.μ R.params.side).2.2.2 (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b)
  have : labelsOfShapes (Ω := R.labels.Ω) (hullShapes (R := R) C bad Yt b) p ∈
      {ω : hullSet (R := R) C bad Yt → CoarseLabel R.labels.Ω R.params.side |
        ∀ y, labelShape (ω y) = hullShapes (R := R) C bad Yt b y} := by
    rw [← hrange]
    exact mem_range_self p
  exact this y
private theorem stateMass_properties {G : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal}
    (hG : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => G p.1 p.2)
    (hoffG : ∀ W ωt, ¬ IsHullState R.params R.range W Yt → G W ωt = 0) :
    (∀ q : CoarseState R n, q.1 ≠ coarseHull R.params.side R.range R.nextRange bad Yt C → stateMass C bad Yt b G q = 0) ∧
    Measurable (fun ω => stateMass C bad Yt b G ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩) ∧
    ∫⁻ ω, stateMass C bad Yt b G ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩
        ∂(Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side) =
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, G W ωt ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  classical
  have hh := hS R.labels.Ω R.labels.μ R.params.side
  have hsb : StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side) := hh.2.1 inferInstance
  obtain ⟨hfill, hinj, hrange, hlaw⟩ := hh.2.2.2 (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b)
  have hemb : MeasurableEmbedding (labelsOfShapes (Ω := R.labels.Ω) (hullShapes (R := R) C bad Yt b)) :=
    Measurable.measurableEmbedding hfill hinj
  have hI : MeasurableSet {ω : hullSet (R := R) C bad Yt → CoarseLabel R.labels.Ω R.params.side |
      ∀ y, labelShape (ω y) = hullShapes (R := R) C bad Yt b y} := by
    rw [← hrange]
    exact hemb.measurableSet_range
  have hsh := labelShape_labelsOfShapes C bad Yt b hS
  have hoff := stateMass_eq_zero_of_not_shape C bad Yt b G
  have hAYt := shapeLabelSites_subset (R := R) C bad Yt b
  have hHa := measurable_heldIntegral (R := R) Yt hG _ hAYt
    (shapeLinkBonds (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b))
  have hH : ∀ p, stateMass C bad Yt b G ⟨hullSet (R := R) C bad Yt, labelsOfShapes (hullShapes (R := R) C bad Yt b) p⟩ =
      heldIntegral Yt G (shapeLabelSites (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b))
        (shapeLinkBonds (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b))
        (fun z => p.1 ((shapeLabelEquiv _ _).symm z), fun c => p.2 ((shapeLinkEquiv _ _).symm c)) :=
    fun p => stateMass_shapeState C bad Yt b G hoffG p (hsh p)
  have hmp1 := measurePreserving_comp_equiv R.labels.μ (shapeLabelEquiv (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b)).symm
  have hmp2 := measurePreserving_comp_equiv (haarUnit : Measure UnitQuaternion)
    (shapeLinkEquiv (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b)).symm
  have hmp := hmp1.prod hmp2
  have hext : (fun ω => stateMass C bad Yt b G ⟨hullSet (R := R) C bad Yt, ω⟩) =
      Function.extend (labelsOfShapes (Ω := R.labels.Ω) (hullShapes (R := R) C bad Yt b))
        (fun p => heldIntegral Yt G _ _ (Prod.map (fun a z => a ((shapeLabelEquiv _ _).symm z))
          (fun a c => a ((shapeLinkEquiv _ _).symm c)) p)) 0 := by
    funext ω
    by_cases hω : ω ∈ range (labelsOfShapes (Ω := R.labels.Ω) (hullShapes (R := R) C bad Yt b))
    · obtain ⟨p, rfl⟩ := hω
      rw [hinj.extend_apply]
      exact hH p
    · rw [Function.extend_apply' _ _ _ (by simpa using hω)]
      exact hoff ω (by rwa [← hrange])
  refine ⟨fun q hq => stateMass_eq_zero_of_not_reached C bad Yt b G q fun W ν h => hq (by rw [← h.2]; rfl), ?_, ?_⟩
  · show Measurable (fun ω => stateMass C bad Yt b G ⟨hullSet (R := R) C bad Yt, ω⟩)
    rw [hext]
    exact hemb.measurable_extend (hHa.comp hmp.measurable) measurable_const
  · have hFm : Measurable (fun ω => stateMass C bad Yt b G ⟨hullSet (R := R) C bad Yt, ω⟩) := by
      rw [hext]
      exact hemb.measurable_extend (hHa.comp hmp.measurable) measurable_const
    have hind : (fun ω => stateMass C bad Yt b G ⟨hullSet (R := R) C bad Yt, ω⟩) =
        {ω : hullSet (R := R) C bad Yt → CoarseLabel R.labels.Ω R.params.side |
          ∀ y, labelShape (ω y) = hullShapes (R := R) C bad Yt b y}.indicator
          (fun ω => stateMass C bad Yt b G ⟨hullSet (R := R) C bad Yt, ω⟩) := by
      funext ω
      by_cases hω : ω ∈ {ω : hullSet (R := R) C bad Yt → CoarseLabel R.labels.Ω R.params.side |
          ∀ y, labelShape (ω y) = hullShapes (R := R) C bad Yt b y}
      · rw [indicator_of_mem hω]
      · rw [indicator_of_notMem hω]
        exact hoff ω hω
    show ∫⁻ ω, stateMass C bad Yt b G ⟨hullSet (R := R) C bad Yt, ω⟩ ∂_ = _
    rw [hind, lintegral_indicator hI, hlaw, hemb.lintegral_map]
    have h1 : ∀ p, stateMass C bad Yt b G ⟨hullSet (R := R) C bad Yt, labelsOfShapes (hullShapes (R := R) C bad Yt b) p⟩ =
        heldIntegral Yt G _ _ (Prod.map (fun a z => a ((shapeLabelEquiv _ _).symm z))
          (fun a c => a ((shapeLinkEquiv _ _).symm c)) p) := hH
    simp_rw [h1]
    rw [hmp.lintegral_comp hHa]
    exact lintegral_joint (G := G)
      (measurePreserving_overwriteBonds (shapeLinkBonds (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b)))
      (measurePreserving_joinOnSubset Yt _ hAYt R.labels.μ) hG
private theorem stateMass_eq_zero_of {G G' : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal}
    (hG : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => G p.1 p.2)
    (hoffG : ∀ W ωt, ¬ IsHullState R.params R.range W Yt → G W ωt = 0)
    (hoffG' : ∀ W ωt, ¬ IsHullState R.params R.range W Yt → G' W ωt = 0)
    (hz : ∀ W ωt, G W ωt = 0 → G' W ωt = 0) (q : CoarseState R n) (h : stateMass C bad Yt b G q = 0) :
    stateMass C bad Yt b G' q = 0 := by
  classical
  obtain ⟨Y, ω⟩ := q
  by_cases hY : Y = hullSet (R := R) C bad Yt
  · subst hY
    obtain ⟨hfill, hinj, hrange, hlaw⟩ := (hS R.labels.Ω R.labels.μ R.params.side).2.2.2 (hullSet (R := R) C bad Yt) (hullShapes (R := R) C bad Yt b)
    by_cases hω : ω ∈ range (labelsOfShapes (Ω := R.labels.Ω) (hullShapes (R := R) C bad Yt b))
    · obtain ⟨p, rfl⟩ := hω
      have hsh := labelShape_labelsOfShapes C bad Yt b hS p
      have h1 := stateMass_shapeState C bad Yt b G hoffG p hsh
      have h2 := stateMass_shapeState C bad Yt b G' hoffG' p hsh
      refine h2.trans (heldIntegral_eq_zero_of Yt hG hz _ (shapeLabelSites_subset (R := R) C bad Yt b) _ _ ?_)
      exact h1.symm.trans h
    · exact stateMass_eq_zero_of_not_shape C bad Yt b G' ω (by rwa [← hrange])
  · exact stateMass_eq_zero_of_not_reached C bad Yt b G' _ fun W ν h => hY (congrArg Sigma.fst h.2).symm
end Inner
theorem configurationMassWithFunction_holds (hS : CoarseLabelMeasureByShapes) (hw : ConfigurationWeightMeasurable) :
    ConfigurationMassWithFunction := by
  classical
  intro R hR n _ hn C V bad Yt b g hg
  have hG₀ := hw R hR n hn C V bad Yt b
  have hG₁ : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      configurationWeight R C V bad Yt b p.1 p.2 * g p.1 p.2 :=
    hG₀.mul hg
  have hoff₀ : ∀ W ωt, ¬ IsHullState R.params R.range W Yt → configurationWeight R C V bad Yt b W ωt = 0 :=
    fun W ωt h => if_neg h
  have hoff₁ : ∀ W ωt, ¬ IsHullState R.params R.range W Yt → configurationWeight R C V bad Yt b W ωt * g W ωt = 0 :=
    fun W ωt h => by
      rw [hoff₀ W ωt h, zero_mul]
  have e₀ : ∀ q, configurationMass R C V bad Yt b q = stateMass C bad Yt b (configurationWeight R C V bad Yt b) q := by
    intro q
    unfold configurationMass stateMass
    refine lintegral_congr fun W => lintegral_congr fun ν => ?_
    by_cases h : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧ coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q
    · rw [if_pos h, if_pos h]
      exact (if_pos h.1).symm
    · rw [if_neg h, if_neg h]
  have e₁ : ∀ q, configurationMassWith R C V bad Yt b g q =
      stateMass C bad Yt b (fun W ωt => configurationWeight R C V bad Yt b W ωt * g W ωt) q := by
    intro q
    unfold configurationMassWith stateMass
    refine lintegral_congr fun W => lintegral_congr fun ν => ?_
    by_cases h : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧ coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q
    · rw [if_pos h, if_pos h]
      congr 1
      exact (if_pos h.1).symm
    · rw [if_neg h, if_neg h]
  obtain ⟨h1, h2, h3⟩ := stateMass_properties C bad Yt b hS hG₁ hoff₁
  refine ⟨fun q hq => (e₁ q).trans (h1 q hq), fun q hq => ?_, ?_, ?_⟩
  · rw [e₁]
    refine stateMass_eq_zero_of C bad Yt b hS hG₀ hoff₀ hoff₁ (fun W ωt h => ?_) q ((e₀ q).symm.trans hq)
    rw [h, zero_mul]
  · simp_rw [e₁]
    exact h2
  · simp_rw [e₁]
    exact h3
end YangMills.Construction.ResponseInTheExpansion
end
