import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesAreBorel
import YangMills.Construction.ClusterExpansionOfAStep.CaseFunctionIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.FactorOfAClassIsBorelProof
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsBorelProof
import YangMills.Construction.ClusterExpansionOfAStep.ZonesOfAFamily
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages hiding unitStep
open ColdStepAtMirrorFrames BlockZones FamilyZones StepSettings StepGas TorusLumps TorusFields
  StepCosts RenormalizationStepParameters StateMeasurability BlockPlaces
namespace CaseIntegrandMeasurability
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem measurable_bondMark (hC : ChartCoordMeasurable) (hp : IsCutoff R.ballRadius R.barrierFn)
    (V : TorusField n) (b : TorusBond (n * R.params.side)) :
    Measurable fun W : TorusField (n * R.params.side) => bondMark R V W b := by apply _root_.YangMills.Construction.StepGas.ActivityMeasurable.measurable_bondMark <;> assumption
theorem measurable_baseLaw (hK : BondKernelBorel) (b : BaseChoice R.params.side n) :
    Measurable fun W : TorusField (n * R.params.side) => baseLaw (R := R) W b := by apply _root_.YangMills.Construction.CoarseMeasurability.measurable_baseLaw <;> assumption
theorem measurableSet_isHullState {m : ℕ} [NeZero m] {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} (hfit : ℓ.Admissible)
    (hLn : ℓ.side ∣ m) (r : ℕ) (Yt : Finset (TorusSite m)) :
    MeasurableSet {W : TorusField m | IsHullState ℓ r W Yt} := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurableSet_isHullState <;> assumption
variable (G : GasGround R n)
open Classical in
theorem coarseStateOf_eq_of_fill {bad : Finset (TorusBond (n * R.params.side))}
    {Yt : Finset (TorusSite (n * R.params.side))} {b : BaseChoice R.params.side n}
    {W W' : TorusField (n * R.params.side)} {ν ν' : G.state.unlabelled Yt → R.labels.Ω}
    (hs : coarseStateOf R G.cut (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b = G.state) :
    coarseStateOf R G.cut (G.state.fieldWithStoredLinks W') Yt (G.state.fillLabels Yt ν') bad b = G.state := by
  have hstore := fun y => (congrArg (fun q => CoarseState.markAt q y) hs).symm.trans
    (markAt_coarseStateOf G.cut (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b y)
  refine Eq.trans (coarseStateOf_congr rfl fun y hy => ?_) hs
  refine blockConfig_ext rfl rfl ?_ rfl ?_
  · funext o
    have hbz : parentBlock R.params.side (blockSite y o) = y := parentBlock_blockSite _ _
    show (if h : blockSite y o ∈ Yt then Sum.inr (G.state.fillLabels Yt ν' ⟨_, h⟩) else Sum.inl ()) =
      if h : blockSite y o ∈ Yt then Sum.inr (G.state.fillLabels Yt ν ⟨_, h⟩) else Sum.inl ()
    by_cases hz : blockSite y o ∈ Yt
    · rw [dif_pos hz, dif_pos hz]
      congr 1
      have hl : G.state.labelAt (blockSite y o) = Sum.inr (G.state.fillLabels Yt ν ⟨_, hz⟩) := by
        unfold CoarseState.labelAt
        rw [hstore, hbz, if_pos hy]
        simp only [blockConfigAt, BlockPlaces.siteOffset_blockSite]
        rw [dif_pos hz]
      rw [fillLabels_of_labelled ν' hz hl]
    · rw [dif_neg hz, dif_neg hz]
  · funext q
    have hbx : parentBlock R.params.side (blockSite (L := R.params.side) y q.1) = y :=
      parentBlock_blockSite _ _
    show (if parentBlock R.params.side (blockSite (L := R.params.side) y q.1 +
          unitStep (n * R.params.side) q.2) ∈ _ then
        Sum.inr (G.state.fieldWithStoredLinks W' (blockSite y q.1) q.2) else Sum.inl ()) =
      if parentBlock R.params.side (blockSite (L := R.params.side) y q.1 +
          unitStep (n * R.params.side) q.2) ∈ _ then
        Sum.inr (G.state.fieldWithStoredLinks W (blockSite y q.1) q.2) else Sum.inl ()
    by_cases hcond : parentBlock R.params.side (blockSite (L := R.params.side) y q.1 +
        unitStep (n * R.params.side) q.2) ∈ storedBlocks R.params.side R.range bad Yt G.cut
    · rw [if_pos hcond, if_pos hcond]
      congr 1
      have key : ∀ W₁ : TorusField (n * R.params.side),
          G.state.fieldWithStoredLinks W₁ (blockSite y q.1) q.2 =
            G.state.fieldWithStoredLinks W (blockSite y q.1) q.2 := by
        intro W₁
        conv_lhs => unfold CoarseState.fieldWithStoredLinks
        rw [hstore, hbx, if_pos hy]
        simp only [blockConfigAt, BlockPlaces.siteOffset_blockSite]
        rw [if_pos hcond]
      exact key W'
    · rw [if_neg hcond, if_neg hcond]
open Classical in
theorem coarseStateOf_eq_iff {bad : Finset (TorusBond (n * R.params.side))}
    {Yt : Finset (TorusSite (n * R.params.side))} {b : BaseChoice R.params.side n}
    {ω : Yt → R.labels.Ω} {W₀ : TorusField (n * R.params.side)}
    (h₀ : coarseStateOf R G.cut W₀ Yt ω bad b = G.state) (W : TorusField (n * R.params.side)) :
    coarseStateOf R G.cut W Yt ω bad b = G.state ↔
      ∀ x i, parentBlock R.params.side x ∈ storedBlocks R.params.side R.range bad Yt G.cut →
        parentBlock R.params.side (x + unitStep (n * R.params.side) i) ∈
          storedBlocks R.params.side R.range bad Yt G.cut → W x i = W₀ x i := by
  constructor
  · intro h x i h1 h2
    have s0 := fun y => (congrArg (fun q => CoarseState.markAt q y) h₀).symm.trans
      (markAt_coarseStateOf G.cut W₀ Yt ω bad b y)
    have s1 := fun y => (congrArg (fun q => CoarseState.markAt q y) h).symm.trans
      (markAt_coarseStateOf G.cut W Yt ω bad b y)
    have e := (s1 (parentBlock R.params.side x)).symm.trans (s0 (parentBlock R.params.side x))
    rw [if_pos h1, if_pos h1] at e
    have e2 := congrArg (fun s => s.linkValue (siteOffset x, i)) (Option.some.inj e)
    simp only [blockConfigAt, BlockPlaces.blockSite_parentBlock_siteOffset] at e2
    rw [if_pos h2, if_pos h2] at e2
    exact Sum.inr.inj e2
  · intro h
    refine Eq.trans (coarseStateOf_congr rfl fun y hy => ?_) h₀
    refine blockConfig_ext rfl rfl rfl rfl ?_
    funext q
    have hbx : parentBlock R.params.side (blockSite (L := R.params.side) y q.1) = y :=
      parentBlock_blockSite _ _
    show (if parentBlock R.params.side (blockSite (L := R.params.side) y q.1 +
          unitStep (n * R.params.side) q.2) ∈ _ then
        Sum.inr (W (blockSite y q.1) q.2) else Sum.inl ()) =
      if parentBlock R.params.side (blockSite (L := R.params.side) y q.1 +
          unitStep (n * R.params.side) q.2) ∈ _ then
        Sum.inr (W₀ (blockSite y q.1) q.2) else Sum.inl ()
    by_cases hcond : parentBlock R.params.side (blockSite (L := R.params.side) y q.1 +
        unitStep (n * R.params.side) q.2) ∈ storedBlocks R.params.side R.range bad Yt G.cut
    · rw [if_pos hcond, if_pos hcond]
      congr 1
      exact h _ _ (by rw [hbx]; exact hy) hcond
    · rw [if_neg hcond, if_neg hcond]
theorem measurable_prod_section {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : α × β → γ} (hf : Measurable f) (b : β) : Measurable fun a => f (a, b) :=
  hf.comp measurable_prodMk_right
theorem measurable_comp_fst {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : α → γ} (hf : Measurable f) : Measurable fun p : α × β => f p.1 :=
  hf.comp measurable_fst
section Pieces
variable {G} (hK : BondKernelBorel) (hC : ChartCoordMeasurable) (hfit : R.params.Admissible)
  (hrow : R.HasExpansions) (hp : IsCutoff R.ballRadius R.barrierFn)
  (hside : IsBlockTorusSide R.params (n * R.params.side))
include hK in
theorem measurable_bondKernel_prod (V : TorusField n) (b : BaseChoice R.params.side n) :
    Measurable fun W : TorusField (n * R.params.side) =>
      ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
          (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c := by
  refine Finset.measurable_prod _ fun c _ => ?_
  obtain ⟨-, -, -, -, -, hk, -⟩ := hK R.params R.coupling n
  exact Measurable.comp (g := fun p : TorusField (n * R.params.side) × TorusField n =>
      bondKernel R.params R.coupling (fineLevelField R.params n p.1) (coarseLevelField R.params n p.2) b c)
    (f := fun W : TorusField (n * R.params.side) => (W, V)) (hk b c) (measurable_id.prodMk measurable_const)
include hC hp in
theorem measurable_remainingMarks (free bad : Finset (TorusBond (n * R.params.side))) :
    Measurable fun W : TorusField (n * R.params.side) => G.remainingMarks free bad W := by
  classical
  unfold GasGround.remainingMarks
  refine Finset.measurable_prod _ fun c _ => ?_
  by_cases hc : c ∈ bad
  · simp only [if_pos hc]
    exact measurable_const.sub (measurable_bondMark hC hp G.coarse c)
  · simp only [if_neg hc]
    exact measurable_bondMark hC hp G.coarse c
include hC hp in
theorem measurable_markProduct (C : Finset (TorusSite n)) (V : TorusField n)
    (bad : Finset (TorusBond (n * R.params.side))) :
    Measurable fun W : TorusField (n * R.params.side) => markProduct R C V W bad := by
  classical
  unfold markProduct
  refine Finset.measurable_prod _ fun c _ => ?_
  by_cases hc : c ∈ bad
  · simp only [if_pos hc]
    exact measurable_const.sub (measurable_bondMark hC hp V c)
  · simp only [if_neg hc]
    exact measurable_bondMark hC hp V c
open Classical in
include hfit in
theorem measurableSet_hull_and_state (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (ω : Yt → R.labels.Ω) : MeasurableSet {W : TorusField (n * R.params.side) |
      IsHullState R.params R.range W Yt ∧ coarseStateOf R G.cut W Yt ω bad b = G.state} := by
  have hh := measurableSet_isHullState hfit
    (Dvd.intro_left n rfl : R.params.side ∣ n * R.params.side) R.range Yt
  by_cases hne : ∃ W₀, coarseStateOf R G.cut W₀ Yt ω bad b = G.state
  · obtain ⟨W₀, h₀⟩ := hne
    have e : {W : TorusField (n * R.params.side) |
        IsHullState R.params R.range W Yt ∧ coarseStateOf R G.cut W Yt ω bad b = G.state} =
        {W : TorusField (n * R.params.side) | IsHullState R.params R.range W Yt} ∩ ⋂ x, ⋂ i,
          {W : TorusField (n * R.params.side) |
            parentBlock R.params.side x ∈ storedBlocks R.params.side R.range bad Yt G.cut →
            parentBlock R.params.side (x + unitStep (n * R.params.side) i) ∈
              storedBlocks R.params.side R.range bad Yt G.cut → W x i = W₀ x i} := by
      ext W
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      exact and_congr Iff.rfl (coarseStateOf_eq_iff G h₀ W)
    rw [e]
    refine hh.inter (MeasurableSet.iInter fun x => MeasurableSet.iInter fun i => ?_)
    by_cases c1 : parentBlock R.params.side x ∈ storedBlocks R.params.side R.range bad Yt G.cut ∧
        parentBlock R.params.side (x + unitStep (n * R.params.side) i) ∈
          storedBlocks R.params.side R.range bad Yt G.cut
    · have e2 : {W : TorusField (n * R.params.side) |
          parentBlock R.params.side x ∈ storedBlocks R.params.side R.range bad Yt G.cut →
          parentBlock R.params.side (x + unitStep (n * R.params.side) i) ∈
            storedBlocks R.params.side R.range bad Yt G.cut → W x i = W₀ x i} =
          (fun W : TorusField (n * R.params.side) => W x i) ⁻¹' {W₀ x i} := by
        ext W
        simp [c1.1, c1.2]
      rw [e2]
      exact ((measurable_pi_apply i).comp (measurable_pi_apply x)) (measurableSet_singleton _)
    · have e2 : {W : TorusField (n * R.params.side) |
          parentBlock R.params.side x ∈ storedBlocks R.params.side R.range bad Yt G.cut →
          parentBlock R.params.side (x + unitStep (n * R.params.side) i) ∈
            storedBlocks R.params.side R.range bad Yt G.cut → W x i = W₀ x i} = Set.univ := by
        ext W
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact fun a b => absurd ⟨a, b⟩ c1
      rw [e2]
      exact MeasurableSet.univ
  · have e : {W : TorusField (n * R.params.side) |
        IsHullState R.params R.range W Yt ∧ coarseStateOf R G.cut W Yt ω bad b = G.state} = ∅ := by
      ext W
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hne ⟨W, h.2⟩
    rw [e]
    exact MeasurableSet.empty
open Classical in
include hK hC hfit hrow hp hside in
theorem measurable_restIntegrand (F : CaseFunctional R n) (hF : IsCaseFunctional F)
    (bad free : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (ν : G.state.unlabelled Yt → R.labels.Ω) :
    Measurable (G.restIntegrand F bad Yt b free ν) := by
  set lab := G.state.fillLabels Yt ν with hlab
  have hD : Measurable fun W : TorusField (n * R.params.side) =>
      if IsHullState R.params R.range W Yt then R.labelWeight (n * R.params.side) W Yt lab else 0 :=
    measurable_prod_section (hrow.2.borel (n * R.params.side) hside Yt).1 lab
  have hFm : Measurable fun W : TorusField (n * R.params.side) => F W Yt lab bad b :=
    measurable_prod_section (hF.measurable Yt bad b) lab
  have hf : Measurable fun W : TorusField (n * R.params.side) => F W Yt lab bad b * ENNReal.ofReal
      ((if IsHullState R.params R.range W Yt then R.labelWeight (n * R.params.side) W Yt lab else 0) *
        baseLaw (R := R) W b *
        (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
          bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
            (readAtLevel (stepBlockFrame R.params.side n) 1 G.coarse) b c) *
        G.remainingMarks free bad W) :=
    hFm.mul (ENNReal.measurable_ofReal.comp (((hD.mul (measurable_baseLaw hK b)).mul
      (measurable_bondKernel_prod hK G.coarse b)).mul (measurable_remainingMarks hC hp free bad)))
  have e : G.restIntegrand F bad Yt b free ν = fun W =>
      if W ∈ {W : TorusField (n * R.params.side) |
          IsHullState R.params R.range W Yt ∧ coarseStateOf R G.cut W Yt lab bad b = G.state} then
        F W Yt lab bad b * ENNReal.ofReal
          ((if IsHullState R.params R.range W Yt then R.labelWeight (n * R.params.side) W Yt lab else 0) *
            baseLaw (R := R) W b *
            (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
              bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
                (readAtLevel (stepBlockFrame R.params.side n) 1 G.coarse) b c) *
            G.remainingMarks free bad W)
      else 0 := by
    funext W
    unfold GasGround.restIntegrand
    by_cases h : IsHullState R.params R.range W Yt ∧ coarseStateOf R G.cut W Yt lab bad b = G.state
    · rw [if_pos h, if_pos (show W ∈ {W : TorusField (n * R.params.side) |
        IsHullState R.params R.range W Yt ∧ coarseStateOf R G.cut W Yt lab bad b = G.state} from h),
        if_pos h.1]
    · rw [if_neg h, if_neg (show W ∉ {W : TorusField (n * R.params.side) |
        IsHullState R.params R.range W Yt ∧ coarseStateOf R G.cut W Yt lab bad b = G.state} from h)]
  rw [e]
  exact Measurable.ite (measurableSet_hull_and_state hfit bad Yt b lab) hf measurable_const
theorem measurable_fillLabels (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable fun ν : G.state.unlabelled Yt → R.labels.Ω => G.state.fillLabels Yt ν := by
  classical
  refine measurable_pi_lambda _ fun z => ?_
  rcases hl : G.state.labelAt z.1 with u | a
  · have hr : z.1 ∈ G.state.unlabelled Yt := Finset.mem_filter.mpr ⟨z.2, hl⟩
    have e : (fun ν : G.state.unlabelled Yt → R.labels.Ω => G.state.fillLabels Yt ν z) =
        fun ν => ν ⟨z.1, hr⟩ :=
      funext fun ν => fillLabels_of_unlabelled ν z.2 hl hr
    rw [e]
    exact measurable_pi_apply _
  · have e : (fun ν : G.state.unlabelled Yt → R.labels.Ω => G.state.fillLabels Yt ν z) = fun _ => a :=
      funext fun ν => fillLabels_of_labelled ν z.2 hl
    rw [e]
    exact measurable_const
theorem measurable_state_fieldWithStoredLinks :
    Measurable fun W : TorusField (n * R.params.side) => G.state.fieldWithStoredLinks W :=
  (measurable_fieldWithStoredLinks G.state.1).comp (measurable_const.prodMk measurable_id)
open Classical in
include hK hC hfit hrow hp hside in
theorem measurable_caseIntegrand (F : CaseFunctional R n) (hF : IsCaseFunctional F)
    (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    Measurable fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
      G.caseIntegrand F bad Yt b p.1 p.2 := by
  have hH := measurableSet_isHullState hfit
    (Dvd.intro_left n rfl : R.params.side ∣ n * R.params.side) R.range Yt
  set h : TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ENNReal := fun p =>
    if p.1 ∈ {W | IsHullState R.params R.range W Yt} then
      F p.1 Yt p.2 bad b * ENNReal.ofReal ((if IsHullState R.params R.range p.1 Yt then
        R.labelWeight (n * R.params.side) p.1 Yt p.2 else 0) *
        baseLaw (R := R) p.1 b * (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
          bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 p.1)
            (readAtLevel (stepBlockFrame R.params.side n) 1 G.coarse) b c) *
        markProduct R G.cut G.coarse p.1 bad) else 0 with hh
  have hhm : Measurable h := by
    refine Measurable.ite (measurable_fst hH)
      ((hF.measurable Yt bad b).mul (ENNReal.measurable_ofReal.comp ?_)) measurable_const
    exact (((hrow.2.borel (n * R.params.side) hside Yt).1.mul
      (measurable_comp_fst (measurable_baseLaw hK b))).mul
      (measurable_comp_fst (measurable_bondKernel_prod hK G.coarse b))).mul
      (measurable_comp_fst (measurable_markProduct hC hp G.cut G.coarse bad))
  have hm : Measurable fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
      (G.state.fieldWithStoredLinks p.1, G.state.fillLabels Yt p.2) :=
    ((measurable_state_fieldWithStoredLinks (G := G)).comp measurable_fst).prodMk
      ((measurable_fillLabels (G := G) Yt).comp measurable_snd)
  by_cases hne : ∃ (W : TorusField (n * R.params.side)) (ν : G.state.unlabelled Yt → R.labels.Ω),
      coarseStateOf R G.cut (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b = G.state
  · obtain ⟨W₀, ν₀, h₀⟩ := hne
    have e : (fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
        G.caseIntegrand F bad Yt b p.1 p.2) =
        h ∘ fun p => (G.state.fieldWithStoredLinks p.1, G.state.fillLabels Yt p.2) := by
      funext p
      have hs := coarseStateOf_eq_of_fill G (W' := p.1) (ν' := p.2) h₀
      unfold GasGround.caseIntegrand
      simp only [Function.comp, hh]
      by_cases hu : IsHullState R.params R.range (G.state.fieldWithStoredLinks p.1) Yt
      · rw [if_pos ⟨hu, hs⟩, if_pos (show G.state.fieldWithStoredLinks p.1 ∈
          {W | IsHullState R.params R.range W Yt} from hu), if_pos hu]
        rfl
      · rw [if_neg fun c => hu c.1, if_neg (show G.state.fieldWithStoredLinks p.1 ∉
          {W | IsHullState R.params R.range W Yt} from hu)]
    rw [e]
    exact hhm.comp hm
  · have e : (fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
        G.caseIntegrand F bad Yt b p.1 p.2) = fun _ => 0 := by
      funext p
      unfold GasGround.caseIntegrand
      rw [if_neg fun c => hne ⟨p.1, p.2, c.2⟩]
    rw [e]
    exact measurable_const
end Pieces
end CaseIntegrandMeasurability
open CaseIntegrandMeasurability in
theorem caseIntegrandMeasurable_of (hK : BondKernelBorel) (hC : ChartCoordMeasurable)
    (hA : AllowedStatesMeasurable) (hFc : ActivityIsMeasurable) : CaseIntegrandMeasurable := by
  classical
  intro T hT
  refine ⟨T.floorMin, fun y hy R hR hx' n _ G hG => ?_⟩
  have hfit : R.params.Admissible := by rw [hR.params_eq]; exact hT.fits y hy
  have eσ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    have e : R.ballRadius = T.ballRadius := by
      show R.params.threshold / 64 = T.threshold / 64
      rw [eσ]
    rw [e, hR.barrierFn_eq]
    exact hT.cut
  have hrow := hR.isStep.1
  have hL1 : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hn₀ : R.params.n₀ ≤ n := by
    rcases hG with h | h
    · exact h.n₀_le
    · exact (Nat.le_mul_of_pos_left _ hL1).trans h.isBlockSide.2
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn₀⟩
  exact ⟨fun F hF bad Yt b =>
      measurable_caseIntegrand (G := G) hK hC hfit hrow hcut hside F hF bad Yt b,
    fun F hF bad free Yt b ν =>
      measurable_restIntegrand (G := G) hK hC hfit hrow hcut hside F hF bad free Yt b ν,
    fun i => ⟨hA R hfit hrow hcut n G i hG, hFc R hfit hrow hcut n G i hG⟩⟩
end YangMills.Construction.ClusterExpansionOfAStep
end
