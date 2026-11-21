import YangMills.Construction.ClusterExpansionOfAStep.WeightOfTheGasIsBorelProof
import YangMills.Construction.ResponseInTheExpansion.GasIntegrandIsBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open Dobrushin ClusterExpansionOfAStep StepSettings StepGas StepCosts RenormalizationStepParameters TorusFields TorusLumps BlockAverages LumpContours
  ColdStepAtMirrorFrames
namespace GasIntegrand
private theorem measurable_of_countable_cover {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable ι]
    {f : α → β} (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i)) (hcov : ∀ a, ∃ i, a ∈ A i)
    (hf : ∀ i, Measurable fun a : A i => f a) : Measurable f := by exact _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurable_of_iUnion_cover (ι := ι) A hA hcov hf
variable {n : ℕ}
private theorem measurable_gaugeAt {R : StepSetup} (x : TorusSite (n * R.params.side)) :
    Measurable fun W : TorusField (n * R.params.side) => gaugeAt (R := R) W x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurable_gaugeAt <;> assumption
variable {R : StepSetup}
private abbrev mkSetting (V : TorusField n) (top : Finset (TorusSite n))
    (Yt : Finset (TorusSite (n * R.params.side))) (free bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) (base : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) :
    ChartSetting R n :=
  ⟨V, top, base, Yt, ω, b, free, bad⟩
private theorem eq_mkSetting (s : ChartSetting R n) {Y : Finset (TorusSite (n * R.params.side))}
    {F Bd : Finset (TorusBond (n * R.params.side))} {b : BaseChoice R.params.side n} (hY : s.support = Y)
    (hF : s.free = F) (hBd : s.bad = Bd) (hb : s.bases = b) :
    s = mkSetting s.coarse s.region Y F Bd b s.fine (fun z => s.labelling ⟨z.1, hY ▸ z.2⟩) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.eq_settingOfParts <;> assumption
section Family
variable {X : Type*} [MeasurableSpace X] (V : TorusField n) (top : Finset (TorusSite n))
  (Yt : Finset (TorusSite (n * R.params.side))) (free bad : Finset (TorusBond (n * R.params.side)))
  (b : BaseChoice R.params.side n)
private theorem measurable_field_prod (base : X → TorusField (n * R.params.side)) (ω : X → Yt → R.labels.Ω)
    (hb : Measurable base) :
    Measurable fun p : X × FreeCoords free => (mkSetting V top Yt free bad b (base p.1) (ω p.1)).field p.2 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurable_field_prod <;> assumption
end Family
section WilsonWeightSeriesExpansion
variable [NeZero n]
private theorem sum_sitesInBlocks (L : ℕ) [NeZero L] (f : TorusSite (n * L) → ℝ) :
    ∑ Y : TorusSite n, ∑ y ∈ sitesInBlocks L {Y}, f y = ∑ y, f y := by apply _root_.YangMills.Construction.FreeBonds.sum_sitesInBlocks_singleton <;> assumption
private theorem sum_levelShare (hS : SharesSumToAction) (a : ℝ) (L t m : ℕ) [NeZero m]
    (S : Finset (TorusSite m)) (W : TorusField m) (ha : 0 ≤ a) (hL : 0 < L) (hm : 2 ≤ m) :
    ∑ y, levelShare a L t S y W = actionAtLevel a L t S W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.sum_levelShare <;> assumption
private def fitEnergy (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (W : TorusField (n * ℓ.side)) (V : TorusField n)
    (b : BaseChoice ℓ.side n) : ℝ :=
  ∑ Y : TorusSite n, ℓ.coupling / 2 *
    ∑ i : Fin 4, (bondFit ℓ W V b (Y, i) + bondFit ℓ W V b (Y - TorusFields.unitStep n i, i))
private theorem exp_neg_potential_eq
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0) (hS : SharesSumToAction)
    (ha : 0 ≤ R.params.coupling) (hL : 0 < R.params.side) (hm : 2 ≤ n * R.params.side) (s : ChartSetting R n)
    (η : FreeCoords s.free) (hh : IsHullState R.params R.range (s.field η) s.support)
    (hΦ : ∀ X ∈ chainComponents R.range s.support,
      R.clusterFactor (n * R.params.side) (s.field η) s.support s.labelling X ≠ 0) :
    Real.exp (-s.potential η) =
      R.labelWeight (n * R.params.side) (s.field η) s.support s.labelling /
          (R.functional (n * R.params.side) (trivialField _) *
            ∏ X ∈ chainComponents R.range s.support,
              R.clusterFactor (n * R.params.side) (s.field η) s.support s.labelling X) *
        Real.exp (-(R.coupling * fitEnergy R.params (s.field η) s.coarse s.bases) +
          ∑ Y : TorusSite n, s.logJacobian (s.field η) η Y) :=
  _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.exp_neg_potential
    hr hside hflat hS ha hL hm s η hh hΦ
private theorem measurable_haarLogDensity : Measurable haarLogDensity := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.measurable_haarLogDensity <;> assumption
private theorem measurable_bondFit (hM : MeasurableContourMeanStatement) (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (V : TorusField n)
    (b : BaseChoice ℓ.side n) (c : TorusBond n) : Measurable fun W : TorusField (n * ℓ.side) => bondFit ℓ W V b c := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurable_bondFit <;> assumption
private theorem measurable_meanNorm (hM : MeasurableContourMeanStatement) (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters)
    (b : BaseChoice ℓ.side n) (c : TorusBond n) : Measurable fun W : TorusField (n * ℓ.side) => meanNorm ℓ W b c :=
  hM ℓ n b (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) (fun q => ‖q‖) continuous_norm
private theorem measurable_fitEnergy (hM : MeasurableContourMeanStatement) (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (V : TorusField n)
    (b : BaseChoice ℓ.side n) : Measurable fun W : TorusField (n * ℓ.side) => fitEnergy ℓ W V b := by
  unfold fitEnergy
  refine Finset.measurable_sum _ fun Y _ => measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
  exact (measurable_bondFit hM ℓ V b _).add (measurable_bondFit hM ℓ V b _)
end WilsonWeightSeriesExpansion
section Mass
variable [NeZero n] {X : Type*} [MeasurableSpace X] (V : TorusField n) (top : Finset (TorusSite n))
  (Yt : Finset (TorusSite (n * R.params.side))) (free bad : Finset (TorusBond (n * R.params.side)))
  (b : BaseChoice R.params.side n)
private def logJacobianSum (W : TorusField (n * R.params.side)) (η : FreeCoords free) : ℝ :=
  open Classical in
  ∑ Y : TorusSite n, (∑ i : Fin 4, logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params W b (Y, i)) +
    ∑ e : free, if bondBlock (R := R) e.1 = Y then
      Real.log (haarLogDensity (toCoords (frameCoord R.params R.anchorRadius R.depth R.frameReach V e.1) + η e))
    else 0)
private def guardedLabelWeight (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) : ℝ :=
  open Classical in
  if IsHullState R.params (clusterRange R.coupling) W Yt then R.labelWeight (n * R.params.side) W Yt ω else 0
private def densityFormula (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) (η : FreeCoords free) : ℝ :=
  (∏ e : free, cutoffFactor R.ballRadius R.barrierFn (coordNorm (η e))) *
    ((guardedLabelWeight Yt W ω /
      (R.functional (n * R.params.side) (trivialField _) *
        ∏ Z ∈ chainComponents R.range Yt, R.clusterFactor (n * R.params.side) W Yt ω Z)) *
        Real.exp (-(R.coupling * fitEnergy R.params W V b) + logJacobianSum V free b W η))
private theorem measurable_logJacobianSum (hM : MeasurableContourMeanStatement)
    (W : X × FreeCoords free → TorusField (n * R.params.side)) (hW : Measurable W) :
    Measurable fun p => logJacobianSum V free b (W p) p.2 := by
  classical
  unfold logJacobianSum
  refine Finset.measurable_sum _ fun Y _ => ?_
  refine (Finset.measurable_sum _ fun i _ => ?_).add (Finset.measurable_sum _ fun e _ => ?_)
  · exact measurable_logPartitionGap.comp (measurable_const.mul ((measurable_meanNorm hM R.params b _).comp hW))
  · by_cases hY : bondBlock (R := R) e.1 = Y
    · simp only [if_pos hY]
      have h1 : Measurable fun p : X × FreeCoords free =>
          toCoords (frameCoord R.params R.anchorRadius R.depth R.frameReach V e.1) + p.2 e :=
        measurable_const.add ((measurable_pi_apply e).comp measurable_snd)
      exact Real.measurable_log.comp (measurable_haarLogDensity.comp h1)
    · simp only [if_neg hY]
      exact measurable_const
private theorem measurable_densityFormula
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) (hM : MeasurableContourMeanStatement)
    (hp : IsCutoff R.ballRadius R.barrierFn) (W : X × FreeCoords free → TorusField (n * R.params.side))
    (ω : X → Yt → R.labels.Ω) (hW : Measurable W) (hω : Measurable ω) :
    Measurable fun p => densityFormula V Yt free b (W p) (ω p.1) p.2 := by
  classical
  have hWω : Measurable fun p : X × FreeCoords free => (W p, ω p.1) := hW.prodMk (hω.comp measurable_fst)
  obtain ⟨bD, bΦ, -⟩ := hr.borel (n * R.params.side) hside Yt
  have h0 : Measurable fun p : X × FreeCoords free =>
      ∏ e : free, cutoffFactor R.ballRadius R.barrierFn (coordNorm (p.2 e)) :=
    Finset.measurable_prod _ fun e _ =>
      (measurable_cutoffFactor_coordNorm hp).comp ((measurable_pi_apply e).comp measurable_snd)
  have hg : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      guardedLabelWeight Yt p.1 p.2 := bD
  have h1' := hg.comp hWω
  have h1 : Measurable fun p : X × FreeCoords free => guardedLabelWeight Yt (W p) (ω p.1) := h1'
  have h2 : Measurable fun p : X × FreeCoords free =>
      R.functional (n * R.params.side) (trivialField _) *
        ∏ Z ∈ chainComponents R.range Yt, R.clusterFactor (n * R.params.side) (W p) Yt (ω p.1) Z :=
    measurable_const.mul (Finset.measurable_prod _ fun Z _ => (bΦ Z).comp hWω)
  have h3 : Measurable fun p : X × FreeCoords free =>
      Real.exp (-(R.coupling * fitEnergy R.params (W p) V b) + logJacobianSum V free b (W p) p.2) :=
    Real.measurable_exp.comp (((measurable_const.mul ((measurable_fitEnergy hM R.params V b).comp hW)).neg).add
      (measurable_logJacobianSum V free b hM W hW))
  unfold densityFormula
  exact h0.mul ((h1.div h2).mul h3)
private theorem cutoffProduct_mul_exp_eq
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0) (hS : SharesSumToAction)
    (ha : 0 ≤ R.params.coupling) (hL : 0 < R.params.side) (hm : 2 ≤ n * R.params.side)
    (base : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω)
    (hs : (mkSetting V top Yt free bad b base ω).IsAdmissible) (η : FreeCoords free) :
    (mkSetting V top Yt free bad b base ω).cutoffProduct η *
        Real.exp (-(mkSetting V top Yt free bad b base ω).potential η) =
      densityFormula V Yt free b ((mkSetting V top Yt free bad b base ω).field η) ω η := by
  classical
  unfold densityFormula
  by_cases hη : (mkSetting V top Yt free bad b base ω).InBalls η
  · have hh := hs.isHull η hη
    have hΦ := hs.factor_ne_zero η hη
    rw [exp_neg_potential_eq hr hside hflat hS ha hL hm (mkSetting V top Yt free bad b base ω) η hh hΦ]
    have hh' : IsHullState R.params (clusterRange R.coupling)
        ((mkSetting V top Yt free bad b base ω).field η) Yt := hh
    have hg : guardedLabelWeight Yt ((mkSetting V top Yt free bad b base ω).field η) ω =
        R.labelWeight (n * R.params.side) ((mkSetting V top Yt free bad b base ω).field η) Yt ω := if_pos hh'
    rw [hg]
    rfl
  · have hz : (∏ e : free, cutoffFactor R.ballRadius R.barrierFn (coordNorm (η e))) = 0 := by
      simp only [ChartSetting.InBalls, not_forall, not_le] at hη
      obtain ⟨e, he⟩ := hη
      refine Finset.prod_eq_zero (Finset.mem_univ e) ?_
      unfold cutoffFactor
      exact if_neg (not_lt.mpr he.le)
    have hz' : (mkSetting V top Yt free bad b base ω).cutoffProduct η = 0 := hz
    rw [hz', hz, zero_mul, zero_mul]
private theorem measurable_settingIntegral_family
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0) (hS : SharesSumToAction)
    (hM : MeasurableContourMeanStatement) (hp : IsCutoff R.ballRadius R.barrierFn) (ha : 0 ≤ R.params.coupling)
    (hL : 0 < R.params.side) (hm : 2 ≤ n * R.params.side) (F : CaseFunctional R n) (hF : IsCaseFunctional F)
    (bd : Finset (TorusBond (n * R.params.side))) (base : X → TorusField (n * R.params.side))
    (ω : X → Yt → R.labels.Ω) (hb : Measurable base) (hω : Measurable ω)
    (hs : ∀ x, (mkSetting V top Yt free bad b (base x) (ω x)).IsAdmissible) :
    Measurable fun x => (mkSetting V top Yt free bad b (base x) (ω x)).settingIntegral F bd := by
  have hJ := measurable_field_prod V top Yt free bad b base ω hb
  have hD := measurable_densityFormula V Yt free b hr hside hM hp _ ω hJ hω
  have hFm : Measurable fun p : X × FreeCoords free =>
      F ((mkSetting V top Yt free bad b (base p.1) (ω p.1)).field p.2) Yt (ω p.1) bd b :=
    (hF.measurable Yt bd b).comp (hJ.prodMk (hω.comp measurable_fst))
  have e : (fun x => (mkSetting V top Yt free bad b (base x) (ω x)).settingIntegral F bd) = fun x =>
      ∫⁻ η, F ((mkSetting V top Yt free bad b (base x) (ω x)).field η) Yt (ω x) bd b *
        ENNReal.ofReal (densityFormula V Yt free b ((mkSetting V top Yt free bad b (base x) (ω x)).field η) (ω x) η) := by
    funext x
    unfold ChartSetting.settingIntegral
    refine lintegral_congr fun η => ?_
    rw [cutoffProduct_mul_exp_eq V top Yt free bad b hr hside hflat hS ha hL hm _ _ (hs x) η]
  rw [e]
  exact Measurable.lintegral_prod_right' (ν := (volume : Measure (FreeCoords free)))
    (f := fun p : X × FreeCoords free =>
      F ((mkSetting V top Yt free bad b (base p.1) (ω p.1)).field p.2) Yt (ω p.1) bd b *
        ENNReal.ofReal (densityFormula V Yt free b
          ((mkSetting V top Yt free bad b (base p.1) (ω p.1)).field p.2) (ω p.1) p.2))
    (hFm.mul (ENNReal.measurable_ofReal.comp hD))
end Mass
section Gas
variable [NeZero n] {X : Type*} [MeasurableSpace X]
open Classical in
private def sitesOfSet (H : Set (GasSupport R n)) : Finset (TorusSite (n * R.params.side)) :=
  (Finset.univ.filter fun θ => θ ∈ H).biUnion Prod.snd
open Classical in
private def freeBondsUnder (G : GasGround R n) (H : Set (GasSupport R n)) :
    Finset (TorusBond (n * R.params.side)) :=
  G.freeBonds.filter fun e => ¬ ∃ θ : GasSupport R n, θ ∈ H ∧ e ∈ θ.coreBonds
open Classical in
private def badBondsUnder (G : GasGround R n) (H : Set (GasSupport R n)) :
    Finset (TorusBond (n * R.params.side)) :=
  G.recordedBad ∪ (Finset.univ.filter fun θ => θ ∈ H).biUnion Prod.fst ∪
    (chartBonds R.params.side n).filter fun b => parentBlock R.params.side b.1 ∈ G.cut
variable (G : GasGround R n) (γ : X → GasFamily R n) (H : Set (GasSupport R n))
  (hγ : ∀ θ, Measurable fun x => γ x θ) (hH : ∀ x θ, (γ x).Occupies θ ↔ θ ∈ H)
include hγ hH
private theorem measurable_of_chosen {β : Type*} [MeasurableSpace β] (Q : GasSupport R n → Prop)
    (v : ∀ θ : GasSupport R n, SupportState θ → Q θ → β) (hv : ∀ θ (h : Q θ), Measurable fun s => v θ s h)
    (h0 : ∃ θ, θ ∈ H ∧ Q θ) (f : X → β)
    (hf : ∀ x (h : ∃ θ, (γ x).Occupies θ ∧ Q θ),
      f x = v h.choose ((γ x).state h.choose_spec.1) h.choose_spec.2) : Measurable f := by exact _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurable_of_pick (R := R) (n := n) (X := X) γ H hγ hH Q v hv h0 f hf
omit hγ [MeasurableSpace X] in
private theorem fieldAt_eq_inl_iff (x : X) (e : TorusBond (n * R.params.side)) :
    (γ x).fieldAt e = Sum.inl () ↔ ¬ ∃ θ : GasSupport R n, θ ∈ H ∧ e ∈ θ.coreBonds := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.fieldAt_eq_inl_iff <;> assumption
omit hγ [MeasurableSpace X] in
private theorem sites_eq_sitesOfSet (x : X) : (γ x).sites = sitesOfSet H := by
  classical
  ext z
  simp [GasFamily.sites, sitesOfSet, hH]
omit hγ [MeasurableSpace X] in
private theorem support_settingOf_eq (x : X) : (G.settingOf (γ x)).support = G.recordedSites ∪ sitesOfSet H := by
  show G.recordedSites ∪ (γ x).sites = _
  rw [sites_eq_sitesOfSet γ H hH x]
omit hγ [MeasurableSpace X] in
private theorem free_settingOf_eq (x : X) : (G.settingOf (γ x)).free = freeBondsUnder G H := by
  classical
  show G.freeBonds.filter (fun b => (γ x).fieldAt b = Sum.inl ()) = _
  ext e
  simp only [freeBondsUnder, Finset.mem_filter]
  exact and_congr_right fun _ => fieldAt_eq_inl_iff γ H hH x e
omit hγ [MeasurableSpace X] in
private theorem bad_settingOf_eq (x : X) : (G.settingOf (γ x)).bad = badBondsUnder G H := by
  classical
  show G.recordedBad ∪ (Finset.univ.filter fun θ => (γ x).Occupies θ).biUnion Prod.fst ∪
    (chartBonds R.params.side n).filter (fun b => parentBlock R.params.side b.1 ∈ G.cut) = _
  ext e
  simp [badBondsUnder, hH]
private theorem measurable_labelling :
    Measurable fun (x : X) (z : (G.recordedSites ∪ sitesOfSet H : Finset (TorusSite (n * R.params.side)))) =>
      (G.settingOf (γ x)).labelling ⟨z.1, (support_settingOf_eq G γ H hH x).symm ▸ z.2⟩ := by
  classical
  refine measurable_pi_iff.mpr fun z => ?_
  by_cases hz : z.1 ∈ sitesOfSet H
  · have hx : ∀ x, z.1 ∈ (γ x).sites := fun x => by rw [sites_eq_sitesOfSet γ H hH x]; exact hz
    have h0 : ∃ θ : GasSupport R n, θ ∈ H ∧ z.1 ∈ θ.2 := by
      obtain ⟨θ, hθ, hzθ⟩ := Finset.mem_biUnion.mp hz
      exact ⟨θ, (Finset.mem_filter.mp hθ).2, hzθ⟩
    refine measurable_of_chosen γ H hγ hH (fun θ : GasSupport R n => z.1 ∈ θ.2)
      (fun θ s h => s.2.1 ⟨z.1, h⟩) ?_ h0 _ ?_
    · intro θ h
      exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
    · intro x h
      show (if h' : z.1 ∈ (γ x).sites then (γ x).labelAt h' else _) = _
      rw [dif_pos (hx x)]
      rfl
  · have hs : z.1 ∈ G.recordedSites := (Finset.mem_union.mp z.2).resolve_right hz
    have e : ∀ x, (G.settingOf (γ x)).labelling ⟨z.1, (support_settingOf_eq G γ H hH x).symm ▸ z.2⟩ =
        G.recordedLabel ⟨z.1, hs⟩ := by
      intro x
      show (if h' : z.1 ∈ (γ x).sites then (γ x).labelAt h' else _) = _
      rw [dif_neg (fun h' => hz (by rwa [sites_eq_sitesOfSet γ H hH x] at h'))]
    simp only [e]
    exact measurable_const
private theorem measurableSet_bases_eq (b : BaseChoice R.params.side n) :
    MeasurableSet {x | (G.settingOf (γ x)).bases = b} := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurableSet_bases_eq <;> assumption
omit hγ [MeasurableSpace X] in
private theorem settingOf_eq_mkSetting (b : BaseChoice R.params.side n) (x : X) (hb : (G.settingOf (γ x)).bases = b) :
    G.settingOf (γ x) = mkSetting G.coarse G.region (G.recordedSites ∪ sitesOfSet H) (freeBondsUnder G H)
      (badBondsUnder G H) b (G.settingOf (γ x)).fine
      (fun z => (G.settingOf (γ x)).labelling ⟨z.1, (support_settingOf_eq G γ H hH x).symm ▸ z.2⟩) :=
  eq_mkSetting (G.settingOf (γ x)) (support_settingOf_eq G γ H hH x) (free_settingOf_eq G γ H hH x)
    (bad_settingOf_eq G γ H hH x) hb
private theorem measurable_settingOf_fine (b : BaseChoice R.params.side n) (hb : ∀ x, (G.settingOf (γ x)).bases = b) :
    Measurable fun x => (G.settingOf (γ x)).fine := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurable_settingOf_fine <;> assumption
variable (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
    R.clusterFactor R.siteDensity)
  (hside : IsBlockTorusSide R.params (n * R.params.side))
  (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0) (hS : SharesSumToAction)
  (hM : MeasurableContourMeanStatement) (hp : IsCutoff R.ballRadius R.barrierFn) (ha : 0 ≤ R.params.coupling)
  (hL : 0 < R.params.side) (hm : 2 ≤ n * R.params.side)
include hr hside hflat hS hM hp ha hL hm in
private theorem measurable_settingIntegral_gas (F : CaseFunctional R n) (hF : IsCaseFunctional F)
    (bd : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hb : ∀ x, (G.settingOf (γ x)).bases = b) (hs : ∀ x, (G.settingOf (γ x)).IsAdmissible) :
    Measurable fun x => (G.settingOf (γ x)).settingIntegral F bd := by
  have hs' : ∀ x, (mkSetting G.coarse G.region (G.recordedSites ∪ sitesOfSet H) (freeBondsUnder G H)
      (badBondsUnder G H) b (G.settingOf (γ x)).fine
      (fun z => (G.settingOf (γ x)).labelling ⟨z.1, (support_settingOf_eq G γ H hH x).symm ▸ z.2⟩)).IsAdmissible :=
    fun x => (settingOf_eq_mkSetting G γ H hH b x (hb x)) ▸ hs x
  have hm' := measurable_settingIntegral_family G.coarse G.region (G.recordedSites ∪ sitesOfSet H)
    (freeBondsUnder G H) (badBondsUnder G H) b hr hside hflat hS hM hp ha hL hm F hF bd
    (fun x => (G.settingOf (γ x)).fine)
    (fun x z => (G.settingOf (γ x)).labelling ⟨z.1, (support_settingOf_eq G γ H hH x).symm ▸ z.2⟩)
    (measurable_settingOf_fine G γ H hγ hH b hb) (measurable_labelling G γ H hγ hH) hs'
  have e : (fun x => (G.settingOf (γ x)).settingIntegral F bd) = fun x =>
      (mkSetting G.coarse G.region (G.recordedSites ∪ sitesOfSet H) (freeBondsUnder G H) (badBondsUnder G H) b
        (G.settingOf (γ x)).fine
        (fun z => (G.settingOf (γ x)).labelling ⟨z.1, (support_settingOf_eq G γ H hH x).symm ▸ z.2⟩)).settingIntegral
          F bd :=
    funext fun x => congrArg (fun s : ChartSetting R n => s.settingIntegral F bd)
      (settingOf_eq_mkSetting G γ H hH b x (hb x))
  rw [e]
  exact hm'
end Gas
section Top
variable [NeZero n] (G : GasGround R n)
private theorem measurable_familyOf (θ : GasSupport R n) : Measurable fun σ : G.Config => G.familyOf σ θ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurable_familyOf <;> assumption
private theorem measurableSet_isAdmissible : MeasurableSet {σ : G.Config | G.pairConstraint.IsAdmissible σ} := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurableSet_admissible <;> assumption
private theorem measurableSet_occupies (θ : GasSupport R n) :
    MeasurableSet {σ : G.Config | (G.familyOf σ).Occupies θ} := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurableSet_occupies <;> assumption
private def occupancyPiece (H : Set (GasSupport R n)) : Set G.Config :=
  {σ | G.pairConstraint.IsAdmissible σ ∧ ∀ θ, (G.familyOf σ).Occupies θ ↔ θ ∈ H}
private theorem measurableSet_occupancyPiece (H : Set (GasSupport R n)) : MeasurableSet (occupancyPiece G H) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurableSet_occupancyPiece <;> assumption
private theorem countable_baseChoice (L n : ℕ) [NeZero L] [NeZero n] : Countable (BaseChoice L n) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.countable_baseChoice <;> assumption
variable (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
    R.clusterFactor R.siteDensity)
  (hside : IsBlockTorusSide R.params (n * R.params.side))
  (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0) (hS : SharesSumToAction)
  (hM : MeasurableContourMeanStatement) (hp : IsCutoff R.ballRadius R.barrierFn) (ha : 0 ≤ R.params.coupling)
  (hL : 0 < R.params.side) (hm : 2 ≤ n * R.params.side)
  (hset : ∀ σ : G.Config, G.pairConstraint.IsAdmissible σ → (G.settingOf (G.familyOf σ)).IsAdmissible)
include hr hside hflat hS hM hp ha hL hm hset
private theorem measurable_settingIntegral_piece (F : CaseFunctional R n) (hF : IsCaseFunctional F)
    (H : Set (GasSupport R n)) :
    Measurable fun a : occupancyPiece G H =>
      (G.settingOf (G.familyOf a.1)).settingIntegral F (G.badBondsOf a.1) := by
  classical
  have hcount := countable_baseChoice R.params.side n
  have hγ : ∀ θ, Measurable fun a : occupancyPiece G H => G.familyOf a.1 θ := fun θ =>
    (measurable_familyOf G θ).comp measurable_subtype_coe
  have hH : ∀ (a : occupancyPiece G H) θ, (G.familyOf a.1).Occupies θ ↔ θ ∈ H := fun a => a.2.2
  have hbad : ∀ a : occupancyPiece G H,
      G.badBondsOf a.1 = G.recordedBad ∪ (Finset.univ.filter fun θ => θ ∈ H).biUnion Prod.fst := by
    intro a
    unfold GasGround.badBondsOf
    ext e
    simp [hH a]
  simp only [hbad]
  refine measurable_of_countable_cover
    (fun b : BaseChoice R.params.side n => {a : occupancyPiece G H | (G.settingOf (G.familyOf a.1)).bases = b})
    (fun b => measurableSet_bases_eq G (fun a : occupancyPiece G H => G.familyOf a.1) H hγ hH b)
    (fun a => ⟨_, rfl⟩) fun b => ?_
  refine measurable_settingIntegral_gas G
    (fun a : {a : occupancyPiece G H | (G.settingOf (G.familyOf a.1)).bases = b} => G.familyOf a.1.1) H
    (fun θ => (hγ θ).comp measurable_subtype_coe) (fun a => hH a.1) hr hside hflat hS hM hp ha hL hm F hF _ b
    (fun a => a.2) (fun a => hset _ a.1.2.1)
theorem measurable_gasIntegrand_aux (F : CaseFunctional R n) (hF : IsCaseFunctional F) :
    Measurable (G.gasIntegrand F) := by
  classical
  refine measurable_of_countable_cover (ι := Option (Set (GasSupport R n)))
    (fun o => o.elim {σ : G.Config | ¬ G.pairConstraint.IsAdmissible σ} (occupancyPiece G)) ?_ ?_ ?_
  · rintro (_ | H)
    · exact (measurableSet_isAdmissible G).compl
    · exact measurableSet_occupancyPiece G H
  · intro σ
    by_cases h : G.pairConstraint.IsAdmissible σ
    · exact ⟨some {θ | (G.familyOf σ).Occupies θ}, h, fun θ => Iff.rfl⟩
    · exact ⟨none, h⟩
  · rintro (_ | H)
    · have e : (fun a : {σ : G.Config | ¬ G.pairConstraint.IsAdmissible σ} => G.gasIntegrand F a.1) =
          fun _ => 0 :=
        funext fun a => if_neg a.2
      exact e ▸ measurable_const
    · have e : (fun a : occupancyPiece G H => G.gasIntegrand F a.1) = fun a =>
          (G.settingOf (G.familyOf a.1)).settingIntegral F (G.badBondsOf a.1) :=
        funext fun a => if_pos a.2.1
      have h := measurable_settingIntegral_piece G hr hside hflat hS hM hp ha hL hm hset F hF H
      exact e ▸ h
end Top
end GasIntegrand
theorem gasIntegrandMeasurable_proof (hC : GasConfigIsAdmissibleSetting)
    (hM : MeasurableContourMeanStatement) (hS : SharesSumToAction) :
    gasIntegrandMeasurableStatement := by
  intro T hT
  obtain ⟨y₀, hy⟩ := hC T hT
  refine ⟨y₀, fun y hy0 R hR hx n _ G hG F hF => ?_⟩
  have hset := hy y hy0 R hR hx n G hG
  have hrow := hR.isStep.1
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn0 : R.params.n₀ ≤ n := by
    rcases hG with h | h
    · exact h.n₀_le
    · exact le_trans (Nat.le_mul_of_pos_left _ hLpos) h.isBlockSide.2
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn0⟩
  have hn4 : 4096 ≤ R.params.n₀ := by
    rw [hR.params_eq]
    exact hT.n₀_ge
  have hnL : R.params.n₀ ≤ n * R.params.side := le_trans hn0 (Nat.le_mul_of_pos_right _ hLpos)
  have hm : 2 ≤ n * R.params.side := by omega
  have ha : 0 ≤ R.params.coupling := by
    rw [hR.params_eq]
    exact le_trans zero_le_one hT.a_ge
  have hp : IsCutoff R.ballRadius R.barrierFn := by
    have e : R.ballRadius = T.ballRadius := by
      simp only [StepSetup.ballRadius, hR.params_eq, ParameterAssignment.ballRadius, ParameterAssignment.stepParameters]
    rw [e, hR.barrierFn_eq]
    exact hT.cut
  have hσ : 0 < R.params.threshold := by
    rw [hR.params_eq]
    exact hT.σ_pos
  have hcold : IsCold R.params.threshold (trivialField (n * R.params.side)) := by
    intro x μ ν _
    simpa [curvature, holonomy, trivialField] using hσ
  have hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0 :=
    (hrow.1.positive (n * R.params.side) hnL _ hcold).ne'
  exact GasIntegrand.measurable_gasIntegrand_aux G hrow.2 hside hflat hS hM hp ha hLpos hm hset F hF
end WeightedResponses
end YangMills.Construction
end
