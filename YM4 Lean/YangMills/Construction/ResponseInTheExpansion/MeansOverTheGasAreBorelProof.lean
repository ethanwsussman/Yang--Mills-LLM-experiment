import YangMills.Construction.ClusterExpansionOfAStep.WeightOfTheGasIsBorelProof
import YangMills.Construction.ClusterExpansionOfAStep.GasDensityOfAGroundIsBorelProof
import YangMills.Construction.ResponseInTheExpansion.DensityOfASettingIsLive
import YangMills.Construction.ResponseInTheExpansion.MeansOverTheGasAreBorel
import YangMills.Construction.ResponseInTheExpansion.TheScoreOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction
open Dobrushin BlockAverages LumpContours ColdStepAtMirrorFrames StepGas StepSettings StepCosts TorusFields TorusLumps
  RenormalizationStepParameters WeightedResponses ClusterExpansionOfAStep
namespace ResponseInTheExpansion
namespace GasMeans
theorem measurable_of_countable_cover {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable ι]
    {f : α → β} (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i)) (hc : ∀ a, ∃ i, a ∈ A i)
    (hf : ∀ i, Measurable fun a : A i => f a) : Measurable f := by exact _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurable_of_iUnion_cover (ι := ι) A hA hc hf
variable {n : ℕ}
theorem measurable_gaugeAt {R : StepSetup} (x : TorusSite (n * R.params.side)) :
    Measurable fun W : TorusField (n * R.params.side) => gaugeAt (R := R) W x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurable_gaugeAt <;> assumption
variable {R : StepSetup}
abbrev assemble (V : TorusField n) (top : Finset (TorusSite n)) (Yt : Finset (TorusSite (n * R.params.side)))
    (free bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (base : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) :
    ChartSetting R n :=
  ⟨V, top, base, Yt, ω, b, free, bad⟩
theorem eq_assemble (s : ChartSetting R n) {Y : Finset (TorusSite (n * R.params.side))}
    {F Bd : Finset (TorusBond (n * R.params.side))} {b : BaseChoice R.params.side n} (hY : s.support = Y)
    (hF : s.free = F) (hBd : s.bad = Bd) (hb : s.bases = b) :
    s = assemble s.coarse s.region Y F Bd b s.fine (fun z => s.labelling ⟨z.1, hY ▸ z.2⟩) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.eq_settingOfParts <;> assumption
section Family
variable {X : Type*} [MeasurableSpace X] (V : TorusField n) (top : Finset (TorusSite n))
  (Yt : Finset (TorusSite (n * R.params.side))) (free bad : Finset (TorusBond (n * R.params.side)))
  (b : BaseChoice R.params.side n)
theorem measurable_field_joint (base : X → TorusField (n * R.params.side)) (ω : X → Yt → R.labels.Ω)
    (hb : Measurable base) :
    Measurable fun p : X × FreeCoords free => (assemble V top Yt free bad b (base p.1) (ω p.1)).field p.2 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurable_field_prod <;> assumption
end Family
section WilsonWeightSeriesExpansion
variable [NeZero n]
theorem sum_sitesInBlocks (L : ℕ) [NeZero L] (f : TorusSite (n * L) → ℝ) :
    ∑ Y : TorusSite n, ∑ y ∈ sitesInBlocks L {Y}, f y = ∑ y, f y := by apply _root_.YangMills.Construction.FreeBonds.sum_sitesInBlocks_singleton <;> assumption
theorem sum_levelShare (hS : SharesSumToAction) (a : ℝ) (L t m : ℕ) [NeZero m] (S : Finset (TorusSite m))
    (W : TorusField m) (ha : 0 ≤ a) (hL : 0 < L) (hm : 2 ≤ m) :
    ∑ y, levelShare a L t S y W = actionAtLevel a L t S W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.sum_levelShare <;> assumption
def fitSum (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (W : TorusField (n * ℓ.side)) (V : TorusField n) (b : BaseChoice ℓ.side n) : ℝ :=
  ∑ Y : TorusSite n, ℓ.coupling / 2 * ∑ i : Fin 4, (bondFit ℓ W V b (Y, i) + bondFit ℓ W V b (Y - TorusFields.unitStep n i, i))
theorem exp_neg_potential_eq
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
        Real.exp (-(R.coupling * fitSum R.params (s.field η) s.coarse s.bases) +
          ∑ Y : TorusSite n, s.logJacobian (s.field η) η Y) :=
  _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.exp_neg_potential
    hr hside hflat hS ha hL hm s η hh hΦ
theorem measurable_haarLogDensity : Measurable haarLogDensity := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.measurable_haarLogDensity <;> assumption
theorem measurable_bondFit (hM : MeasurableContourMeanStatement) (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (V : TorusField n)
    (b : BaseChoice ℓ.side n) (c : TorusBond n) : Measurable fun W : TorusField (n * ℓ.side) => bondFit ℓ W V b c := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurable_bondFit <;> assumption
theorem measurable_meanNorm (hM : MeasurableContourMeanStatement) (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (b : BaseChoice ℓ.side n)
    (c : TorusBond n) : Measurable fun W : TorusField (n * ℓ.side) => meanNorm ℓ W b c :=
  hM ℓ n b (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) (fun q => ‖q‖) continuous_norm
theorem measurable_fitSum (hM : MeasurableContourMeanStatement) (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (V : TorusField n)
    (b : BaseChoice ℓ.side n) : Measurable fun W : TorusField (n * ℓ.side) => fitSum ℓ W V b := by
  unfold fitSum
  refine Finset.measurable_sum _ fun Y _ => measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
  exact (measurable_bondFit hM ℓ V b _).add (measurable_bondFit hM ℓ V b _)
end WilsonWeightSeriesExpansion
section Mass
variable [NeZero n] {X : Type*} [MeasurableSpace X] (V : TorusField n) (top : Finset (TorusSite n))
  (Yt : Finset (TorusSite (n * R.params.side))) (free bad : Finset (TorusBond (n * R.params.side)))
  (b : BaseChoice R.params.side n)
def logJacobianSum (W : TorusField (n * R.params.side)) (η : FreeCoords free) : ℝ :=
  open Classical in
  ∑ Y : TorusSite n, (∑ i : Fin 4, logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params W b (Y, i)) +
    ∑ e : free, if bondBlock (R := R) e.1 = Y then
      Real.log (haarLogDensity (toCoords (frameCoord R.params R.anchorRadius R.depth R.frameReach V e.1) + η e))
      else 0)
def hullLabelWeight (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) : ℝ :=
  open Classical in
  if IsHullState R.params (clusterRange R.coupling) W Yt then R.labelWeight (n * R.params.side) W Yt ω else 0
def integrandDensity (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) (η : FreeCoords free) : ℝ :=
  (∏ e : free, cutoffFactor R.ballRadius R.barrierFn (coordNorm (η e))) *
    ((hullLabelWeight Yt W ω /
      (R.functional (n * R.params.side) (trivialField _) *
        ∏ Z ∈ chainComponents R.range Yt, R.clusterFactor (n * R.params.side) W Yt ω Z)) *
        Real.exp (-(R.coupling * fitSum R.params W V b) + logJacobianSum V free b W η))
theorem measurable_logJacobianSum (hM : MeasurableContourMeanStatement)
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
theorem measurable_integrandDensity
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) (hM : MeasurableContourMeanStatement)
    (hp : IsCutoff R.ballRadius R.barrierFn) (W : X × FreeCoords free → TorusField (n * R.params.side))
    (ω : X → Yt → R.labels.Ω) (hW : Measurable W) (hω : Measurable ω) :
    Measurable fun p => integrandDensity V Yt free b (W p) (ω p.1) p.2 := by
  classical
  have hWω : Measurable fun p : X × FreeCoords free => (W p, ω p.1) := hW.prodMk (hω.comp measurable_fst)
  obtain ⟨bD, bΦ, -⟩ := hr.borel (n * R.params.side) hside Yt
  have h0 : Measurable fun p : X × FreeCoords free =>
      ∏ e : free, cutoffFactor R.ballRadius R.barrierFn (coordNorm (p.2 e)) :=
    Finset.measurable_prod _ fun e _ =>
      (measurable_cutoffFactor_coordNorm hp).comp ((measurable_pi_apply e).comp measurable_snd)
  have hg : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => hullLabelWeight Yt p.1 p.2 := bD
  have h1' := hg.comp hWω
  have h1 : Measurable fun p : X × FreeCoords free => hullLabelWeight Yt (W p) (ω p.1) := h1'
  have h2 : Measurable fun p : X × FreeCoords free =>
      R.functional (n * R.params.side) (trivialField _) *
        ∏ Z ∈ chainComponents R.range Yt, R.clusterFactor (n * R.params.side) (W p) Yt (ω p.1) Z :=
    measurable_const.mul (Finset.measurable_prod _ fun Z _ => (bΦ Z).comp hWω)
  have h3 : Measurable fun p : X × FreeCoords free =>
      Real.exp (-(R.coupling * fitSum R.params (W p) V b) + logJacobianSum V free b (W p) p.2) :=
    Real.measurable_exp.comp (((measurable_const.mul ((measurable_fitSum hM R.params V b).comp hW)).neg).add
      (measurable_logJacobianSum V free b hM W hW))
  unfold integrandDensity
  exact h0.mul ((h1.div h2).mul h3)
theorem cutoff_mul_exp_eq
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0) (hS : SharesSumToAction)
    (ha : 0 ≤ R.params.coupling) (hL : 0 < R.params.side) (hm : 2 ≤ n * R.params.side)
    (base : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω)
    (hs : (assemble V top Yt free bad b base ω).IsAdmissible) (η : FreeCoords free) :
    (assemble V top Yt free bad b base ω).cutoffProduct η *
        Real.exp (-(assemble V top Yt free bad b base ω).potential η) =
      integrandDensity V Yt free b ((assemble V top Yt free bad b base ω).field η) ω η := by
  classical
  unfold integrandDensity
  by_cases hη : (assemble V top Yt free bad b base ω).InBalls η
  · have hh := hs.isHull η hη
    have hΦ := hs.factor_ne_zero η hη
    rw [exp_neg_potential_eq hr hside hflat hS ha hL hm (assemble V top Yt free bad b base ω) η hh hΦ]
    have hh' : IsHullState R.params (clusterRange R.coupling) ((assemble V top Yt free bad b base ω).field η) Yt := hh
    have hg : hullLabelWeight Yt ((assemble V top Yt free bad b base ω).field η) ω =
        R.labelWeight (n * R.params.side) ((assemble V top Yt free bad b base ω).field η) Yt ω := if_pos hh'
    rw [hg]
    rfl
  · have hz : (∏ e : free, cutoffFactor R.ballRadius R.barrierFn (coordNorm (η e))) = 0 := by
      simp only [ChartSetting.InBalls, not_forall, not_le] at hη
      obtain ⟨e, he⟩ := hη
      refine Finset.prod_eq_zero (Finset.mem_univ e) ?_
      unfold cutoffFactor
      exact if_neg (not_lt.mpr he.le)
    have hz' : (assemble V top Yt free bad b base ω).cutoffProduct η = 0 := hz
    rw [hz', hz, zero_mul, zero_mul]
theorem measurable_weightedMean_family
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0) (hS : SharesSumToAction)
    (hM : MeasurableContourMeanStatement) (hp : IsCutoff R.ballRadius R.barrierFn) (ha : 0 ≤ R.params.coupling)
    (hL : 0 < R.params.side) (hm : 2 ≤ n * R.params.side) (base : X → TorusField (n * R.params.side))
    (ω : X → Yt → R.labels.Ω) (hb : Measurable base) (hω : Measurable ω)
    (hs : ∀ x, (assemble V top Yt free bad b (base x) (ω x)).IsAdmissible)
    (F : X × FreeCoords free → ℝ) (hF : Measurable F) :
    Measurable fun x =>
      weightedMean (chartDensity (assemble V top Yt free bad b (base x) (ω x))) fun η => F (x, η) := by
  have hD := measurable_integrandDensity V Yt free b hr hside hM hp _ ω
    (measurable_field_joint V top Yt free bad b base ω hb) hω
  have e : ∀ x η, chartDensity (assemble V top Yt free bad b (base x) (ω x)) η =
      integrandDensity V Yt free b ((assemble V top Yt free bad b (base x) (ω x)).field η) (ω x) η := fun x η =>
    cutoff_mul_exp_eq V top Yt free bad b hr hside hflat hS ha hL hm _ _ (hs x) η
  have hmean : (fun x =>
        weightedMean (chartDensity (assemble V top Yt free bad b (base x) (ω x))) fun η => F (x, η)) =
      fun x => (∫ η, F (x, η) *
          integrandDensity V Yt free b ((assemble V top Yt free bad b (base x) (ω x)).field η) (ω x) η) /
        ∫ η, integrandDensity V Yt free b ((assemble V top Yt free bad b (base x) (ω x)).field η) (ω x) η := by
    funext x
    unfold weightedMean
    simp_rw [e x]
  rw [hmean]
  have h1 := (hF.mul hD).stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (FreeCoords free)))
  have h2 := hD.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (FreeCoords free)))
  exact h1.measurable.div h2.measurable
end Mass
def MeasurableOnFamilies [NeZero n] (G : GasGround R n) (Ψ : ChartSetting R n → ℝ) : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (Yt : Finset (TorusSite (n * R.params.side)))
    (free bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (base : X → TorusField (n * R.params.side)) (ω : X → Yt → R.labels.Ω), Measurable base → Measurable ω →
    (∀ x, (assemble G.coarse G.region Yt free bad b (base x) (ω x)).IsAdmissible) →
    Measurable fun x => Ψ (assemble G.coarse G.region Yt free bad b (base x) (ω x))
section Gas
variable [NeZero n] {X : Type} [MeasurableSpace X]
theorem finite_cell (L n : ℕ) [NeZero L] [NeZero n] : Finite (stepBlockFrame L n).Cell := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.finite_cell <;> assumption
theorem measurableSet_withNone {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (S : Set (WithNone α)) : MeasurableSet S :=
  And.intro (Set.to_countable (Sum.inl ⁻¹' S)).measurableSet (Set.to_countable (Sum.inr ⁻¹' S)).measurableSet
open Classical in
def occupiedSites (H : Set (GasSupport R n)) : Finset (TorusSite (n * R.params.side)) :=
  (Finset.univ.filter fun θ => θ ∈ H).biUnion Prod.snd
open Classical in
def freeBondsUnder (G : GasGround R n) (H : Set (GasSupport R n)) : Finset (TorusBond (n * R.params.side)) :=
  G.freeBonds.filter fun e => ¬ ∃ θ : GasSupport R n, θ ∈ H ∧ e ∈ θ.coreBonds
open Classical in
def badBondsUnder (G : GasGround R n) (H : Set (GasSupport R n)) : Finset (TorusBond (n * R.params.side)) :=
  G.recordedBad ∪ (Finset.univ.filter fun θ => θ ∈ H).biUnion Prod.fst ∪
    (chartBonds R.params.side n).filter fun b => parentBlock R.params.side b.1 ∈ G.cut
variable (G : GasGround R n) (γ : X → GasFamily R n) (H : Set (GasSupport R n))
  (hγ : ∀ θ, Measurable fun x => γ x θ) (hH : ∀ x θ, (γ x).Occupies θ ↔ θ ∈ H)
include hγ hH
theorem measurable_of_pick {β : Type*} [MeasurableSpace β] (Q : GasSupport R n → Prop)
    (v : ∀ θ : GasSupport R n, SupportState θ → Q θ → β) (hv : ∀ θ (h : Q θ), Measurable fun s => v θ s h)
    (h0 : ∃ θ, θ ∈ H ∧ Q θ) (f : X → β)
    (hf : ∀ x (h : ∃ θ, (γ x).Occupies θ ∧ Q θ),
      f x = v h.choose ((γ x).state h.choose_spec.1) h.choose_spec.2) : Measurable f := by exact _root_.YangMills.Construction.ClusterExpansionOfAStep.GroundDensityMeasurability.measurable_of_chosen_support (R := R) (n := n) (X := X) γ H hγ hH Q v hv h0 f hf
omit hγ [MeasurableSpace X] in
theorem fieldAt_eq_inl_iff (x : X) (e : TorusBond (n * R.params.side)) :
    (γ x).fieldAt e = Sum.inl () ↔ ¬ ∃ θ : GasSupport R n, θ ∈ H ∧ e ∈ θ.coreBonds := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GroundDensityMeasurability.fieldAt_eq_inl_iff <;> assumption
theorem measurable_fieldAt (e : TorusBond (n * R.params.side)) : Measurable fun x => (γ x).fieldAt e := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GroundDensityMeasurability.measurable_fieldAt_family <;> assumption
theorem measurable_baseAt (y : TorusSite n) : Measurable fun x => (γ x).baseAt y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GroundDensityMeasurability.measurable_baseAt_family <;> assumption
omit hγ [MeasurableSpace X] in
theorem sites_eq (x : X) : (γ x).sites = occupiedSites H := by
  classical
  ext z
  simp [GasFamily.sites, occupiedSites, hH]
theorem measurable_withFamily_fine : Measurable fun x => (G.settingWithFamily (γ x)).fine := by
  refine measurable_pi_iff.mpr fun y => measurable_pi_iff.mpr fun i => ?_
  have e : (fun x => (G.settingWithFamily (γ x)).fine y i) = fun x =>
      Sum.elim (fun _ => G.state.fieldWithStoredLinks (trivialField _) y i) id ((γ x).fieldAt (y, i)) := by
    funext x
    show (match (γ x).fieldAt (y, i) with
      | Sum.inr g => g
      | Sum.inl _ => G.state.fieldWithStoredLinks (trivialField _) y i) = _
    cases (γ x).fieldAt (y, i) <;> rfl
  rw [e]
  exact (measurable_const.sumElim measurable_id).comp (measurable_fieldAt γ H hγ hH _)
omit hγ [MeasurableSpace X] in
theorem support_eq (x : X) : (G.settingOf (γ x)).support = G.recordedSites ∪ occupiedSites H := by
  show G.recordedSites ∪ (γ x).sites = _
  rw [sites_eq γ H hH x]
omit hγ [MeasurableSpace X] in
theorem free_eq (x : X) : (G.settingOf (γ x)).free = freeBondsUnder G H := by
  classical
  show G.freeBonds.filter (fun b => (γ x).fieldAt b = Sum.inl ()) = _
  ext e
  simp only [freeBondsUnder, Finset.mem_filter]
  exact and_congr_right fun _ => fieldAt_eq_inl_iff γ H hH x e
omit hγ [MeasurableSpace X] in
theorem bad_eq (x : X) : (G.settingOf (γ x)).bad = badBondsUnder G H := by
  classical
  show G.recordedBad ∪ (Finset.univ.filter fun θ => (γ x).Occupies θ).biUnion Prod.fst ∪
    (chartBonds R.params.side n).filter (fun b => parentBlock R.params.side b.1 ∈ G.cut) = _
  ext e
  simp [badBondsUnder, hH]
theorem measurable_labels :
    Measurable fun (x : X) (z : (G.recordedSites ∪ occupiedSites H : Finset (TorusSite (n * R.params.side)))) =>
      (G.settingOf (γ x)).labelling ⟨z.1, (support_eq G γ H hH x).symm ▸ z.2⟩ := by
  classical
  refine measurable_pi_iff.mpr fun z => ?_
  by_cases hz : z.1 ∈ occupiedSites H
  · have hx : ∀ x, z.1 ∈ (γ x).sites := fun x => by rw [sites_eq γ H hH x]; exact hz
    have h0 : ∃ θ : GasSupport R n, θ ∈ H ∧ z.1 ∈ θ.2 := by
      obtain ⟨θ, hθ, hzθ⟩ := Finset.mem_biUnion.mp hz
      exact ⟨θ, (Finset.mem_filter.mp hθ).2, hzθ⟩
    refine measurable_of_pick γ H hγ hH (fun θ : GasSupport R n => z.1 ∈ θ.2) (fun θ s h => s.2.1 ⟨z.1, h⟩) ?_ h0 _ ?_
    · intro θ h
      exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
    · intro x h
      show (if h' : z.1 ∈ (γ x).sites then (γ x).labelAt h' else _) = _
      rw [dif_pos (hx x)]
      rfl
  · have hs : z.1 ∈ G.recordedSites := (Finset.mem_union.mp z.2).resolve_right hz
    have e : ∀ x, (G.settingOf (γ x)).labelling ⟨z.1, (support_eq G γ H hH x).symm ▸ z.2⟩ =
        G.recordedLabel ⟨z.1, hs⟩ := by
      intro x
      show (if h' : z.1 ∈ (γ x).sites then (γ x).labelAt h' else _) = _
      rw [dif_neg (fun h' => hz (by rwa [sites_eq γ H hH x] at h'))]
    simp only [e]
    exact measurable_const
omit hγ hH [MeasurableSpace X] in
theorem bases_apply (c : (stepBlockFrame R.params.side n).Cell) (x : X) :
    (G.settingOf (γ x)).bases c = Sum.elim (fun _ => G.groundBases c)
      (fun o => frameBlockSite R.params.side n
        (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o)
      ((γ x).baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c)) := by
  show (match (γ x).baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
    | Sum.inr o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o
    | Sum.inl _ => G.groundBases c) = _
  cases (γ x).baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) <;> rfl
theorem measurableSet_bases_apply (b : BaseChoice R.params.side n) (c : (stepBlockFrame R.params.side n).Cell) :
    MeasurableSet {x | (G.settingOf (γ x)).bases c = b c} := by
  have h1 := measurable_baseAt γ H hγ hH (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c)
    (measurableSet_withNone {m | Sum.elim (fun _ => G.groundBases c)
      (fun o => frameBlockSite R.params.side n
        (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o) m = b c})
  have h2 : {x | (G.settingOf (γ x)).bases c = b c} =
      (fun x => (γ x).baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c)) ⁻¹'
        {m | Sum.elim (fun _ => G.groundBases c)
          (fun o => frameBlockSite R.params.side n
            (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o) m = b c} := by
    ext x
    rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq, bases_apply]
  rw [h2]
  exact h1
theorem measurableSet_bases (b : BaseChoice R.params.side n) :
    MeasurableSet {x | (G.settingOf (γ x)).bases = b} := by
  have e : {x | (G.settingOf (γ x)).bases = b} =
      ⋂ c : (stepBlockFrame R.params.side n).Cell, {x | (G.settingOf (γ x)).bases c = b c} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact funext_iff
  rw [e]
  have hcount : Countable (stepBlockFrame R.params.side n).Cell := (finite_cell R.params.side n).to_countable
  exact MeasurableSet.iInter fun c => measurableSet_bases_apply G γ H hγ hH b c
omit hγ [MeasurableSpace X] in
theorem setting_eq (b : BaseChoice R.params.side n) (x : X) (hb : (G.settingOf (γ x)).bases = b) :
    G.settingOf (γ x) = assemble G.coarse G.region (G.recordedSites ∪ occupiedSites H) (freeBondsUnder G H)
      (badBondsUnder G H) b (G.settingOf (γ x)).fine
      (fun z => (G.settingOf (γ x)).labelling ⟨z.1, (support_eq G γ H hH x).symm ▸ z.2⟩) :=
  eq_assemble (G.settingOf (γ x)) (support_eq G γ H hH x) (free_eq G γ H hH x) (bad_eq G γ H hH x) hb
omit hγ [MeasurableSpace X] in
theorem withFamily_eq (b : BaseChoice R.params.side n) (x : X) (hb : (G.settingOf (γ x)).bases = b) :
    G.settingWithFamily (γ x) = assemble G.coarse G.region (G.recordedSites ∪ occupiedSites H)
      (freeBondsUnder G H) (badBondsUnder G H) b (G.settingWithFamily (γ x)).fine
      (fun z => (G.settingOf (γ x)).labelling ⟨z.1, (support_eq G γ H hH x).symm ▸ z.2⟩) :=
  eq_assemble (G.settingWithFamily (γ x)) (support_eq G γ H hH x) (free_eq G γ H hH x) (bad_eq G γ H hH x) hb
theorem measurable_setting_fine (b : BaseChoice R.params.side n) (hb : ∀ x, (G.settingOf (γ x)).bases = b) :
    Measurable fun x => (G.settingOf (γ x)).fine := by
  have e : (fun x => (G.settingOf (γ x)).fine) = fun x =>
      (assemble G.coarse G.region (G.recordedSites ∪ occupiedSites H) (freeBondsUnder G H) (badBondsUnder G H) b
        (G.settingWithFamily (γ x)).fine
        (fun z => (G.settingOf (γ x)).labelling ⟨z.1, (support_eq G γ H hH x).symm ▸ z.2⟩)).field 0 :=
    funext fun x => congrArg (fun s : ChartSetting R n => s.field 0) (withFamily_eq G γ H hH b x (hb x))
  rw [e]
  have h1 := measurable_field_joint G.coarse G.region (G.recordedSites ∪ occupiedSites H) (freeBondsUnder G H)
    (badBondsUnder G H) b (fun x => (G.settingWithFamily (γ x)).fine)
    (fun x z => (G.settingOf (γ x)).labelling ⟨z.1, (support_eq G γ H hH x).symm ▸ z.2⟩)
    (measurable_withFamily_fine G γ H hγ hH)
  have h0 : Measurable fun x : X => (x, (0 : FreeCoords (freeBondsUnder G H))) :=
    measurable_id.prodMk measurable_const
  have h2 := h1.comp h0
  exact h2
theorem measurable_of_fixed_parts (Ψ : ChartSetting R n → ℝ) (hΨ : MeasurableOnFamilies G Ψ)
    (b : BaseChoice R.params.side n) (hb : ∀ x, (G.settingOf (γ x)).bases = b)
    (hs : ∀ x, (G.settingOf (γ x)).IsAdmissible) : Measurable fun x => Ψ (G.settingOf (γ x)) := by
  have hs' : ∀ x, (assemble G.coarse G.region (G.recordedSites ∪ occupiedSites H) (freeBondsUnder G H)
      (badBondsUnder G H) b (G.settingOf (γ x)).fine
      (fun z => (G.settingOf (γ x)).labelling ⟨z.1, (support_eq G γ H hH x).symm ▸ z.2⟩)).IsAdmissible := fun x =>
    (setting_eq G γ H hH b x (hb x)) ▸ hs x
  have hm' := hΨ (G.recordedSites ∪ occupiedSites H) (freeBondsUnder G H) (badBondsUnder G H) b
    (fun x => (G.settingOf (γ x)).fine)
    (fun x z => (G.settingOf (γ x)).labelling ⟨z.1, (support_eq G γ H hH x).symm ▸ z.2⟩)
    (measurable_setting_fine G γ H hγ hH b hb) (measurable_labels G γ H hγ hH) hs'
  have e : (fun x => Ψ (G.settingOf (γ x))) = fun x =>
      Ψ (assemble G.coarse G.region (G.recordedSites ∪ occupiedSites H) (freeBondsUnder G H) (badBondsUnder G H) b
        (G.settingOf (γ x)).fine
        (fun z => (G.settingOf (γ x)).labelling ⟨z.1, (support_eq G γ H hH x).symm ▸ z.2⟩)) :=
    funext fun x => congrArg Ψ (setting_eq G γ H hH b x (hb x))
  rw [e]
  exact hm'
end Gas
section Top
variable [NeZero n] (G : GasGround R n)
theorem measurable_familyOf (θ : GasSupport R n) : Measurable fun σ : G.Config => G.familyOf σ θ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurable_familyOf <;> assumption
theorem measurableSet_admissible : MeasurableSet {σ : G.Config | G.pairConstraint.IsAdmissible σ} := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurableSet_admissible <;> assumption
theorem measurableSet_occupies (θ : GasSupport R n) :
    MeasurableSet {σ : G.Config | (G.familyOf σ).Occupies θ} := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurableSet_occupies <;> assumption
def occupancyPiece (H : Set (GasSupport R n)) : Set G.Config :=
  {σ | G.pairConstraint.IsAdmissible σ ∧ ∀ θ, (G.familyOf σ).Occupies θ ↔ θ ∈ H}
theorem measurableSet_occupancyPiece (H : Set (GasSupport R n)) : MeasurableSet (occupancyPiece G H) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurableSet_occupancyPiece <;> assumption
theorem countable_baseChoice (L n : ℕ) [NeZero L] [NeZero n] : Countable (BaseChoice L n) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.countable_baseChoice <;> assumption
variable (hset : ∀ σ : G.Config, G.pairConstraint.IsAdmissible σ → (G.settingOf (G.familyOf σ)).IsAdmissible)
include hset
theorem measurable_on_occupancyPiece (Ψ : ChartSetting R n → ℝ) (hΨ : MeasurableOnFamilies G Ψ)
    (H : Set (GasSupport R n)) :
    Measurable fun a : occupancyPiece G H => Ψ (G.settingOf (G.familyOf a.1)) := by
  have hcount := countable_baseChoice R.params.side n
  have hγ : ∀ θ, Measurable fun a : occupancyPiece G H => G.familyOf a.1 θ := fun θ =>
    (measurable_familyOf G θ).comp measurable_subtype_coe
  have hH : ∀ (a : occupancyPiece G H) θ, (G.familyOf a.1).Occupies θ ↔ θ ∈ H := fun a => a.2.2
  refine measurable_of_countable_cover
    (fun b : BaseChoice R.params.side n => {a : occupancyPiece G H | (G.settingOf (G.familyOf a.1)).bases = b})
    (fun b => measurableSet_bases G (fun a : occupancyPiece G H => G.familyOf a.1) H hγ hH b) (fun a => ⟨_, rfl⟩)
    fun b => ?_
  exact measurable_of_fixed_parts G
    (fun a : {a : occupancyPiece G H | (G.settingOf (G.familyOf a.1)).bases = b} => G.familyOf a.1.1) H
    (fun θ => (hγ θ).comp measurable_subtype_coe) (fun a => hH a.1) Ψ hΨ b (fun a => a.2)
    (fun a => hset _ a.1.2.1)
theorem measurable_restrictAdmissible (Ψ : ChartSetting R n → ℝ) (hΨ : MeasurableOnFamilies G Ψ) :
    Measurable (restrictAdmissible G fun σ => Ψ (configSetting G σ)) := by
  classical
  refine measurable_of_countable_cover (ι := Option (Set (GasSupport R n)))
    (fun o => o.elim {σ : G.Config | ¬ G.pairConstraint.IsAdmissible σ} (occupancyPiece G)) ?_ ?_ ?_
  · rintro (_ | H)
    · exact (measurableSet_admissible G).compl
    · exact measurableSet_occupancyPiece G H
  · intro σ
    by_cases h : G.pairConstraint.IsAdmissible σ
    · exact ⟨some {θ | (G.familyOf σ).Occupies θ}, h, fun θ => Iff.rfl⟩
    · exact ⟨none, h⟩
  · rintro (_ | H)
    · have e : (fun a : {σ : G.Config | ¬ G.pairConstraint.IsAdmissible σ} =>
            restrictAdmissible G (fun σ => Ψ (configSetting G σ)) a.1) = fun _ => 0 :=
        funext fun a => if_neg a.2
      exact e ▸ measurable_const
    · have e : (fun a : occupancyPiece G H => restrictAdmissible G (fun σ => Ψ (configSetting G σ)) a.1) =
          fun a => Ψ (G.settingOf (G.familyOf a.1)) := funext fun a => if_pos a.2.1
      have h := measurable_on_occupancyPiece G hset Ψ hΨ H
      exact e ▸ h
end Top
end GasMeans
set_option maxHeartbeats 2000000 in
open GasMeans in
theorem gasMeansMeasurable_holds (hC : GasConfigIsAdmissibleSetting)
    (hM : MeasurableContourMeanStatement) (hS : SharesSumToAction)
    (hLive : ChartDensitySupportedOnLiveStates) (hScore : BondScoreProperties) :
    GasMeansMeasurable := by
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT _ K => ?_⟩
  obtain ⟨y₀, hy⟩ := hC T hT
  obtain ⟨y₁, hy₁⟩ := hLive T hT
  refine ⟨max y₀ (max y₁ (max T.floorMin (200 * T.B + 1))), fun y hy0 R A _ hAt n _ G hG => ?_⟩
  obtain ⟨a₀, hy0⟩ := max_le_iff.mp hy0
  obtain ⟨a₁, hy0⟩ := max_le_iff.mp hy0
  obtain ⟨a₂, a₃⟩ := max_le_iff.mp hy0
  have hR := hAt.onFamily
  have hx : y ≤ R.coupling := hR.le_coupling
  have hx' : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAt.abs_sub_le).2
    have h2 : 200 * T.B + 1 ≤ R.coupling := a₃.trans hx
    linarith
  have hset := hy y a₀ R hR hx' n G hG
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
  have hfit : R.params.Admissible := by
    rw [hR.params_eq]
    exact hT.fits y a₂
  have hresp := hAt.admissible.bounds
  refine ⟨fun z h => ?_, fun c => ?_, fun z => ?_⟩
  · refine measurable_restrictAdmissible G hset (fun s => chartResponse A s z h) ?_
    intro X _ Yt free bad b base ω hb hω hs
    classical
    let Qg : TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ℝ := fun p =>
      if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then A.hull (n * R.params.side) z p.1 Yt p.2 h
      else 0
    have hQ : Measurable Qg := hresp.hull_borel (n * R.params.side) hside z Yt h
    have hfj := measurable_field_joint G.coarse G.region Yt free bad b base ω hb
    have hF : Measurable fun p : X × FreeCoords free =>
        Qg ((assemble G.coarse G.region Yt free bad b (base p.1) (ω p.1)).field p.2, ω p.1) -
          A.cold (n * R.params.side) z (trivialField _) h :=
      (hQ.comp (hfj.prodMk (hω.comp measurable_fst))).sub measurable_const
    have key := measurable_weightedMean_family G.coarse G.region Yt free bad b hrow.2 hside hflat hS hM hp ha hLpos
      hm base ω hb hω hs _ hF
    have e : (fun x => chartResponse A (assemble G.coarse G.region Yt free bad b (base x) (ω x)) z h) = fun x =>
        weightedMean (chartDensity (assemble G.coarse G.region Yt free bad b (base x) (ω x))) fun η =>
          Qg ((assemble G.coarse G.region Yt free bad b (base x) (ω x)).field η, ω x) -
            A.cold (n * R.params.side) z (trivialField _) h := by
      funext x
      unfold chartResponse weightedMean
      congr 1
      refine integral_congr_ae (ae_of_all _ fun η => ?_)
      by_cases hd : chartDensity (assemble G.coarse G.region Yt free bad b (base x) (ω x)) η = 0
      · simp only [hd, mul_zero]
      · have hl := hy₁ y a₁ R hR n _ hn0 (hs x) η hd
        have hq : Qg ((assemble G.coarse G.region Yt free bad b (base x) (ω x)).field η, ω x) =
            A.hull (n * R.params.side) z ((assemble G.coarse G.region Yt free bad b (base x) (ω x)).field η) Yt
              (ω x) h := if_pos hl
        simp only [centeredHullResponse]
        rw [hq]
    rw [e]
    exact key
  · refine measurable_restrictAdmissible G hset (fun s => chartBondScore s c) ?_
    intro X _ Yt free bad b base ω hb hω hs
    have hfj := measurable_field_joint G.coarse G.region Yt free bad b base ω hb
    have hsc := (hScore R.params hfit R.coupling n b c).2.2.2.2
    have h2 : Measurable fun p : X × FreeCoords free =>
        ((assemble G.coarse G.region Yt free bad b (base p.1) (ω p.1)).field p.2, G.coarse) :=
      hfj.prodMk measurable_const
    have hF := Measurable.comp hsc h2
    have key := measurable_weightedMean_family G.coarse G.region Yt free bad b hrow.2 hside hflat hS hM hp ha hLpos
      hm base ω hb hω hs _ hF
    exact key
  · refine measurable_restrictAdmissible G hset (fun s => chartSiteScore A s z) ?_
    intro X _ Yt free bad b base ω hb hω hs
    classical
    have hpr := hAt.admissible.price
    change Measurable fun x => siteScore A.score Yt (ω x) z
    by_cases hz : z ∈ Yt
    · have e : (fun x => siteScore A.score Yt (ω x) z) = fun x => A.score (ω x ⟨z, hz⟩) := by
        funext x
        unfold siteScore
        rw [dif_pos hz]
      rw [e]
      exact hpr.borel.comp ((measurable_pi_apply (⟨z, hz⟩ : Yt)).comp hω)
    · have e : (fun x => siteScore A.score Yt (ω x) z) = fun _ => 0 := by
        funext x
        unfold siteScore
        rw [dif_neg hz]
      rw [e]
      exact measurable_const
end ResponseInTheExpansion
end YangMills.Construction
end
