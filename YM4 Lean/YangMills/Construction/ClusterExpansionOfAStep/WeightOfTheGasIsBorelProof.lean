import YangMills.Construction.ClusterExpansionOfAStep.ConfigurationsOfTheGasAreSettings
import YangMills.Construction.ClusterExpansionOfAStep.WeightOfTheGasIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames Dobrushin StepCosts TorusFields TorusLumps StepSettings StepGas
  RenormalizationStepParameters
namespace GasWeight
theorem measurable_of_iUnion_cover {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable ι]
    {f : α → β} (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i)) (hcover : ∀ a, ∃ i, a ∈ A i)
    (hf : ∀ i, Measurable fun a : A i => f a) : Measurable f := by
  intro B hB
  have e : f ⁻¹' B = ⋃ i, Subtype.val '' ((fun a : A i => f a) ⁻¹' B) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    constructor
    · intro h
      obtain ⟨i, hi⟩ := hcover a
      exact ⟨i, hi, h⟩
    · rintro ⟨i, hi, h⟩
      exact h
  rw [e]
  exact MeasurableSet.iUnion fun i => (hA i).subtype_image (hf i hB)
theorem measurable_sum_getRight {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → Unit ⊕ β}
    (hf : Measurable f) (h : ∀ a, (f a).isRight = true) : Measurable fun a => (f a).getRight (h a) := by
  intro B hB
  have e : (fun a => (f a).getRight (h a)) ⁻¹' B = f ⁻¹' (Sum.inr '' B) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hb
      exact ⟨_, hb, by simp⟩
    · rintro ⟨c, hc, e⟩
      have : (f a).getRight (h a) = c := by simp [← e]
      rwa [this]
  rw [e]
  exact hf hB.inr_image
variable {n : ℕ}
theorem measurable_pathHolonomy {F : BlockFrame} {j : ℕ} {Z : Type*} [MeasurableSpace Z]
    (f : Z → F.GaugeField j) (hf : ∀ x i, Measurable fun z => f z x i) (l : List PathStep) :
    ∀ x : F.Site j, Measurable fun z => pathHolonomy (f z) x l := by
  induction l with
  | nil => intro x; simp [pathHolonomy]
  | cons st r ih =>
    intro x
    simp only [pathHolonomy]
    refine Measurable.mul ?_ (ih _)
    unfold linkValue
    by_cases h : st.2 = true
    · simp only [if_pos h]
      exact hf x st.1
    · simp only [if_neg h]
      exact (hf _ st.1).inv
theorem measurable_gaugeAt {R : StepSetup} (x : TorusSite (n * R.params.side)) :
    Measurable fun W : TorusField (n * R.params.side) => gaugeAt (R := R) W x := by
  unfold gaugeAt axialGauge
  refine measurable_pathHolonomy
    (fun W : TorusField (n * R.params.side) => readAtLevel (stepBlockFrame R.params.side n) 0 W) (fun y i => ?_) _ _
  exact (measurable_pi_apply i).comp (measurable_pi_apply _)
variable {R : StepSetup}
abbrev settingOfParts (V : TorusField n) (top : Finset (TorusSite n)) (Yt : Finset (TorusSite (n * R.params.side)))
    (free bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (base : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) :
    ChartSetting R n :=
  ⟨V, top, base, Yt, ω, b, free, bad⟩
theorem eq_settingOfParts (s : ChartSetting R n) {Y : Finset (TorusSite (n * R.params.side))}
    {F Bd : Finset (TorusBond (n * R.params.side))} {b : BaseChoice R.params.side n} (hY : s.support = Y)
    (hF : s.free = F) (hBd : s.bad = Bd) (hb : s.bases = b) :
    s = settingOfParts s.coarse s.region Y F Bd b s.fine (fun z => s.labelling ⟨z.1, hY ▸ z.2⟩) := by
  subst hY hF hBd hb
  cases s
  rfl
section Family
variable {X : Type*} [MeasurableSpace X] (V : TorusField n) (top : Finset (TorusSite n))
  (Yt : Finset (TorusSite (n * R.params.side))) (free bad : Finset (TorusBond (n * R.params.side)))
  (b : BaseChoice R.params.side n)
theorem measurable_field_prod (base : X → TorusField (n * R.params.side)) (ω : X → Yt → R.labels.Ω)
    (hb : Measurable base) :
    Measurable fun p : X × FreeCoords free => (settingOfParts V top Yt free bad b (base p.1) (ω p.1)).field p.2 := by
  classical
  refine measurable_pi_iff.mpr fun y => measurable_pi_iff.mpr fun i => ?_
  by_cases h : (y, i) ∈ free
  · have h1 : Continuous fun v : EuclideanSpace ℝ (Fin 3) =>
        expUnit ((frameCoord R.params R.anchorRadius R.depth R.frameReach V (y, i)) + toImaginary v) :=
      continuous_expUnit.comp (continuous_const.add continuous_toImaginary)
    have h2 : Measurable fun p : X × FreeCoords free =>
        expUnit ((frameCoord R.params R.anchorRadius R.depth R.frameReach V (y, i)) + toImaginary (p.2 ⟨(y, i), h⟩)) :=
      h1.measurable.comp ((measurable_pi_apply _).comp measurable_snd)
    have t1 : ∀ z : TorusSite (n * R.params.side),
        Measurable fun p : X × FreeCoords free => gaugeAt (R := R) (base p.1) z :=
      fun z => (measurable_gaugeAt z).comp (hb.comp measurable_fst)
    simp only [ChartSetting.field, dif_pos h, chartLink]
    refine ((t1 y).inv.mul ?_).mul (t1 _)
    by_cases hc : IsCrossingBond (F := stepBlockFrame R.params.side n)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 0 y, i)
    · simp only [if_pos hc]
      exact h2.mul measurable_const
    · simp only [if_neg hc]
      exact h2
  · simp only [ChartSetting.field, dif_neg h]
    exact (measurable_pi_apply i).comp ((measurable_pi_apply y).comp (hb.comp measurable_fst))
end Family
section WilsonWeightSeriesExpansion
variable [NeZero n]
theorem sum_sitesInBlocks (L : ℕ) [NeZero L] (f : TorusSite (n * L) → ℝ) :
    ∑ Y : TorusSite n, ∑ y ∈ sitesInBlocks L {Y}, f y = ∑ y, f y := by apply _root_.YangMills.Construction.FreeBonds.sum_sitesInBlocks_singleton <;> assumption
theorem sum_count_cast {m : ℕ} [NeZero m] (l : List (TorusSite m)) :
    ∑ y : TorusSite m, ((l.count y : ℕ) : ℝ) = l.length := by apply _root_.YangMills.Construction.FreeBonds.sum_count_cast <;> assumption
theorem sum_levelShare (hS : SharesSumToAction) (a : ℝ) (L t m : ℕ) [NeZero m] (S : Finset (TorusSite m))
    (W : TorusField m) (ha : 0 ≤ a) (hL : 0 < L) (hm : 2 ≤ m) :
    ∑ y, levelShare a L t S y W = actionAtLevel a L t S W := by
  cases t with
  | succ t => exact hS a L t m S W ha hL hm
  | zero =>
    simp only [levelShare, actionAtLevel, TorusFields.wilsonAction]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_mul, ← Finset.sum_div, sum_count_cast]
    simp [plaquetteVertices]
def fitEnergy (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (W : TorusField (n * ℓ.side)) (V : TorusField n) (b : BaseChoice ℓ.side n) : ℝ :=
  ∑ Y : TorusSite n, ℓ.coupling / 2 * ∑ i : Fin 4, (bondFit ℓ W V b (Y, i) + bondFit ℓ W V b (Y - TorusFields.unitStep n i, i))
theorem exp_neg_potential
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
          ∑ Y : TorusSite n, s.logJacobian (s.field η) η Y) := by
  have form := hr.form (n * R.params.side) hside (s.field η) s.support s.labelling hh
  have hP : (∏ X ∈ chainComponents R.range s.support,
      R.clusterFactor (n * R.params.side) (s.field η) s.support s.labelling X) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hΦ
  have hcost : ∑ Y : TorusSite n, blockCost R.params R.depth (s.field η) s.coarse s.bases Y =
      actionAtLevel R.params.coupling R.params.side R.depth
          (Finset.univ \ thickening lumpRange (torusHotSites R.params (s.field η))) (s.field η) +
        fitEnergy R.params (s.field η) s.coarse s.bases := by
    simp only [blockCost, Finset.sum_add_distrib, fitEnergy]
    rw [sum_sitesInBlocks, sum_levelShare hS _ _ _ _ _ _ ha hL hm]
  have hphi : ∑ Y : TorusSite n, s.blockDensity (s.field η) Y =
      ∑ y, R.siteDensity (n * R.params.side) y (s.field η) s.support s.labelling := by
    simp only [ChartSetting.blockDensity]
    exact sum_sitesInBlocks _ _
  have hpot : -s.potential η =
      (-R.coupling * actionAtLevel R.params.coupling R.params.side R.depth
          (Finset.univ \ thickening lumpRange (torusHotSites R.params (s.field η))) (s.field η) +
        ∑ y, R.siteDensity (n * R.params.side) y (s.field η) s.support s.labelling) +
      (-(R.coupling * fitEnergy R.params (s.field η) s.coarse s.bases) +
        ∑ Y : TorusSite n, s.logJacobian (s.field η) η Y) := by
    simp only [ChartSetting.potential, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hcost, hphi]
    ring
  rw [hpot, Real.exp_add, form]
  field_simp
  rfl
theorem measurable_haarLogDensity : Measurable haarLogDensity := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.measurable_haarLogDensity <;> assumption
theorem measurable_bondFit (hM : MeasurableContourMeanStatement) (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (V : TorusField n)
    (b : BaseChoice ℓ.side n) (c : TorusBond n) :
    Measurable fun W : TorusField (n * ℓ.side) => bondFit ℓ W V b c := by
  refine hM ℓ n b (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2)
    (fun q => ‖q‖ - (q * ((((readAtLevel (stepBlockFrame ℓ.side n) 1 V)
      (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1) c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) ?_
  exact continuous_norm.sub (Quaternion.continuous_re.comp (continuous_id.mul continuous_const))
theorem measurable_meanNorm (hM : MeasurableContourMeanStatement) (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (b : BaseChoice ℓ.side n)
    (c : TorusBond n) : Measurable fun W : TorusField (n * ℓ.side) => meanNorm ℓ W b c :=
  hM ℓ n b (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) (fun q => ‖q‖) continuous_norm
theorem measurable_fitEnergy (hM : MeasurableContourMeanStatement) (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (V : TorusField n)
    (b : BaseChoice ℓ.side n) : Measurable fun W : TorusField (n * ℓ.side) => fitEnergy ℓ W V b := by
  unfold fitEnergy
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
        Real.exp (-(R.coupling * fitEnergy R.params W V b) + logJacobianSum V free b W η))
theorem measurable_logJacobianSum (hM : MeasurableContourMeanStatement)
    (W : X × FreeCoords free → TorusField (n * R.params.side)) (hW : Measurable W) :
    Measurable fun p => logJacobianSum V free b (W p) p.2 := by
  classical
  unfold logJacobianSum
  refine Finset.measurable_sum _ fun Y _ => ?_
  refine (Finset.measurable_sum _ fun i _ => ?_).add (Finset.measurable_sum _ fun e _ => ?_)
  · exact measurable_logPartitionGap.comp
      (measurable_const.mul ((measurable_meanNorm hM R.params b _).comp hW))
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
      Real.exp (-(R.coupling * fitEnergy R.params (W p) V b) + logJacobianSum V free b (W p) p.2) :=
    Real.measurable_exp.comp (((measurable_const.mul ((measurable_fitEnergy hM R.params V b).comp hW)).neg).add
      (measurable_logJacobianSum V free b hM W hW))
  unfold integrandDensity
  exact h0.mul ((h1.div h2).mul h3)
theorem cutoffProduct_mul_exp_eq
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0) (hS : SharesSumToAction)
    (ha : 0 ≤ R.params.coupling) (hL : 0 < R.params.side) (hm : 2 ≤ n * R.params.side)
    (base : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω)
    (hs : (settingOfParts V top Yt free bad b base ω).IsAdmissible) (η : FreeCoords free) :
    (settingOfParts V top Yt free bad b base ω).cutoffProduct η *
        Real.exp (-(settingOfParts V top Yt free bad b base ω).potential η) =
      integrandDensity V Yt free b ((settingOfParts V top Yt free bad b base ω).field η) ω η := by
  classical
  unfold integrandDensity
  by_cases hη : (settingOfParts V top Yt free bad b base ω).InBalls η
  · have hh := hs.isHull η hη
    have hΦ := hs.factor_ne_zero η hη
    rw [exp_neg_potential hr hside hflat hS ha hL hm (settingOfParts V top Yt free bad b base ω) η hh hΦ]
    have hh' : IsHullState R.params (clusterRange R.coupling)
        ((settingOfParts V top Yt free bad b base ω).field η) Yt := hh
    have hg : hullLabelWeight Yt ((settingOfParts V top Yt free bad b base ω).field η) ω =
        R.labelWeight (n * R.params.side) ((settingOfParts V top Yt free bad b base ω).field η) Yt ω := if_pos hh'
    rw [hg]
    rfl
  · have hz : (∏ e : free, cutoffFactor R.ballRadius R.barrierFn (coordNorm (η e))) = 0 := by
      simp only [ChartSetting.InBalls, not_forall, not_le] at hη
      obtain ⟨e, he⟩ := hη
      refine Finset.prod_eq_zero (Finset.mem_univ e) ?_
      unfold cutoffFactor
      exact if_neg (not_lt.mpr he.le)
    have hz' : (settingOfParts V top Yt free bad b base ω).cutoffProduct η = 0 := hz
    rw [hz', hz, zero_mul, zero_mul]
theorem measurable_settingMass_family
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0) (hS : SharesSumToAction)
    (hM : MeasurableContourMeanStatement) (hp : IsCutoff R.ballRadius R.barrierFn) (ha : 0 ≤ R.params.coupling)
    (hL : 0 < R.params.side) (hm : 2 ≤ n * R.params.side) (base : X → TorusField (n * R.params.side))
    (ω : X → Yt → R.labels.Ω) (hb : Measurable base) (hω : Measurable ω)
    (hs : ∀ x, (settingOfParts V top Yt free bad b (base x) (ω x)).IsAdmissible) :
    Measurable fun x => settingMass (settingOfParts V top Yt free bad b (base x) (ω x)) := by
  have hD := measurable_integrandDensity V Yt free b hr hside hM hp _ ω
    (measurable_field_prod V top Yt free bad b base ω hb) hω
  have e : (fun x => settingMass (settingOfParts V top Yt free bad b (base x) (ω x))) = fun x =>
      ∫⁻ η, ENNReal.ofReal
        (integrandDensity V Yt free b ((settingOfParts V top Yt free bad b (base x) (ω x)).field η) (ω x) η) := by
    funext x
    unfold settingMass
    refine lintegral_congr fun η => ?_
    rw [cutoffProduct_mul_exp_eq V top Yt free bad b hr hside hflat hS ha hL hm _ _ (hs x) η]
  rw [e]
  exact Measurable.lintegral_prod_right' (ν := (volume : Measure (FreeCoords free)))
    (f := fun p : X × FreeCoords free => ENNReal.ofReal
      (integrandDensity V Yt free b ((settingOfParts V top Yt free bad b (base p.1) (ω p.1)).field p.2) (ω p.1) p.2))
    (ENNReal.measurable_ofReal.comp hD)
end Mass
section Gas
variable [NeZero n] {X : Type*} [MeasurableSpace X]
theorem finite_cell (L n : ℕ) [NeZero L] [NeZero n] : Finite (stepBlockFrame L n).Cell := by
  have h : ∀ i : Fin 4, Finite (ZMod ((stepBlockFrame L n).period (stepBlockFrame L n).top i)) := fun i =>
    @Finite.of_fintype _ (@ZMod.fintype _ inferInstance)
  exact @Pi.finite _ _ _ h
theorem measurableSet_withNone {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (S : Set (WithNone α)) : MeasurableSet S :=
  And.intro (Set.to_countable (Sum.inl ⁻¹' S)).measurableSet (Set.to_countable (Sum.inr ⁻¹' S)).measurableSet
theorem exists_choose_congr {α : Type*} {P Q : α → Prop} (h : ∀ a, P a ↔ Q a) (hp : ∃ a, P a) (hq : ∃ a, Q a) :
    hp.choose = hq.choose := by
  have e : P = Q := funext fun a => propext (h a)
  subst e
  rfl
open Classical in
def supportSites (H : Set (GasSupport R n)) : Finset (TorusSite (n * R.params.side)) :=
  (Finset.univ.filter fun θ => θ ∈ H).biUnion Prod.snd
open Classical in
def freeBondsUnder (G : GasGround R n) (H : Set (GasSupport R n)) : Finset (TorusBond (n * R.params.side)) :=
  G.freeBonds.filter fun e => ¬ ∃ θ : GasSupport R n, θ ∈ H ∧ e ∈ θ.coreBonds
open Classical in
def badBondsUnder (G : GasGround R n) (H : Set (GasSupport R n)) : Finset (TorusBond (n * R.params.side)) :=
  G.recordedBad ∪ (Finset.univ.filter fun θ => θ ∈ H).biUnion Prod.fst ∪
    (chartBonds R.params.side n).filter fun c => parentBlock R.params.side c.1 ∈ G.cut
variable (G : GasGround R n) (γ : X → GasFamily R n) (H : Set (GasSupport R n))
  (hγ : ∀ θ, Measurable fun x => γ x θ) (hH : ∀ x θ, (γ x).Occupies θ ↔ θ ∈ H)
include hγ hH
theorem measurable_of_pick {β : Type*} [MeasurableSpace β] (Q : GasSupport R n → Prop)
    (v : ∀ θ : GasSupport R n, SupportState θ → Q θ → β) (hv : ∀ θ (h : Q θ), Measurable fun s => v θ s h)
    (h0 : ∃ θ, θ ∈ H ∧ Q θ) (f : X → β)
    (hf : ∀ x (h : ∃ θ, (γ x).Occupies θ ∧ Q θ),
      f x = v h.choose ((γ x).state h.choose_spec.1) h.choose_spec.2) : Measurable f := by
  have hc := h0.choose_spec
  have e : f = fun x => v h0.choose ((γ x).state ((hH x _).2 hc.1)) hc.2 := by
    funext x
    have hx : ∃ θ, (γ x).Occupies θ ∧ Q θ := ⟨h0.choose, (hH x _).2 hc.1, hc.2⟩
    rw [hf x hx]
    have key : ∀ (θ₁ : GasSupport R n) (h₁ : (γ x).Occupies θ₁ ∧ Q θ₁), θ₁ = h0.choose →
        v θ₁ ((γ x).state h₁.1) h₁.2 = v h0.choose ((γ x).state ((hH x _).2 hc.1)) hc.2 := by
      rintro _ _ rfl
      rfl
    exact key _ hx.choose_spec (exists_choose_congr (fun θ => and_congr_left' (hH x θ)) hx h0)
  rw [e]
  exact (hv _ hc.2).comp (measurable_sum_getRight (hγ h0.choose) _)
omit hγ [MeasurableSpace X] in
theorem fieldAt_eq_inl_iff (x : X) (e : TorusBond (n * R.params.side)) :
    (γ x).fieldAt e = Sum.inl () ↔ ¬ ∃ θ : GasSupport R n, θ ∈ H ∧ e ∈ θ.coreBonds := by
  classical
  constructor
  · rintro h ⟨θ, h1, h2⟩
    have hx : ∃ θ, (γ x).Occupies θ ∧ e ∈ GasSupport.coreBonds θ := ⟨θ, (hH x θ).2 h1, h2⟩
    unfold GasFamily.fieldAt at h
    rw [dif_pos hx] at h
    cases h
  · intro h
    unfold GasFamily.fieldAt
    refine dif_neg ?_
    rintro ⟨θ, h1, h2⟩
    exact h ⟨θ, (hH x θ).1 h1, h2⟩
theorem measurable_fieldAt (e : TorusBond (n * R.params.side)) : Measurable fun x => (γ x).fieldAt e := by
  classical
  by_cases h0 : ∃ θ : GasSupport R n, θ ∈ H ∧ e ∈ θ.coreBonds
  · refine measurable_of_pick γ H hγ hH (fun θ : GasSupport R n => e ∈ θ.coreBonds)
      (fun θ s h => Sum.inr (s.1 ⟨e, h⟩)) ?_ h0 _ ?_
    · intro θ h
      exact measurable_inr.comp ((measurable_pi_apply _).comp measurable_fst)
    · intro x h
      unfold GasFamily.fieldAt
      rw [dif_pos h]
  · simp only [(fieldAt_eq_inl_iff γ H hH _ e).2 h0]
    exact measurable_const
theorem measurable_baseAt (y : TorusSite n) : Measurable fun x => (γ x).baseAt y := by
  classical
  by_cases h0 : ∃ θ : GasSupport R n, θ ∈ H ∧ y ∈ θ.core
  · refine measurable_of_pick γ H hγ hH (fun θ : GasSupport R n => y ∈ θ.core)
      (fun θ s h => Sum.inr (s.2.2 ⟨y, h⟩)) ?_ h0 _ ?_
    · intro θ h
      exact measurable_inr.comp ((measurable_pi_apply _).comp (measurable_snd.comp measurable_snd))
    · intro x h
      unfold GasFamily.baseAt
      rw [dif_pos h]
  · have : ∀ x, (γ x).baseAt y = Sum.inl () := by
      intro x
      unfold GasFamily.baseAt
      refine dif_neg ?_
      rintro ⟨θ, h1, h2⟩
      exact h0 ⟨θ, (hH x θ).1 h1, h2⟩
    simp only [this]
    exact measurable_const
omit hγ [MeasurableSpace X] in
theorem sites_eq_supportSites (x : X) : (γ x).sites = supportSites H := by
  classical
  ext z
  simp [GasFamily.sites, supportSites, hH]
theorem measurable_settingWithFamily_fine : Measurable fun x => (G.settingWithFamily (γ x)).fine := by
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
theorem support_settingOf (x : X) : (G.settingOf (γ x)).support = G.recordedSites ∪ supportSites H := by
  show G.recordedSites ∪ (γ x).sites = _
  rw [sites_eq_supportSites γ H hH x]
omit hγ [MeasurableSpace X] in
theorem free_settingOf (x : X) : (G.settingOf (γ x)).free = freeBondsUnder G H := by
  classical
  show G.freeBonds.filter (fun c => (γ x).fieldAt c = Sum.inl ()) = _
  ext e
  simp only [freeBondsUnder, Finset.mem_filter]
  exact and_congr_right fun _ => fieldAt_eq_inl_iff γ H hH x e
omit hγ [MeasurableSpace X] in
theorem bad_settingOf (x : X) : (G.settingOf (γ x)).bad = badBondsUnder G H := by
  classical
  show G.recordedBad ∪ (Finset.univ.filter fun θ => (γ x).Occupies θ).biUnion Prod.fst ∪
    (chartBonds R.params.side n).filter (fun c => parentBlock R.params.side c.1 ∈ G.cut) = _
  ext e
  simp [badBondsUnder, hH]
theorem measurable_labelling :
    Measurable fun (x : X) (z : (G.recordedSites ∪ supportSites H : Finset (TorusSite (n * R.params.side)))) =>
      (G.settingOf (γ x)).labelling ⟨z.1, (support_settingOf G γ H hH x).symm ▸ z.2⟩ := by
  classical
  refine measurable_pi_iff.mpr fun z => ?_
  by_cases hz : z.1 ∈ supportSites H
  · have hx : ∀ x, z.1 ∈ (γ x).sites := fun x => by rw [sites_eq_supportSites γ H hH x]; exact hz
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
    have e : ∀ x, (G.settingOf (γ x)).labelling ⟨z.1, (support_settingOf G γ H hH x).symm ▸ z.2⟩ =
        G.recordedLabel ⟨z.1, hs⟩ := by
      intro x
      show (if h' : z.1 ∈ (γ x).sites then (γ x).labelAt h' else _) = _
      rw [dif_neg (fun h' => hz (by rwa [sites_eq_supportSites γ H hH x] at h'))]
    simp only [e]
    exact measurable_const
omit hγ hH [MeasurableSpace X] in
theorem bases_settingOf_apply (c : (stepBlockFrame R.params.side n).Cell) (x : X) :
    (G.settingOf (γ x)).bases c = Sum.elim (fun _ => G.groundBases c)
      (fun o => frameBlockSite R.params.side n
        (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o)
      ((γ x).baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c)) := by
  show (match (γ x).baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
    | Sum.inr o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o
    | Sum.inl _ => G.groundBases c) = _
  cases (γ x).baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) <;> rfl
theorem measurableSet_bases_apply_eq (b : BaseChoice R.params.side n) (c : (stepBlockFrame R.params.side n).Cell) :
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
    rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq, bases_settingOf_apply]
  rw [h2]
  exact h1
theorem measurableSet_bases_eq (b : BaseChoice R.params.side n) :
    MeasurableSet {x | (G.settingOf (γ x)).bases = b} := by
  have e : {x | (G.settingOf (γ x)).bases = b} =
      ⋂ c : (stepBlockFrame R.params.side n).Cell, {x | (G.settingOf (γ x)).bases c = b c} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact funext_iff
  rw [e]
  have hcount : Countable (stepBlockFrame R.params.side n).Cell := (finite_cell R.params.side n).to_countable
  exact MeasurableSet.iInter fun c => measurableSet_bases_apply_eq G γ H hγ hH b c
omit hγ [MeasurableSpace X] in
theorem settingOf_eq_parts (b : BaseChoice R.params.side n) (x : X) (hb : (G.settingOf (γ x)).bases = b) :
    G.settingOf (γ x) = settingOfParts G.coarse G.region (G.recordedSites ∪ supportSites H) (freeBondsUnder G H)
      (badBondsUnder G H) b (G.settingOf (γ x)).fine
      (fun z => (G.settingOf (γ x)).labelling ⟨z.1, (support_settingOf G γ H hH x).symm ▸ z.2⟩) :=
  eq_settingOfParts (G.settingOf (γ x)) (support_settingOf G γ H hH x) (free_settingOf G γ H hH x)
    (bad_settingOf G γ H hH x) hb
omit hγ [MeasurableSpace X] in
theorem settingWithFamily_eq_parts (b : BaseChoice R.params.side n) (x : X) (hb : (G.settingOf (γ x)).bases = b) :
    G.settingWithFamily (γ x) = settingOfParts G.coarse G.region (G.recordedSites ∪ supportSites H)
      (freeBondsUnder G H) (badBondsUnder G H) b (G.settingWithFamily (γ x)).fine
      (fun z => (G.settingOf (γ x)).labelling ⟨z.1, (support_settingOf G γ H hH x).symm ▸ z.2⟩) :=
  eq_settingOfParts (G.settingWithFamily (γ x)) (support_settingOf G γ H hH x) (free_settingOf G γ H hH x)
    (bad_settingOf G γ H hH x) hb
theorem measurable_settingOf_fine (b : BaseChoice R.params.side n) (hb : ∀ x, (G.settingOf (γ x)).bases = b) :
    Measurable fun x => (G.settingOf (γ x)).fine := by
  have e : (fun x => (G.settingOf (γ x)).fine) = fun x =>
      (settingOfParts G.coarse G.region (G.recordedSites ∪ supportSites H) (freeBondsUnder G H) (badBondsUnder G H) b
        (G.settingWithFamily (γ x)).fine
        (fun z => (G.settingOf (γ x)).labelling ⟨z.1, (support_settingOf G γ H hH x).symm ▸ z.2⟩)).field 0 :=
    funext fun x => congrArg (fun s : ChartSetting R n => s.field 0) (settingWithFamily_eq_parts G γ H hH b x (hb x))
  rw [e]
  have h1 := measurable_field_prod G.coarse G.region (G.recordedSites ∪ supportSites H) (freeBondsUnder G H)
    (badBondsUnder G H) b (fun x => (G.settingWithFamily (γ x)).fine)
    (fun x z => (G.settingOf (γ x)).labelling ⟨z.1, (support_settingOf G γ H hH x).symm ▸ z.2⟩)
    (measurable_settingWithFamily_fine G γ H hγ hH)
  have h0 : Measurable fun x : X => (x, (0 : FreeCoords (freeBondsUnder G H))) := measurable_id.prodMk measurable_const
  have h2 := h1.comp h0
  exact h2
variable
  (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
    R.siteDensity)
  (hside : IsBlockTorusSide R.params (n * R.params.side))
  (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0) (hS : SharesSumToAction)
  (hM : MeasurableContourMeanStatement) (hp : IsCutoff R.ballRadius R.barrierFn) (ha : 0 ≤ R.params.coupling)
  (hL : 0 < R.params.side) (hm : 2 ≤ n * R.params.side)
include hr hside hflat hS hM hp ha hL hm in
theorem measurable_settingMass_gas (b : BaseChoice R.params.side n) (hb : ∀ x, (G.settingOf (γ x)).bases = b)
    (hs : ∀ x, (G.settingOf (γ x)).IsAdmissible) : Measurable fun x => settingMass (G.settingOf (γ x)) := by
  have hs' : ∀ x, (settingOfParts G.coarse G.region (G.recordedSites ∪ supportSites H) (freeBondsUnder G H)
      (badBondsUnder G H) b (G.settingOf (γ x)).fine
      (fun z => (G.settingOf (γ x)).labelling ⟨z.1, (support_settingOf G γ H hH x).symm ▸ z.2⟩)).IsAdmissible :=
    fun x => (settingOf_eq_parts G γ H hH b x (hb x)) ▸ hs x
  have hm' := measurable_settingMass_family G.coarse G.region (G.recordedSites ∪ supportSites H)
    (freeBondsUnder G H) (badBondsUnder G H) b hr hside hflat hS hM hp ha hL hm
    (fun x => (G.settingOf (γ x)).fine)
    (fun x z => (G.settingOf (γ x)).labelling ⟨z.1, (support_settingOf G γ H hH x).symm ▸ z.2⟩)
    (measurable_settingOf_fine G γ H hγ hH b hb) (measurable_labelling G γ H hγ hH) hs'
  have e : (fun x => settingMass (G.settingOf (γ x))) = fun x =>
      settingMass (settingOfParts G.coarse G.region (G.recordedSites ∪ supportSites H) (freeBondsUnder G H)
        (badBondsUnder G H) b (G.settingOf (γ x)).fine
        (fun z => (G.settingOf (γ x)).labelling ⟨z.1, (support_settingOf G γ H hH x).symm ▸ z.2⟩)) :=
    funext fun x => congrArg settingMass (settingOf_eq_parts G γ H hH b x (hb x))
  rw [e]
  exact hm'
end Gas
section Top
variable [NeZero n] (G : GasGround R n)
theorem measurable_familyOf (θ : GasSupport R n) : Measurable fun σ : G.Config => G.familyOf σ θ := by
  classical
  by_cases h : G.IsGasSupport θ
  · have e : (fun σ : G.Config => G.familyOf σ θ) = fun σ =>
        Sum.elim (fun u => Sum.inl u) (fun s : G.SpinState ⟨θ, h⟩ => Sum.inr s.1) (σ ⟨θ, h⟩) := by
      funext σ
      unfold GasGround.familyOf
      rw [dif_pos h]
      cases σ ⟨θ, h⟩ <;> rfl
    rw [e]
    exact (measurable_inl.sumElim (measurable_inr.comp measurable_subtype_coe)).comp (measurable_pi_apply _)
  · have e : (fun σ : G.Config => G.familyOf σ θ) = fun _ => Sum.inl () := by
      funext σ
      unfold GasGround.familyOf
      rw [dif_neg h]
    rw [e]
    exact measurable_const
theorem measurableSet_vacant (i : G.GasSpin) : MeasurableSet {σ : G.Config | σ i = Sum.inl ()} := by
  have e : {σ : G.Config | σ i = Sum.inl ()} =
      (fun σ : G.Config => σ i) ⁻¹' Set.range (Sum.inl : Unit → G.SpinValue i) := by
    ext σ
    constructor
    · intro h
      exact ⟨(), Eq.symm h⟩
    · rintro ⟨u, h⟩
      exact Eq.symm h
  rw [e]
  exact measurable_pi_apply i measurableSet_range_inl
theorem measurableSet_admissible : MeasurableSet {σ : G.Config | G.pairConstraint.IsAdmissible σ} := by
  have e : {σ : G.Config | G.pairConstraint.IsAdmissible σ} = ⋂ (i : G.GasSpin) (j : G.GasSpin) (_ : i ≠ j),
      ({σ : G.Config | σ i = Sum.inl ()} ∪
        ({σ : G.Config | σ j = Sum.inl ()} ∪ {_σ : G.Config | i.1.FarApart j.1})) := by
    ext σ
    simp only [Set.mem_iInter]
    exact Iff.rfl
  rw [e]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    (measurableSet_vacant G i).union ((measurableSet_vacant G j).union (MeasurableSet.const _))
theorem measurableSet_occupies (θ : GasSupport R n) : MeasurableSet {σ : G.Config | (G.familyOf σ).Occupies θ} := by
  have e : {σ : G.Config | (G.familyOf σ).Occupies θ} =
      (fun σ : G.Config => G.familyOf σ θ) ⁻¹'
        Set.range (Sum.inr : SupportState θ → WithNone (SupportState θ)) := by
    ext σ
    constructor
    · intro h
      exact ⟨_, (Sum.inr_getRight _ h)⟩
    · rintro ⟨u, h⟩
      have h' : G.familyOf σ θ = Sum.inr u := h.symm
      show (G.familyOf σ θ).isRight = true
      rw [h']
      rfl
  rw [e]
  exact measurable_familyOf G θ measurableSet_range_inr
def occupancyPiece (H : Set (GasSupport R n)) : Set G.Config :=
  {σ | G.pairConstraint.IsAdmissible σ ∧ ∀ θ, (G.familyOf σ).Occupies θ ↔ θ ∈ H}
theorem measurableSet_occupancyPiece (H : Set (GasSupport R n)) : MeasurableSet (occupancyPiece G H) := by
  classical
  have e : occupancyPiece G H = {σ : G.Config | G.pairConstraint.IsAdmissible σ} ∩
      ⋂ θ : GasSupport R n, {σ : G.Config | (G.familyOf σ).Occupies θ ↔ θ ∈ H} := by
    ext σ
    simp only [occupancyPiece, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [e]
  refine (measurableSet_admissible G).inter (MeasurableSet.iInter fun θ => ?_)
  by_cases hθ : θ ∈ H
  · simp only [hθ, iff_true]
    exact measurableSet_occupies G θ
  · simp only [hθ, iff_false]
    exact (measurableSet_occupies G θ).compl
theorem countable_baseChoice (L n : ℕ) [NeZero L] [NeZero n] : Countable (BaseChoice L n) := by
  have h1 := finite_cell L n
  have h2 : ∀ i : Fin 4, Finite (ZMod ((stepBlockFrame L n).period 0 i)) := fun i =>
    @Finite.of_fintype _ (@ZMod.fintype _ inferInstance)
  have h3 : Finite ((stepBlockFrame L n).Site 0) := @Pi.finite _ _ _ h2
  exact (@Pi.finite _ _ h1 fun _ => h3).to_countable
variable
  (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
    R.siteDensity)
  (hside : IsBlockTorusSide R.params (n * R.params.side))
  (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0) (hS : SharesSumToAction)
  (hM : MeasurableContourMeanStatement) (hp : IsCutoff R.ballRadius R.barrierFn) (ha : 0 ≤ R.params.coupling)
  (hL : 0 < R.params.side) (hm : 2 ≤ n * R.params.side)
  (hset : ∀ σ : G.Config, G.pairConstraint.IsAdmissible σ → (G.settingOf (G.familyOf σ)).IsAdmissible)
include hr hside hflat hS hM hp ha hL hm hset
theorem measurable_settingMass_occupancyPiece (H : Set (GasSupport R n)) :
    Measurable fun a : occupancyPiece G H => settingMass (G.settingOf (G.familyOf a.1)) := by
  have hcount := countable_baseChoice R.params.side n
  have hγ : ∀ θ, Measurable fun a : occupancyPiece G H => G.familyOf a.1 θ := fun θ =>
    (measurable_familyOf G θ).comp measurable_subtype_coe
  have hH : ∀ (a : occupancyPiece G H) θ, (G.familyOf a.1).Occupies θ ↔ θ ∈ H := fun a => a.2.2
  refine measurable_of_iUnion_cover
    (fun b : BaseChoice R.params.side n => {a : occupancyPiece G H | (G.settingOf (G.familyOf a.1)).bases = b})
    (fun b => measurableSet_bases_eq G (fun a : occupancyPiece G H => G.familyOf a.1) H hγ hH b)
    (fun a => ⟨_, rfl⟩) fun b => ?_
  refine measurable_settingMass_gas G
    (fun a : {a : occupancyPiece G H | (G.settingOf (G.familyOf a.1)).bases = b} => G.familyOf a.1.1) H
    (fun θ => (hγ θ).comp measurable_subtype_coe) (fun a => hH a.1) hr hside hflat hS hM hp ha hL hm b
    (fun a => a.2) (fun a => hset _ a.1.2.1)
theorem measurable_weight : Measurable G.weight := by
  classical
  refine measurable_of_iUnion_cover (ι := Option (Set (GasSupport R n)))
    (fun o => o.elim {σ : G.Config | ¬ G.pairConstraint.IsAdmissible σ} (occupancyPiece G)) ?_ ?_ ?_
  · rintro (_ | H)
    · exact (measurableSet_admissible G).compl
    · exact measurableSet_occupancyPiece G H
  · intro σ
    by_cases h : G.pairConstraint.IsAdmissible σ
    · exact ⟨some {θ | (G.familyOf σ).Occupies θ}, h, fun θ => Iff.rfl⟩
    · exact ⟨none, h⟩
  · rintro (_ | H)
    · have e : (fun a : {σ : G.Config | ¬ G.pairConstraint.IsAdmissible σ} => G.weight a.1) = fun _ => 0 :=
        funext fun a => if_neg a.2
      exact e ▸ measurable_const
    · have e : (fun a : occupancyPiece G H => G.weight a.1) =
          fun a => (settingMass (G.settingOf (G.familyOf a.1))).toReal :=
        funext fun a => if_pos a.2.1
      have h := ENNReal.measurable_toReal.comp
        (measurable_settingMass_occupancyPiece G hr hside hflat hS hM hp ha hL hm hset H)
      exact e ▸ h
end Top
end GasWeight
theorem gasWeightMeasurable_holds (hC : GasConfigIsAdmissibleSetting)
    (hM : MeasurableContourMeanStatement) (hS : SharesSumToAction) :
    GasWeightMeasurable := by
  intro T hT
  obtain ⟨y₀, hy⟩ := hC T hT
  refine ⟨y₀, fun y hy0 R hR hx n _ G hG => ?_⟩
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
  exact GasWeight.measurable_weight G hrow.2 hside hflat hS hM hp ha hLpos hm hset
end YangMills.Construction.ClusterExpansionOfAStep
end
