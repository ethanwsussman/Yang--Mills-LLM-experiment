import YangMills.Construction.ClusterExpansionOfAStep.CasesOfAFamilyProof
import YangMills.Construction.ClusterExpansionOfAStep.FactorOfAClassIsBorelProof
import YangMills.Construction.ClusterExpansionOfAStep.HullStatesAreGrounds
import YangMills.Construction.ClusterExpansionOfAStep.WeightOfTheGasIsBorelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames Dobrushin TorusFields TorusLumps StepGas StepSettings
  StepCosts StateMeasurability RenormalizationStepParameters ColdChain MarkedIntegrals StepFrames BlockTrees
namespace ClusterExpansionOfAStep
namespace GroundDensityMeasurability
theorem lintegral_pi_prod_factors {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, MeasurableSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, SigmaFinite (μ i)] (h : ∀ i, E i → ℝ≥0∞)
    (hh : ∀ i, Measurable (h i)) :
    ∫⁻ x, ∏ i, h i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, h i x ∂μ i := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.FamilyCaseSum.lintegral_pi_prod_apply_eq_prod <;> assumption
theorem pi_withDensity_prod {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, MeasurableSpace (E i)]
    (ν : ∀ i, Measure (E i)) [∀ i, SigmaFinite (ν i)] (d : ∀ i, E i → ℝ) (hd : ∀ i, Measurable (d i)) :
    Measure.pi (fun i => (ν i).withDensity fun x => ENNReal.ofReal (d i x)) =
      (Measure.pi ν).withDensity fun x => ∏ i, ENNReal.ofReal (d i (x i)) := by
  classical
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have e : (Set.univ.pi s).indicator (fun x : ∀ i, E i => ∏ i, ENNReal.ofReal (d i (x i))) =
      fun x => ∏ i, (s i).indicator (fun y => ENNReal.ofReal (d i y)) (x i) := by
    funext x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by simpa [Set.mem_univ_pi] using hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [e]
  refine (lintegral_pi_prod_factors ν (fun i => (s i).indicator fun y => ENNReal.ofReal (d i y))
    fun i => (ENNReal.measurable_ofReal.comp (hd i)).indicator (hs i)).trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]
theorem lintegral_pi_transport {ι : Type} [Fintype ι] {A B : ι → Type} [∀ i, MeasurableSpace (A i)]
    [∀ i, MeasurableSpace (B i)] (m : ∀ i, Measure (A i)) (ν : ∀ i, Measure (B i))
    [∀ i, SigmaFinite (ν i)] (e : ∀ i, A i → B i) (he : ∀ i, Measurable (e i))
    (d : ∀ i, B i → ℝ) (hd : ∀ i, Measurable (d i))
    (h : ∀ i, Measure.map (e i) (m i) = (ν i).withDensity fun x => ENNReal.ofReal (d i x))
    (F : (∀ i, B i) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ σ, F (fun i => e i (σ i)) ∂Measure.pi m =
      ∫⁻ τ, (∏ i, ENNReal.ofReal (d i (τ i))) * F τ ∂Measure.pi ν := by
  have : ∀ i, SigmaFinite (Measure.map (e i) (m i)) := fun i => by
    rw [h i]
    infer_instance
  have hD : Measurable fun τ : ∀ i, B i => ∏ i, ENNReal.ofReal (d i (τ i)) :=
    Finset.measurable_prod _ fun i _ =>
      ENNReal.measurable_ofReal.comp ((hd i).comp (measurable_pi_apply i))
  have hE : Measurable fun (σ : ∀ i, A i) i => e i (σ i) :=
    measurable_pi_lambda _ fun i => (he i).comp (measurable_pi_apply i)
  have h0 : ∫⁻ σ, F (fun i => e i (σ i)) ∂Measure.pi m =
      ∫⁻ τ, F τ ∂Measure.map (fun (σ : ∀ i, A i) i => e i (σ i)) (Measure.pi m) :=
    (lintegral_map hF hE).symm
  rw [h0, Measure.pi_map_pi fun i => (he i).aemeasurable,
    show (fun i => Measure.map (e i) (m i)) = fun i => (ν i).withDensity fun x => ENNReal.ofReal (d i x) from
      funext h, pi_withDensity_prod ν d hd, lintegral_withDensity_eq_lintegral_mul _ hD hF]
  rfl
theorem measurable_withNone_of_sides {X S β : Type} [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace β]
    {f : X × WithNone S → β} (h1 : Measurable fun x => f (x, Sum.inl ()))
    (h2 : Measurable fun y : X × S => f (y.1, Sum.inr y.2)) : Measurable f := by
  have e : f = (Sum.elim (fun p : X × Unit => f (p.1, Sum.inl ()))
      (fun y : X × S => f (y.1, Sum.inr y.2))) ∘ MeasurableEquiv.prodSumDistrib X Unit S := by
    funext ⟨x, m⟩
    rcases m with u | s <;> rfl
  rw [e]
  exact ((h1.comp measurable_fst).sumElim h2).comp (MeasurableEquiv.measurable _)
theorem withDensity_map_inl_dirac {α : Type} [MeasurableSpace α] (f : WithNone α → ℝ≥0∞) (hf : Measurable f)
    (h : f (Sum.inl ()) = 1) :
    (Measure.map (Sum.inl : Unit → WithNone α) (Measure.dirac ())).withDensity f =
      Measure.map Sum.inl (Measure.dirac ()) := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.map_apply measurable_inl hs, ← lintegral_indicator hs,
    lintegral_map (hf.indicator hs) measurable_inl, lintegral_dirac]
  by_cases hu : (Sum.inl () : WithNone α) ∈ s
  · rw [Set.indicator_of_mem hu, h, Measure.dirac_apply]
    simp [hu]
  · rw [Set.indicator_of_notMem hu, Measure.dirac_apply]
    simp [hu]
def withNoneDensity {S : Type} (A : Set S) (g : S → ℝ) (m : WithNone S) : ℝ :=
  open Classical in Sum.elim (fun _ => 1) (fun s => if s ∈ A then g s else 0) m
def forgetSubtype {S : Type} {P : S → Prop} (m : WithNone {s // P s}) : WithNone S := Sum.map id Subtype.val m
theorem measurable_forgetSubtype {S : Type} [MeasurableSpace S] {P : S → Prop} :
    Measurable (forgetSubtype : WithNone {s // P s} → WithNone S) :=
  measurable_inl.sumElim (measurable_inr.comp measurable_subtype_coe)
theorem map_forgetSubtype_withNoneMeasure {S : Type} [MeasurableSpace S] (μ : Measure S) (P : S → Prop)
    (hP : MeasurableSet {s | P s}) (g : S → ℝ) (hg : Measurable g) (hm : Measurable (withNoneDensity {s | P s} g)) :
    Measure.map (forgetSubtype : WithNone {s // P s} → WithNone S)
      (withNoneMeasure ((μ.comap (Subtype.val : {s // P s} → S)).withDensity fun s => ENNReal.ofReal (g s.1))) =
    (withNoneMeasure μ).withDensity fun m => ENNReal.ofReal (withNoneDensity {s | P s} g m) := by
  classical
  have hd : Measurable fun m => ENNReal.ofReal (withNoneDensity {s | P s} g m) :=
    ENNReal.measurable_ofReal.comp hm
  unfold withNoneMeasure
  rw [Measure.map_add _ _ measurable_forgetSubtype, withDensity_add_measure,
    withDensity_map_inl_dirac _ hd (by simp [withNoneDensity]),
    Measure.map_map measurable_forgetSubtype measurable_inl,
    Measure.map_map measurable_forgetSubtype measurable_inr]
  congr 1
  ext t ht
  have hmi : Measurable ((forgetSubtype : WithNone {s // P s} → WithNone S) ∘ Sum.inr) :=
    measurable_forgetSubtype.comp measurable_inr
  rw [Measure.map_apply hmi ht, withDensity_apply _ (hmi ht), withDensity_apply _ ht,
    ← lintegral_indicator (hmi ht), ← lintegral_indicator ht,
    lintegral_map (hd.indicator ht) measurable_inr]
  have e1 : (((forgetSubtype : WithNone {s // P s} → WithNone S) ∘ Sum.inr) ⁻¹' t).indicator
      (fun s : {s // P s} => ENNReal.ofReal (g s.1)) = fun s =>
      ((Sum.inr ⁻¹' t : Set S).indicator fun y => ENNReal.ofReal (g y)) s.1 := by
    funext s
    by_cases h : (Sum.inr s.1 : WithNone S) ∈ t
    · rw [Set.indicator_of_mem (show s ∈ _ from h), Set.indicator_of_mem (show s.1 ∈ _ from h)]
    · rw [Set.indicator_of_notMem (show s ∉ _ from h), Set.indicator_of_notMem (show s.1 ∉ _ from h)]
  rw [e1]
  have e2 := lintegral_subtype_comap (μ := μ) hP ((Sum.inr ⁻¹' t : Set S).indicator fun y => ENNReal.ofReal (g y))
  refine Eq.trans e2 ?_
  rw [← lintegral_indicator hP]
  refine lintegral_congr fun y => ?_
  by_cases h : (Sum.inr y : WithNone S) ∈ t <;> by_cases h' : y ∈ {s | P s}
  · rw [Set.indicator_of_mem h', Set.indicator_of_mem (show y ∈ _ from h), Set.indicator_of_mem h]
    simp [withNoneDensity, show P y from h']
  · rw [Set.indicator_of_notMem h', Set.indicator_of_mem h]
    simp [withNoneDensity, show ¬ P y from h']
  · rw [Set.indicator_of_mem h', Set.indicator_of_notMem (show y ∉ _ from h), Set.indicator_of_notMem h]
  · rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]
theorem measurable_getRight_of_isRight {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → Unit ⊕ β}
    (hf : Measurable f) (h : ∀ a, (f a).isRight = true) : Measurable fun a => (f a).getRight (h a) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurable_sum_getRight <;> assumption
variable {n : ℕ}
theorem measurable_gaugeAt {R : StepSetup} (x : TorusSite (n * R.params.side)) :
    Measurable fun W : TorusField (n * R.params.side) => gaugeAt (R := R) W x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.measurable_gaugeAt <;> assumption
variable {R : StepSetup}
abbrev mkSetting (V : TorusField n) (top : Finset (TorusSite n)) (Yt : Finset (TorusSite (n * R.params.side)))
    (free bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (base : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) :
    ChartSetting R n :=
  ⟨V, top, base, Yt, ω, b, free, bad⟩
theorem eq_mkSetting (s : ChartSetting R n) {Y : Finset (TorusSite (n * R.params.side))}
    {F Bd : Finset (TorusBond (n * R.params.side))}
    {b : BaseChoice R.params.side n} (hY : s.support = Y) (hF : s.free = F) (hBd : s.bad = Bd) (hb : s.bases = b) :
    s = mkSetting s.coarse s.region Y F Bd b s.fine (fun z => s.labelling ⟨z.1, hY ▸ z.2⟩) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.eq_settingOfParts <;> assumption
theorem measurable_toCoords_of {Z : Type} [MeasurableSpace Z] {w : Z → imaginaryQuaternions}
    (hw : MeasurableQuaternion fun z => ((w z : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable fun z => toCoords (w z) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.measurable_toCoords <;> assumption
theorem toImaginary_add_toImaginary (a b : EuclideanSpace ℝ (Fin 3)) :
    toImaginary a + toImaginary b = toImaginary (a + b) := by
  apply Subtype.ext
  show ((toImaginary a : imaginaryQuaternions) : ℍ[ℝ]) + ((toImaginary b : imaginaryQuaternions) : ℍ[ℝ]) =
    ((toImaginary (a + b) : imaginaryQuaternions) : ℍ[ℝ])
  ext
  · show (0 : ℝ) + 0 = 0
    simp
  · show a 0 + b 0 = (a + b) 0
    simp
  · show a 1 + b 1 = (a + b) 1
    simp
  · show a 2 + b 2 = (a + b) 2
    simp
theorem measurable_expUnit_add {Z : Type} [MeasurableSpace Z] {w : Z → imaginaryQuaternions}
    (hw : MeasurableQuaternion fun z => ((w z : imaginaryQuaternions) : ℍ[ℝ])) {v : Z → EuclideanSpace ℝ (Fin 3)}
    (hv : Measurable v) : Measurable fun z => expUnit (w z + toImaginary (v z)) := by
  have e : (fun z => expUnit (w z + toImaginary (v z))) = fun z =>
      (fun u : EuclideanSpace ℝ (Fin 3) => expUnit (toImaginary u)) (toCoords (w z) + v z) := by
    funext z
    show expUnit (w z + toImaginary (v z)) = expUnit (toImaginary (toCoords (w z) + v z))
    rw [← toImaginary_add_toImaginary, toImaginary_toCoords]
  rw [e]
  exact (continuous_expUnit.comp continuous_toImaginary).measurable.comp ((measurable_toCoords_of hw).add hv)
section Chart
variable {Z : Type} [MeasurableSpace Z]
open Classical in
theorem measurable_chartLink_family {V : Z → TorusField n} {B : Z → TorusField (n * R.params.side)}
    {w : Z → imaginaryQuaternions} {v : Z → EuclideanSpace ℝ (Fin 3)}
    (hV : Measurable V) (hB : Measurable B) (hw : MeasurableQuaternion fun z => ((w z : imaginaryQuaternions) : ℍ[ℝ]))
    (hv : Measurable v) (y : TorusSite (n * R.params.side)) (i : Fin 4) :
    Measurable fun z => (gaugeAt (R := R) (B z) y)⁻¹ *
      (if IsCrossingBond (F := stepBlockFrame R.params.side n) (torusSiteInFrame (stepBlockFrame R.params.side n) 0 y, i)
        then expUnit (w z + toImaginary (v z)) * V z (parentBlock R.params.side y) i
        else expUnit (w z + toImaginary (v z))) *
      gaugeAt (R := R) (B z) (y + TorusFields.unitStep (n * R.params.side) i) := by
  have t1 : ∀ u : TorusSite (n * R.params.side), Measurable fun z => gaugeAt (R := R) (B z) u :=
    fun u => (measurable_gaugeAt u).comp hB
  have h2 := measurable_expUnit_add hw hv
  refine ((t1 y).inv.mul ?_).mul (t1 _)
  by_cases hc : IsCrossingBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 y, i)
  · simp only [if_pos hc]
    exact h2.mul ((measurable_pi_apply i).comp ((measurable_pi_apply _).comp hV))
  · simp only [if_neg hc]
    exact h2
theorem measurable_field_family {X : Type} [MeasurableSpace X] (V : X → TorusField n) (top : X → Finset (TorusSite n))
    (Yt : Finset (TorusSite (n * R.params.side))) (free bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n)
    (base : X → TorusField (n * R.params.side)) (ω : X → Yt → R.labels.Ω) (hV : Measurable V) (hb : Measurable base)
    (hfr : ∀ e ∈ free, MeasurableQuaternion fun x =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (V x) e : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable fun p : X × FreeCoords free =>
      (mkSetting (V p.1) (top p.1) Yt free bad b (base p.1) (ω p.1)).field p.2 := by
  classical
  refine measurable_pi_iff.mpr fun y => measurable_pi_iff.mpr fun i => ?_
  by_cases h : (y, i) ∈ free
  · simp only [ChartSetting.field, dif_pos h, chartLink]
    have hf := hfr _ h
    exact measurable_chartLink_family (R := R) (V := fun p : X × FreeCoords free => V p.1)
      (B := fun p => base p.1)
      (w := fun p => frameCoord R.params R.anchorRadius R.depth R.frameReach (V p.1) (y, i))
      (v := fun p => p.2 ⟨(y, i), h⟩) (hV.comp measurable_fst) (hb.comp measurable_fst)
      ⟨hf.1.comp measurable_fst, hf.2.1.comp measurable_fst, hf.2.2.1.comp measurable_fst,
        hf.2.2.2.comp measurable_fst⟩ ((measurable_pi_apply _).comp measurable_snd) y i
  · simp only [ChartSetting.field, dif_neg h]
    exact (measurable_pi_apply i).comp ((measurable_pi_apply y).comp (hb.comp measurable_fst))
theorem measurable_frameField_family (free : Finset (TorusBond (n * R.params.side))) {V : Z → TorusField n}
    {B : Z → TorusField (n * R.params.side)}
    (hV : Measurable V) (hB : Measurable B)
    (hfr : ∀ e ∈ free, MeasurableQuaternion fun z =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (V z) e : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable fun z => frameField R free (V z) (B z) := by
  classical
  refine measurable_pi_iff.mpr fun y => measurable_pi_iff.mpr fun i => ?_
  unfold frameField
  by_cases h : (y, i) ∈ free
  · simp only [if_pos h]
    exact measurable_chartLink_family (R := R) hV hB (hfr _ h) measurable_const y i
  · simp only [if_neg h]
    exact (measurable_pi_apply i).comp ((measurable_pi_apply y).comp hB)
end Chart
section WilsonWeightSeriesExpansion
variable [NeZero n]
theorem sum_sitesInBlocks (L : ℕ) [NeZero L] (f : TorusSite (n * L) → ℝ) :
    ∑ Y : TorusSite n, ∑ y ∈ sitesInBlocks L {Y}, f y = ∑ y, f y := by apply _root_.YangMills.Construction.FreeBonds.sum_sitesInBlocks_singleton <;> assumption
theorem sum_levelShare_eq (hS : SharesSumToAction) (a : ℝ) (L t m : ℕ) [NeZero m] (S : Finset (TorusSite m))
    (W : TorusField m) (ha : 0 ≤ a) (hL : 0 < L) (hm : 2 ≤ m) :
    ∑ y, levelShare a L t S y W = actionAtLevel a L t S W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.sum_levelShare <;> assumption
def fitSum (ℓ : TorusLumps.StepParameters) (W : TorusField (n * ℓ.side)) (V : TorusField n)
    (b : BaseChoice ℓ.side n) : ℝ :=
  ∑ Y : TorusSite n, ℓ.coupling / 2 * ∑ i : Fin 4, (bondFit ℓ W V b (Y, i) + bondFit ℓ W V b (Y - TorusFields.unitStep n i, i))
theorem exp_neg_potential_eq
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0) (hS : SharesSumToAction)
    (ha : 0 ≤ R.params.coupling)
    (hL : 0 < R.params.side) (hm : 2 ≤ n * R.params.side) (s : ChartSetting R n) (η : FreeCoords s.free)
    (hh : IsHullState R.params R.range (s.field η) s.support)
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
theorem measurable_bondFit_pair (hM : MeasurableContourMeanStatement) (ℓ : TorusLumps.StepParameters)
    (b : BaseChoice ℓ.side n) (c : TorusBond n) :
    Measurable fun p : TorusField (n * ℓ.side) × TorusField n => bondFit ℓ p.1 p.2 b c := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.measurable_bondFit <;> assumption
theorem measurable_meanNorm (hM : MeasurableContourMeanStatement) (ℓ : TorusLumps.StepParameters)
    (b : BaseChoice ℓ.side n) (c : TorusBond n) : Measurable fun W : TorusField (n * ℓ.side) => meanNorm ℓ W b c :=
  hM ℓ n b (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) (fun q => ‖q‖) continuous_norm
theorem measurable_fitSum_pair (hM : MeasurableContourMeanStatement) (ℓ : TorusLumps.StepParameters)
    (b : BaseChoice ℓ.side n) :
    Measurable fun p : TorusField (n * ℓ.side) × TorusField n => fitSum ℓ p.1 p.2 b := by
  unfold fitSum
  refine Finset.measurable_sum _ fun Y _ => measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
  exact (measurable_bondFit_pair hM ℓ b _).add (measurable_bondFit_pair hM ℓ b _)
end WilsonWeightSeriesExpansion
section Mass
variable [NeZero n] (V : TorusField n) (top : Finset (TorusSite n))
  (Yt : Finset (TorusSite (n * R.params.side))) (free bad : Finset (TorusBond (n * R.params.side)))
  (b : BaseChoice R.params.side n)
def logJacobianSum (W : TorusField (n * R.params.side)) (η : FreeCoords free) : ℝ :=
  open Classical in
  ∑ Y : TorusSite n, (∑ i : Fin 4, logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params W b (Y, i)) +
    ∑ e : free, if bondBlock (R := R) e.1 = Y then
      Real.log (haarLogDensity
        (toCoords (frameCoord R.params R.anchorRadius R.depth R.frameReach V e.1) + η e)) else 0)
def hullLabelWeight (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) : ℝ :=
  open Classical in
  if IsHullState R.params (clusterRange R.coupling) W Yt then R.labelWeight (n * R.params.side) W Yt ω else 0
def massDensity (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) (η : FreeCoords free) : ℝ :=
  (∏ e : free, cutoffFactor R.ballRadius R.barrierFn (coordNorm (η e))) *
    ((hullLabelWeight Yt W ω /
      (R.functional (n * R.params.side) (trivialField _) *
        ∏ Z ∈ chainComponents R.range Yt, R.clusterFactor (n * R.params.side) W Yt ω Z)) *
        Real.exp (-(R.coupling * fitSum R.params W V b) + logJacobianSum V free b W η))
theorem cutoffProduct_mul_exp_eq
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0) (hS : SharesSumToAction)
    (ha : 0 ≤ R.params.coupling)
    (hL : 0 < R.params.side) (hm : 2 ≤ n * R.params.side) (base : TorusField (n * R.params.side))
    (ω : Yt → R.labels.Ω)
    (hs : (mkSetting V top Yt free bad b base ω).IsAdmissible) (η : FreeCoords free) :
    (mkSetting V top Yt free bad b base ω).cutoffProduct η *
        Real.exp (-(mkSetting V top Yt free bad b base ω).potential η) =
      massDensity V Yt free b ((mkSetting V top Yt free bad b base ω).field η) ω η := by
  classical
  unfold massDensity
  by_cases hη : (mkSetting V top Yt free bad b base ω).InBalls η
  · have hh := hs.isHull η hη
    have hΦ := hs.factor_ne_zero η hη
    rw [exp_neg_potential_eq hr hside hflat hS ha hL hm (mkSetting V top Yt free bad b base ω) η hh hΦ]
    have hh' : IsHullState R.params (clusterRange R.coupling)
        ((mkSetting V top Yt free bad b base ω).field η) Yt := hh
    have hg : hullLabelWeight Yt ((mkSetting V top Yt free bad b base ω).field η) ω =
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
end Mass
section MassJoint
variable [NeZero n] {Z : Type} [MeasurableSpace Z] (Yt : Finset (TorusSite (n * R.params.side)))
  (free bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
theorem measurable_logJacobianSum (hM : MeasurableContourMeanStatement) (V : Z → TorusField n)
    (W : Z → TorusField (n * R.params.side))
    (η : Z → FreeCoords free) (hW : Measurable W) (hη : Measurable η)
    (hfr : ∀ e ∈ free, MeasurableQuaternion fun z =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (V z) e : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable fun z => logJacobianSum (V z) free b (W z) (η z) := by
  classical
  unfold logJacobianSum
  refine Finset.measurable_sum _ fun Y _ => ?_
  refine (Finset.measurable_sum _ fun i _ => ?_).add (Finset.measurable_sum _ fun e _ => ?_)
  · exact measurable_logPartitionGap.comp (measurable_const.mul ((measurable_meanNorm hM R.params b _).comp hW))
  · by_cases hY : bondBlock (R := R) e.1 = Y
    · simp only [if_pos hY]
      have h1 : Measurable fun z =>
          toCoords (frameCoord R.params R.anchorRadius R.depth R.frameReach (V z) e.1) + η z e :=
        (measurable_toCoords_of (hfr e.1 e.2)).add ((measurable_pi_apply e).comp hη)
      exact Real.measurable_log.comp (measurable_haarLogDensity.comp h1)
    · simp only [if_neg hY]
      exact measurable_const
theorem measurable_massDensity
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hM : MeasurableContourMeanStatement) (hp : IsCutoff R.ballRadius R.barrierFn) (V : Z → TorusField n)
    (W : Z → TorusField (n * R.params.side))
    (ω : Z → Yt → R.labels.Ω) (η : Z → FreeCoords free) (hV : Measurable V) (hW : Measurable W)
    (hω : Measurable ω) (hη : Measurable η)
    (hfr : ∀ e ∈ free, MeasurableQuaternion fun z =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (V z) e : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable fun z => massDensity (V z) Yt free b (W z) (ω z) (η z) := by
  classical
  have hWω : Measurable fun z => (W z, ω z) := hW.prodMk hω
  obtain ⟨bD, bΦ, -⟩ := hr.borel (n * R.params.side) hside Yt
  have h0 : Measurable fun z => ∏ e : free, cutoffFactor R.ballRadius R.barrierFn (coordNorm (η z e)) :=
    Finset.measurable_prod _ fun e _ =>
      (measurable_cutoffFactor_coordNorm hp).comp ((measurable_pi_apply e).comp hη)
  have hg : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => hullLabelWeight Yt p.1 p.2 := bD
  have h1' := hg.comp hWω
  have h1 : Measurable fun z => hullLabelWeight Yt (W z) (ω z) := h1'
  have h2 : Measurable fun z =>
      R.functional (n * R.params.side) (trivialField _) *
        ∏ Y ∈ chainComponents R.range Yt, R.clusterFactor (n * R.params.side) (W z) Yt (ω z) Y :=
    measurable_const.mul (Finset.measurable_prod _ fun Y _ => (bΦ Y).comp hWω)
  have hf0 := (measurable_fitSum_pair (n := n) hM R.params b).comp (hW.prodMk hV)
  have hf : Measurable fun z => fitSum R.params (W z) (V z) b := hf0
  have hj := measurable_logJacobianSum free b hM V W η hW hη hfr
  have h3 : Measurable fun z =>
      Real.exp (-(R.coupling * fitSum R.params (W z) (V z) b) + logJacobianSum (V z) free b (W z) (η z)) :=
    Real.measurable_exp.comp ((hf.const_mul R.coupling).neg.add hj)
  unfold massDensity
  exact h0.mul ((h1.div h2).mul h3)
theorem measurable_settingMass_family {X : Type} [MeasurableSpace X]
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0)
    (hS : SharesSumToAction) (hM : MeasurableContourMeanStatement) (hp : IsCutoff R.ballRadius R.barrierFn)
    (ha : 0 ≤ R.params.coupling) (hL : 0 < R.params.side) (hm : 2 ≤ n * R.params.side) (V : X → TorusField n)
    (top : X → Finset (TorusSite n))
    (base : X → TorusField (n * R.params.side)) (ω : X → Yt → R.labels.Ω) (hV : Measurable V) (hb : Measurable base)
    (hω : Measurable ω)
    (hfr : ∀ e ∈ free, MeasurableQuaternion fun x =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (V x) e : imaginaryQuaternions) : ℍ[ℝ]))
    (hs : ∀ x, (mkSetting (V x) (top x) Yt free bad b (base x) (ω x)).IsAdmissible) :
    Measurable fun x => settingMass (mkSetting (V x) (top x) Yt free bad b (base x) (ω x)) := by
  have hfr' : ∀ e ∈ free, MeasurableQuaternion fun p : X × FreeCoords free =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (V p.1) e : imaginaryQuaternions) : ℍ[ℝ]) :=
    fun e he =>
    ⟨(hfr e he).1.comp measurable_fst, (hfr e he).2.1.comp measurable_fst,
      (hfr e he).2.2.1.comp measurable_fst, (hfr e he).2.2.2.comp measurable_fst⟩
  have hD := measurable_massDensity Yt free b hr hside hM hp (fun p : X × FreeCoords free => V p.1)
    (fun p => (mkSetting (V p.1) (top p.1) Yt free bad b (base p.1) (ω p.1)).field p.2) (fun p => ω p.1)
    (fun p => p.2)
    (hV.comp measurable_fst) (measurable_field_family V top Yt free bad b base ω hV hb hfr)
    (hω.comp measurable_fst) measurable_snd hfr'
  have e : (fun x => settingMass (mkSetting (V x) (top x) Yt free bad b (base x) (ω x))) = fun x =>
      ∫⁻ η, ENNReal.ofReal (massDensity (V x) Yt free b
        ((mkSetting (V x) (top x) Yt free bad b (base x) (ω x)).field η) (ω x) η) := by
    funext x
    unfold settingMass
    refine lintegral_congr fun η => ?_
    rw [cutoffProduct_mul_exp_eq (V x) (top x) Yt free bad b hr hside hflat hS ha hL hm _ _ (hs x) η]
  rw [e]
  exact Measurable.lintegral_prod_right' (ν := (volume : Measure (FreeCoords free)))
    (f := fun p : X × FreeCoords free => ENNReal.ofReal
      (massDensity (V p.1) Yt free b ((mkSetting (V p.1) (top p.1) Yt free bad b (base p.1) (ω p.1)).field p.2)
        (ω p.1) p.2))
    (ENNReal.measurable_ofReal.comp hD)
end MassJoint
section Gas
variable [NeZero n] {X : Type} [MeasurableSpace X]
theorem finite_cell (L n : ℕ) [NeZero L] [NeZero n] : Finite (stepBlockFrame L n).Cell := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.finite_cell <;> assumption
theorem measurableSet_withNone {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (S : Set (WithNone α)) : MeasurableSet S :=
  And.intro (Set.to_countable (Sum.inl ⁻¹' S)).measurableSet (Set.to_countable (Sum.inr ⁻¹' S)).measurableSet
theorem choose_eq_of_iff {α : Type*} {P Q : α → Prop} (h : ∀ a, P a ↔ Q a) (hp : ∃ a, P a) (hq : ∃ a, Q a) :
    hp.choose = hq.choose := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.exists_choose_congr <;> assumption
open Classical in
def supportSites (H : Set (GasSupport R n)) : Finset (TorusSite (n * R.params.side)) :=
  (Finset.univ.filter fun θ => θ ∈ H).biUnion Prod.snd
open Classical in
def freeAfter (F₀ : Finset (TorusBond (n * R.params.side))) (H : Set (GasSupport R n)) :
    Finset (TorusBond (n * R.params.side)) :=
  F₀.filter fun e => ¬ ∃ θ : GasSupport R n, θ ∈ H ∧ e ∈ θ.coreBonds
open Classical in
def badAfter (B₀ : Finset (TorusBond (n * R.params.side))) (C₀ : Finset (TorusSite n)) (H : Set (GasSupport R n)) :
    Finset (TorusBond (n * R.params.side)) :=
  B₀ ∪ (Finset.univ.filter fun θ => θ ∈ H).biUnion Prod.fst ∪
    (chartBonds R.params.side n).filter fun b => parentBlock R.params.side b.1 ∈ C₀
structure TameFamily (Gf : X → GasGround R n) (C₀ : Finset (TorusSite n)) (Y₀ : Finset (TorusSite (n * R.params.side)))
    (B₀ F₀ : Finset (TorusBond (n * R.params.side))) (b₀ : BaseChoice R.params.side n) : Prop where
  cut_eq : ∀ x, (Gf x).cut = C₀
  sites_eq : ∀ x, (Gf x).recordedSites = Y₀
  bad_eq : ∀ x, (Gf x).recordedBad = B₀
  free_eq : ∀ x, (Gf x).freeBonds = F₀
  bases_eq : ∀ x, (Gf x).groundBases = b₀
  free_sub : F₀ ⊆ markedBonds R C₀
  measurable_coarse : Measurable fun x => (Gf x).coarse
  measurable_fine : Measurable fun x => (Gf x).state.fieldWithStoredLinks (trivialField _)
  measurable_label : ∀ z (_ : z ∈ Y₀) (h' : ∀ x, z ∈ (Gf x).recordedSites),
    Measurable fun x => (Gf x).recordedLabel ⟨z, h' x⟩
  measurable_frame : ∀ b ∈ markedBonds R C₀,
    MeasurableQuaternion fun x =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (Gf x).coarse b : imaginaryQuaternions) : ℍ[ℝ])
theorem TameFamily.comp {X' : Type} [MeasurableSpace X'] {Gf : X → GasGround R n} {C₀ : Finset (TorusSite n)}
    {Y₀ : Finset (TorusSite (n * R.params.side))} {B₀ F₀ : Finset (TorusBond (n * R.params.side))}
    {b₀ : BaseChoice R.params.side n}
    (hT : TameFamily Gf C₀ Y₀ B₀ F₀ b₀) {f : X' → X} (hf : Measurable f) :
    TameFamily (fun x => Gf (f x)) C₀ Y₀ B₀ F₀ b₀ where
  cut_eq x := hT.cut_eq (f x)
  sites_eq x := hT.sites_eq (f x)
  bad_eq x := hT.bad_eq (f x)
  free_eq x := hT.free_eq (f x)
  bases_eq x := hT.bases_eq (f x)
  free_sub := hT.free_sub
  measurable_coarse := hT.measurable_coarse.comp hf
  measurable_fine := hT.measurable_fine.comp hf
  measurable_label z h _ := (hT.measurable_label z h fun x => (hT.sites_eq x).symm ▸ h).comp hf
  measurable_frame b hb := ⟨(hT.measurable_frame b hb).1.comp hf, (hT.measurable_frame b hb).2.1.comp hf,
    (hT.measurable_frame b hb).2.2.1.comp hf, (hT.measurable_frame b hb).2.2.2.comp hf⟩
section Pick
variable (γ : X → GasFamily R n) (H : Set (GasSupport R n))
  (hγ : ∀ θ, Measurable fun x => γ x θ) (hH : ∀ x θ, (γ x).Occupies θ ↔ θ ∈ H)
include hγ hH
theorem measurable_of_chosen_support {β : Type*} [MeasurableSpace β] (Q : GasSupport R n → Prop)
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
    exact key _ hx.choose_spec (choose_eq_of_iff (fun θ => and_congr_left' (hH x θ)) hx h0)
  rw [e]
  exact (hv _ hc.2).comp (measurable_getRight_of_isRight (hγ h0.choose) _)
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
theorem measurable_fieldAt_family (e : TorusBond (n * R.params.side)) : Measurable fun x => (γ x).fieldAt e := by
  classical
  by_cases h0 : ∃ θ : GasSupport R n, θ ∈ H ∧ e ∈ θ.coreBonds
  · refine measurable_of_chosen_support γ H hγ hH (fun θ : GasSupport R n => e ∈ θ.coreBonds)
      (fun θ s h => Sum.inr (s.1 ⟨e, h⟩)) ?_ h0 _ ?_
    · intro θ h
      exact measurable_inr.comp ((measurable_pi_apply _).comp measurable_fst)
    · intro x h
      unfold GasFamily.fieldAt
      rw [dif_pos h]
  · simp only [(fieldAt_eq_inl_iff γ H hH _ e).2 h0]
    exact measurable_const
theorem measurable_baseAt_family (y : TorusSite n) : Measurable fun x => (γ x).baseAt y := by
  classical
  by_cases h0 : ∃ θ : GasSupport R n, θ ∈ H ∧ y ∈ θ.core
  · refine measurable_of_chosen_support γ H hγ hH (fun θ : GasSupport R n => y ∈ θ.core)
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
end Pick
section Family
variable {Gf : X → GasGround R n} {C₀ : Finset (TorusSite n)} {Y₀ : Finset (TorusSite (n * R.params.side))}
  {B₀ F₀ : Finset (TorusBond (n * R.params.side))} {b₀ : BaseChoice R.params.side n}
  (hT : TameFamily Gf C₀ Y₀ B₀ F₀ b₀)
  (γ : X → GasFamily R n) (H : Set (GasSupport R n))
  (hγ : ∀ θ, Measurable fun x => γ x θ) (hH : ∀ x θ, (γ x).Occupies θ ↔ θ ∈ H)
include hT hγ hH
theorem measurable_settingWithFamily_fine : Measurable fun x => ((Gf x).settingWithFamily (γ x)).fine := by
  refine measurable_pi_iff.mpr fun y => measurable_pi_iff.mpr fun i => ?_
  have e : (fun x => ((Gf x).settingWithFamily (γ x)).fine y i) = fun x =>
      getOrDefault ((γ x).fieldAt (y, i)) ((Gf x).state.fieldWithStoredLinks (trivialField _) y i) := by
    funext x
    show (match (γ x).fieldAt (y, i) with
      | Sum.inr g => g
      | Sum.inl _ => (Gf x).state.fieldWithStoredLinks (trivialField _) y i) = _
    cases (γ x).fieldAt (y, i) <;> rfl
  rw [e]
  have h2 : Measurable fun x => (Gf x).state.fieldWithStoredLinks (trivialField _) y i :=
    (measurable_pi_apply i).comp ((measurable_pi_apply y).comp hT.measurable_fine)
  have h3 := (measurable_getOrDefault (α := UnitQuaternion)).comp
    ((measurable_fieldAt_family γ H hγ hH (y, i)).prodMk h2)
  exact h3
omit hγ in
theorem support_settingOf_eq (x : X) : ((Gf x).settingOf (γ x)).support = Y₀ ∪ supportSites H := by
  show (Gf x).recordedSites ∪ (γ x).sites = _
  rw [hT.sites_eq x, sites_eq_supportSites γ H hH x]
omit hγ in
theorem free_settingOf_eq (x : X) : ((Gf x).settingOf (γ x)).free = freeAfter F₀ H := by
  classical
  show (Gf x).freeBonds.filter (fun b => (γ x).fieldAt b = Sum.inl ()) = _
  rw [hT.free_eq x]
  ext e
  simp only [freeAfter, Finset.mem_filter]
  exact and_congr_right fun _ => fieldAt_eq_inl_iff γ H hH x e
omit hγ in
theorem bad_settingOf_eq (x : X) : ((Gf x).settingOf (γ x)).bad = badAfter B₀ C₀ H := by
  classical
  show (Gf x).recordedBad ∪ (Finset.univ.filter fun θ => (γ x).Occupies θ).biUnion Prod.fst ∪
    (chartBonds R.params.side n).filter (fun b => parentBlock R.params.side b.1 ∈ (Gf x).cut) = _
  rw [hT.bad_eq x, hT.cut_eq x]
  ext e
  simp [badAfter, hH]
theorem measurable_labelling_family :
    Measurable fun (x : X) (z : (Y₀ ∪ supportSites H : Finset (TorusSite (n * R.params.side)))) =>
      ((Gf x).settingOf (γ x)).labelling ⟨z.1, (support_settingOf_eq hT γ H hH x).symm ▸ z.2⟩ := by
  classical
  refine measurable_pi_iff.mpr fun z => ?_
  by_cases hz : z.1 ∈ supportSites H
  · have hx : ∀ x, z.1 ∈ (γ x).sites := fun x => by rw [sites_eq_supportSites γ H hH x]; exact hz
    have h0 : ∃ θ : GasSupport R n, θ ∈ H ∧ z.1 ∈ θ.2 := by
      obtain ⟨θ, hθ, hzθ⟩ := Finset.mem_biUnion.mp hz
      exact ⟨θ, (Finset.mem_filter.mp hθ).2, hzθ⟩
    refine measurable_of_chosen_support γ H hγ hH (fun θ : GasSupport R n => z.1 ∈ θ.2)
      (fun θ s h => s.2.1 ⟨z.1, h⟩) ?_ h0 _ ?_
    · intro θ h
      exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
    · intro x h
      show (if h' : z.1 ∈ (γ x).sites then (γ x).labelAt h' else _) = _
      rw [dif_pos (hx x)]
      rfl
  · have hs : z.1 ∈ Y₀ := (Finset.mem_union.mp z.2).resolve_right hz
    have hs' : ∀ x, z.1 ∈ (Gf x).recordedSites := fun x => by rw [hT.sites_eq x]; exact hs
    have e : ∀ x, ((Gf x).settingOf (γ x)).labelling ⟨z.1, (support_settingOf_eq hT γ H hH x).symm ▸ z.2⟩ =
        (Gf x).recordedLabel ⟨z.1, hs' x⟩ := by
      intro x
      show (if h' : z.1 ∈ (γ x).sites then (γ x).labelAt h' else _) = _
      rw [dif_neg (fun h' => hz (by rwa [sites_eq_supportSites γ H hH x] at h'))]
    simp only [e]
    exact hT.measurable_label z.1 hs hs'
omit hγ hH in
theorem bases_settingOf_apply (c : (stepBlockFrame R.params.side n).Cell) (x : X) :
    ((Gf x).settingOf (γ x)).bases c =
    Sum.elim (fun _ => b₀ c)
      (fun o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o)
      ((γ x).baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c)) := by
  show (match (γ x).baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
    | Sum.inr o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o
    | Sum.inl _ => (Gf x).groundBases c) = _
  rw [hT.bases_eq x]
  cases (γ x).baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) <;> rfl
theorem measurableSet_bases_apply_eq (b : BaseChoice R.params.side n) (c : (stepBlockFrame R.params.side n).Cell) :
    MeasurableSet {x | ((Gf x).settingOf (γ x)).bases c = b c} := by
  have h1 := measurable_baseAt_family γ H hγ hH (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c)
    (measurableSet_withNone {m | Sum.elim (fun _ => b₀ c)
      (fun o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o) m =
        b c})
  have h2 : {x | ((Gf x).settingOf (γ x)).bases c = b c} =
      (fun x => (γ x).baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c)) ⁻¹'
      {m | Sum.elim (fun _ => b₀ c)
        (fun o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o) m =
          b c} := by
    ext x
    rw [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_setOf_eq, bases_settingOf_apply hT γ]
  rw [h2]
  exact h1
theorem measurableSet_bases_eq (b : BaseChoice R.params.side n) :
    MeasurableSet {x | ((Gf x).settingOf (γ x)).bases = b} := by
  have e : {x | ((Gf x).settingOf (γ x)).bases = b} =
      ⋂ c : (stepBlockFrame R.params.side n).Cell, {x | ((Gf x).settingOf (γ x)).bases c = b c} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact funext_iff
  rw [e]
  have hcount : Countable (stepBlockFrame R.params.side n).Cell := (finite_cell R.params.side n).to_countable
  exact MeasurableSet.iInter fun c => measurableSet_bases_apply_eq hT γ H hγ hH b c
omit hγ in
theorem settingOf_eq_mkSetting (b : BaseChoice R.params.side n) (x : X) (hb : ((Gf x).settingOf (γ x)).bases = b) :
    (Gf x).settingOf (γ x) = mkSetting (Gf x).coarse (Gf x).region (Y₀ ∪ supportSites H) (freeAfter F₀ H)
      (badAfter B₀ C₀ H) b ((Gf x).settingOf (γ x)).fine
      (fun z => ((Gf x).settingOf (γ x)).labelling ⟨z.1, (support_settingOf_eq hT γ H hH x).symm ▸ z.2⟩) :=
  eq_mkSetting ((Gf x).settingOf (γ x)) (support_settingOf_eq hT γ H hH x) (free_settingOf_eq hT γ H hH x)
    (bad_settingOf_eq hT γ H hH x) hb
omit hγ in
theorem frameField_eq (x : X) : (Gf x).frameField (γ x) =
    frameField R (freeAfter F₀ H) (Gf x).coarse ((Gf x).settingWithFamily (γ x)).fine := by
  have hf : ((Gf x).settingWithFamily (γ x)).free = freeAfter F₀ H := free_settingOf_eq hT γ H hH x
  show ((Gf x).settingWithFamily (γ x)).field 0 = _
  rw [ChartSetting.field_zero]
  exact congrArg (fun F => frameField R F (Gf x).coarse ((Gf x).settingWithFamily (γ x)).fine) hf
omit hγ hH in
theorem measurable_frameCoord_free (H : Set (GasSupport R n)) : ∀ e ∈ freeAfter F₀ H,
    MeasurableQuaternion fun x =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (Gf x).coarse e : imaginaryQuaternions) : ℍ[ℝ]) := by
  intro e he
  classical
  exact hT.measurable_frame e (hT.free_sub (Finset.mem_filter.mp he).1)
theorem measurable_frameField_gas : Measurable fun x => (Gf x).frameField (γ x) := by
  rw [funext (frameField_eq hT γ H hH)]
  exact measurable_frameField_family _ hT.measurable_coarse (measurable_settingWithFamily_fine hT γ H hγ hH)
    (measurable_frameCoord_free hT H)
variable (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
    R.clusterFactor R.siteDensity)
  (hside : IsBlockTorusSide R.params (n * R.params.side))
  (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0) (hS : SharesSumToAction)
  (hM : MeasurableContourMeanStatement) (hp : IsCutoff R.ballRadius R.barrierFn) (ha : 0 ≤ R.params.coupling)
  (hL : 0 < R.params.side) (hm : 2 ≤ n * R.params.side)
include hr hside hflat hS hM hp ha hL hm in
theorem measurable_mass_gas (b : BaseChoice R.params.side n) (hb : ∀ x, ((Gf x).settingOf (γ x)).bases = b)
    (hs : ∀ x, ((Gf x).settingOf (γ x)).IsAdmissible) :
    Measurable fun x => settingMass ((Gf x).settingOf (γ x)) := by
  have hs' : ∀ x, (mkSetting (Gf x).coarse (Gf x).region (Y₀ ∪ supportSites H) (freeAfter F₀ H)
      (badAfter B₀ C₀ H) b ((Gf x).settingOf (γ x)).fine
      (fun z => ((Gf x).settingOf (γ x)).labelling
        ⟨z.1, (support_settingOf_eq hT γ H hH x).symm ▸ z.2⟩)).IsAdmissible := fun x =>
    (settingOf_eq_mkSetting hT γ H hH b x (hb x)) ▸ hs x
  have hm' := measurable_settingMass_family (Y₀ ∪ supportSites H) (freeAfter F₀ H) (badAfter B₀ C₀ H) b hr hside
    hflat hS hM hp ha hL hm (fun x => (Gf x).coarse) (fun x => (Gf x).region)
    (fun x => ((Gf x).settingOf (γ x)).fine)
    (fun x z => ((Gf x).settingOf (γ x)).labelling ⟨z.1, (support_settingOf_eq hT γ H hH x).symm ▸ z.2⟩)
    hT.measurable_coarse (measurable_frameField_gas hT γ H hγ hH) (measurable_labelling_family hT γ H hγ hH)
    (measurable_frameCoord_free hT H) hs'
  have e : (fun x => settingMass ((Gf x).settingOf (γ x))) = fun x =>
      settingMass (mkSetting (Gf x).coarse (Gf x).region (Y₀ ∪ supportSites H) (freeAfter F₀ H) (badAfter B₀ C₀ H) b
        ((Gf x).settingOf (γ x)).fine
        (fun z => ((Gf x).settingOf (γ x)).labelling ⟨z.1, (support_settingOf_eq hT γ H hH x).symm ▸ z.2⟩)) :=
    funext fun x => congrArg settingMass (settingOf_eq_mkSetting hT γ H hH b x (hb x))
  rw [e]
  exact hm'
end Family
theorem countable_baseChoice (L n : ℕ) [NeZero L] [NeZero n] : Countable (BaseChoice L n) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.countable_baseChoice <;> assumption
theorem congr_dependent {T Ω α : Type} (f : ∀ Y : Finset T, (Y → Ω) → α) {Y Y' : Finset T} (h : Y = Y')
    (ω : Y → Ω) (ω' : Y' → Ω) (hω : ∀ z (hz : z ∈ Y) (hz' : z ∈ Y'), ω ⟨z, hz⟩ = ω' ⟨z, hz'⟩) :
    f Y ω = f Y' ω' := by apply _root_.YangMills.Construction.StepGas.ActivityMeasurable.dependent_congr <;> assumption
theorem measurable_norm_sub_quaternion {α : Type} [MeasurableSpace α] {f g : α → ℍ[ℝ]}
    (hf : MeasurableQuaternion f) (hg : MeasurableQuaternion g) : Measurable fun a => ‖f a - g a‖ := by apply _root_.YangMills.Construction.CoarseMeasurability.measurable_norm_sub_of_quaternion <;> assumption
theorem measurable_cutoffFactor_comp {ρ : ℝ} {p : ℝ → ℝ} (hp : ContinuousOn p (Set.Ico 0 ρ)) {α : Type}
    [MeasurableSpace α] {u : α → ℝ} (hu : Measurable u) (h0 : ∀ a, 0 ≤ u a) :
    Measurable fun a => cutoffFactor ρ p (u a) := by
  classical
  have hr : Measurable ((Set.Ico 0 ρ).restrict p) :=
    (continuousOn_iff_continuous_restrict.mp hp).measurable
  let v : {a | u a < ρ} → Set.Ico 0 ρ := fun a => ⟨u a, h0 a, a.2⟩
  have hv : Measurable v := (hu.comp measurable_subtype_coe).subtype_mk
  have hlt : MeasurableSet {a | u a < ρ} := measurableSet_lt hu measurable_const
  refine measurable_of_restrict_of_restrict_compl hlt ?_ ?_
  · have e : (fun x : {a | u a < ρ} => cutoffFactor ρ p (u x)) =
        fun x => Real.exp (- (Set.Ico 0 ρ).restrict p (v x)) := by
      funext x
      have hx : u x < ρ := x.2
      show (if u x < ρ then Real.exp (- p (u x)) else 0) = _
      rw [if_pos hx]
      rfl
    show Measurable fun x : {a | u a < ρ} => cutoffFactor ρ p (u x)
    rw [e]
    exact Real.measurable_exp.comp (hr.comp hv).neg
  · have e : (fun x : ({a | u a < ρ} : Set α)ᶜ.Elem => cutoffFactor ρ p (u x)) = fun _ => 0 := by
      funext x
      have hx : ¬ u x < ρ := x.2
      show (if u x < ρ then Real.exp (- p (u x)) else 0) = 0
      rw [if_neg hx]
    show Measurable fun x : ({a | u a < ρ} : Set α)ᶜ.Elem => cutoffFactor ρ p (u x)
    rw [e]
    exact measurable_const
theorem measurableQuaternion_comp_pair {β₁ β₂ α : Type} [MeasurableSpace β₁] [MeasurableSpace β₂]
    [MeasurableSpace α]
    (C : β₁ → β₂ → ℍ[ℝ]) (hC : MeasurableQuaternion fun p : β₁ × β₂ => C p.1 p.2) {v : α → β₁} {w : α → β₂}
    (hv : Measurable v) (hw : Measurable w) : MeasurableQuaternion fun a => C (v a) (w a) := by
  have hp : Measurable fun a => (v a, w a) := hv.prodMk hw
  exact ⟨hC.1.comp hp, hC.2.1.comp hp, hC.2.2.1.comp hp, hC.2.2.2.comp hp⟩
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
theorem measurableSet_isHullState {m : ℕ} [NeZero m] {ℓ : TorusLumps.StepParameters} (hfit : ℓ.Admissible)
    (hLn : ℓ.side ∣ m) (r : ℕ)
    (Yt : Finset (TorusSite m)) : MeasurableSet {W : TorusField m | IsHullState ℓ r W Yt} := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurableSet_isHullState <;> assumption
section Class
variable {Gf : X → GasGround R n} {C₀ : Finset (TorusSite n)} {Y₀ : Finset (TorusSite (n * R.params.side))}
  {B₀ F₀ : Finset (TorusBond (n * R.params.side))} {b₀ : BaseChoice R.params.side n}
  (hT : TameFamily Gf C₀ Y₀ B₀ F₀ b₀)
  {θ : GasSupport R n} {s : X → SupportState θ} (hs : Measurable s)
include hs in
theorem measurable_single_apply (θ' : GasSupport R n) : Measurable fun x => GasFamily.single θ (s x) θ' := by
  classical
  by_cases h : θ' = θ
  · subst h
    have e : ∀ x, GasFamily.single θ' (s x) θ' = Sum.inr (s x) := fun x => Function.update_self _ _ _
    simp only [e]
    exact measurable_inr.comp hs
  · have e : ∀ x, GasFamily.single θ (s x) θ' = Sum.inl () := fun x => Function.update_of_ne h _ _
    simp only [e]
    exact measurable_const
omit [MeasurableSpace X] in
theorem single_occupies_iff (x : X) (θ' : GasSupport R n) :
    (GasFamily.single θ (s x)).Occupies θ' ↔ θ' ∈ ({θ} : Set (GasSupport R n)) := by
  classical
  by_cases h : θ' = θ
  · subst h
    have e : GasFamily.single θ' (s x) θ' = Sum.inr (s x) := Function.update_self _ _ _
    simp [GasFamily.Occupies, e]
  · have e : GasFamily.single θ (s x) θ' = Sum.inl () := Function.update_of_ne h _ _
    simp [GasFamily.Occupies, e, h]
theorem measurable_bondMark_family {Z : Type} [MeasurableSpace Z] (hCC : ChartCoordMeasurable)
    (hcut : IsCutoff R.ballRadius R.barrierFn)
    {v : Z → TorusField n} {w : Z → TorusField (n * R.params.side)} (hv : Measurable v) (hw : Measurable w)
    (b : TorusBond (n * R.params.side))
    (hf : MeasurableQuaternion fun z =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v z) b : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable fun z => bondMark R (v z) (w z) b := by
  have hchart : MeasurableQuaternion fun z => ((chartCoord R.params (v z) (w z) b : imaginaryQuaternions) : ℍ[ℝ]) :=
    measurableQuaternion_comp_pair (fun V W => ((chartCoord R.params V W b : imaginaryQuaternions) : ℍ[ℝ]))
      (hCC R.params n b) hv hw
  unfold bondMark
  exact measurable_cutoffFactor_comp hcut.smooth.continuousOn (measurable_norm_sub_quaternion hchart hf)
    fun _ => norm_nonneg _
include hT hs
theorem measurable_frameField_single : Measurable fun x => (Gf x).frameField (GasFamily.single θ (s x)) :=
  measurable_frameField_gas hT (fun x => GasFamily.single θ (s x)) {θ} (measurable_single_apply hs)
    single_occupies_iff
theorem measurable_clusterFactor_single
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (Xc : Finset (TorusSite (n * R.params.side))) :
    Measurable fun x => R.clusterFactor (n * R.params.side) ((Gf x).frameField (GasFamily.single θ (s x)))
      ((Gf x).settingOf (GasFamily.single θ (s x))).support
      ((Gf x).settingOf (GasFamily.single θ (s x))).labelling Xc := by
  obtain ⟨-, hΦ, -⟩ := hr.borel (n * R.params.side) hside (Y₀ ∪ supportSites {θ})
  have hl := measurable_labelling_family hT (fun x => GasFamily.single θ (s x)) {θ} (measurable_single_apply hs)
    single_occupies_iff
  have h1 := (hΦ Xc).comp ((measurable_frameField_single hT hs).prodMk hl)
  have e : (fun x => R.clusterFactor (n * R.params.side) ((Gf x).frameField (GasFamily.single θ (s x)))
      ((Gf x).settingOf (GasFamily.single θ (s x))).support
      ((Gf x).settingOf (GasFamily.single θ (s x))).labelling Xc) =
      fun x => R.clusterFactor (n * R.params.side) ((Gf x).frameField (GasFamily.single θ (s x)))
        (Y₀ ∪ supportSites {θ})
        (fun z => ((Gf x).settingOf (GasFamily.single θ (s x))).labelling
          ⟨z.1, (support_settingOf_eq hT (fun x => GasFamily.single θ (s x)) {θ} single_occupies_iff x).symm ▸
            z.2⟩) Xc := by
    funext x
    exact congr_dependent
      (fun Y ω => R.clusterFactor (n * R.params.side) ((Gf x).frameField (GasFamily.single θ (s x))) Y ω Xc)
      (support_settingOf_eq hT (fun x => GasFamily.single θ (s x)) {θ} single_occupies_iff x) _ _
      fun z hz hz' => rfl
  rw [e]
  exact h1
theorem measurable_baseUniformWeight_single (hK : BondKernelBorel) (y : TorusSite n) :
    Measurable fun x => baseUniformWeight ((Gf x).frameField (GasFamily.single θ (s x)))
      ((Gf x).settingOf (GasFamily.single θ (s x))).bases y := by
  have hc := countable_baseChoice R.params.side n
  refine measurable_of_countable_cover (fun b => {x | ((Gf x).settingOf (GasFamily.single θ (s x))).bases = b})
    (fun b => measurableSet_bases_eq hT (fun x => GasFamily.single θ (s x)) {θ} (measurable_single_apply hs)
      single_occupies_iff b)
    (fun a => ⟨_, rfl⟩) fun b => ?_
  have e : (fun x : {x | ((Gf x).settingOf (GasFamily.single θ (s x))).bases = b} =>
      baseUniformWeight ((Gf x).frameField (GasFamily.single θ (s x)))
        ((Gf x).settingOf (GasFamily.single θ (s x))).bases y) =
      fun x => baseUniformWeight ((Gf x.1).frameField (GasFamily.single θ (s x.1))) b y := by
    funext x
    rw [show ((Gf x.1).settingOf (GasFamily.single θ (s x.1))).bases = b from x.2]
  rw [e]
  have h1 := measurable_baseUniformWeight (R := R) hK b y
  exact h1.comp ((measurable_frameField_single hT hs).comp measurable_subtype_coe)
theorem measurable_bondMark_single (hCC : ChartCoordMeasurable) (hcut : IsCutoff R.ballRadius R.barrierFn)
    (b : TorusBond (n * R.params.side))
    (hb : b ∈ markedBonds R C₀) :
    Measurable fun x => bondMark R (Gf x).coarse ((Gf x).frameField (GasFamily.single θ (s x))) b :=
  measurable_bondMark_family hCC hcut hT.measurable_coarse (measurable_frameField_single hT hs) b
    (hT.measurable_frame b hb)
theorem measurable_activity_single
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hCC : ChartCoordMeasurable) (hK : BondKernelBorel) (hcut : IsCutoff R.ballRadius R.barrierFn) :
    Measurable fun x => (Gf x).activity θ (s x) := by
  classical
  have e : ∀ x, (Gf x).supportMarks θ ((Gf x).frameField (GasFamily.single θ (s x))) =
      ∏ b ∈ θ.coreBonds ∩ markedBonds R C₀, if b ∈ θ.1
        then 1 - bondMark R (Gf x).coarse ((Gf x).frameField (GasFamily.single θ (s x))) b
        else bondMark R (Gf x).coarse ((Gf x).frameField (GasFamily.single θ (s x))) b := by
    intro x
    unfold GasGround.supportMarks
    rw [hT.cut_eq x]
  have h1 : Measurable fun x => (Gf x).supportMarks θ ((Gf x).frameField (GasFamily.single θ (s x))) := by
    simp only [e]
    refine Finset.measurable_fun_prod _ fun b hb => ?_
    have hbm := (Finset.mem_inter.mp hb).2
    by_cases h : b ∈ θ.1
    · simp only [if_pos h]
      exact measurable_const.sub (measurable_bondMark_single hT hs hCC hcut b hbm)
    · simp only [if_neg h]
      exact measurable_bondMark_single hT hs hCC hcut b hbm
  unfold GasGround.activity
  exact (h1.mul (Finset.measurable_fun_prod _ fun Xc _ => measurable_clusterFactor_single hT hs hr hside Xc)).mul
    (Finset.measurable_fun_prod _ fun y _ => measurable_baseUniformWeight_single hT hs hK y)
theorem measurableSet_isAllowed_single (hfit : R.params.Admissible)
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) (hCC : ChartCoordMeasurable)
    (hK : BondKernelBorel) (hcut : IsCutoff R.ballRadius R.barrierFn) :
    MeasurableSet {x | (Gf x).IsAllowed θ (s x)} := by
  classical
  have hA : MeasurableSet {x | IsHullState R.params R.range ((Gf x).frameField (GasFamily.single θ (s x)))
      ((Gf x).settingOf (GasFamily.single θ (s x))).support} := by
    have e : {x | IsHullState R.params R.range ((Gf x).frameField (GasFamily.single θ (s x)))
        ((Gf x).settingOf (GasFamily.single θ (s x))).support} =
        (fun x => (Gf x).frameField (GasFamily.single θ (s x))) ⁻¹'
          {W | IsHullState R.params R.range W (Y₀ ∪ supportSites {θ})} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      rw [support_settingOf_eq hT (fun x => GasFamily.single θ (s x)) {θ} single_occupies_iff x]
    rw [e]
    exact (measurable_frameField_single hT hs) (measurableSet_isHullState hfit (Dvd.intro_left n rfl) _ _)
  have e : {x | (Gf x).IsAllowed θ (s x)} =
      {x | IsHullState R.params R.range ((Gf x).frameField (GasFamily.single θ (s x)))
        ((Gf x).settingOf (GasFamily.single θ (s x))).support} ∩
      ((⋂ Xc ∈ chainComponents R.range θ.2, {x | R.clusterFactor (n * R.params.side)
        ((Gf x).frameField (GasFamily.single θ (s x)))
        ((Gf x).settingOf (GasFamily.single θ (s x))).support
        ((Gf x).settingOf (GasFamily.single θ (s x))).labelling Xc ≠ 0}) ∩
      ((⋂ b ∈ θ.coreBonds ∩ markedBonds R C₀, {x | b ∉ θ.1 →
        bondMark R (Gf x).coarse ((Gf x).frameField (GasFamily.single θ (s x))) b ≠ 0}) ∩
      ⋂ y ∈ θ.core, {x | baseUniformWeight ((Gf x).frameField (GasFamily.single θ (s x)))
        ((Gf x).settingOf (GasFamily.single θ (s x))).bases y ≠ 0})) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    unfold GasGround.IsAllowed
    rw [hT.cut_eq x]
  rw [e]
  refine hA.inter (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))
  · refine Finset.measurableSet_biInter _ fun Xc _ => ?_
    exact (measurableSet_singleton (0 : ℝ)).compl.preimage (measurable_clusterFactor_single hT hs hr hside Xc)
  · refine Finset.measurableSet_biInter _ fun b hb => ?_
    by_cases h : b ∈ θ.1
    · have e2 : {x | b ∉ θ.1 → bondMark R (Gf x).coarse ((Gf x).frameField (GasFamily.single θ (s x))) b ≠ 0} =
          Set.univ := by
        ext x
        simp [h]
      rw [e2]
      exact MeasurableSet.univ
    · have e2 : {x | b ∉ θ.1 → bondMark R (Gf x).coarse ((Gf x).frameField (GasFamily.single θ (s x))) b ≠ 0} =
          (fun x => bondMark R (Gf x).coarse ((Gf x).frameField (GasFamily.single θ (s x))) b) ⁻¹' {0}ᶜ := by
        ext x
        simp [h]
      rw [e2]
      exact (measurableSet_singleton (0 : ℝ)).compl.preimage
        (measurable_bondMark_single hT hs hCC hcut b (Finset.mem_inter.mp hb).2)
  · refine Finset.measurableSet_biInter _ fun y _ => ?_
    exact (measurableSet_singleton (0 : ℝ)).compl.preimage (measurable_baseUniformWeight_single hT hs hK y)
end Class
end Gas
section Fixed
variable [NeZero n]
abbrev SupportIndex (S0 : GasSupport R n → Prop) : Type := {θ : GasSupport R n // S0 θ}
open Classical in
instance fintypeSupportIndex (S0 : GasSupport R n → Prop) : Fintype (SupportIndex S0) := Fintype.ofFinite _
abbrev SupportValues (S0 : GasSupport R n → Prop) : Type := ∀ i : SupportIndex S0, WithNone (SupportState i.1)
variable {S0 : GasSupport R n → Prop}
open Classical in
def familyOfValues (τ : SupportValues S0) : GasFamily R n := fun θ => if h : S0 θ then τ ⟨θ, h⟩ else Sum.inl ()
def ValuesCompatible (τ : SupportValues S0) : Prop :=
  ∀ i j : SupportIndex S0, i ≠ j → τ i = Sum.inl () ∨ τ j = Sum.inl () ∨ i.1.FarApart j.1
def ValueAllowed (G : GasGround R n) (θ : GasSupport R n) (m : WithNone (SupportState θ)) : Prop :=
  ∀ s, m = Sum.inr s → G.IsAllowed θ s
def AllValuesAllowed (G : GasGround R n) (τ : SupportValues S0) : Prop :=
  ∀ i : SupportIndex S0, ValueAllowed G i.1 (τ i)
open Classical in
def valuesWeight (G : GasGround R n) (τ : SupportValues S0) : ℝ≥0∞ :=
  if AllValuesAllowed G τ ∧ ValuesCompatible τ then
    ENNReal.ofReal (settingMass (G.settingOf (familyOfValues τ))).toReal else 0
def supportDensity (G : GasGround R n) (θ : GasSupport R n) (m : WithNone (SupportState θ)) : ℝ :=
  withNoneDensity {s | G.IsAllowed θ s} (G.activity θ) m
variable (S0) in
open Classical in
def valuesReference (A : Finset (TorusSite n)) (i : SupportIndex S0) : Measure (WithNone (SupportState i.1)) :=
  if i.1.Touches A then Measure.map Sum.inl (Measure.dirac ()) else withNoneMeasure (supportStateMeasure i.1)
instance (A : Finset (TorusSite n)) (i : SupportIndex S0) : SigmaFinite (valuesReference S0 A i) := by
  classical
  unfold valuesReference
  split_ifs
  · infer_instance
  · exact sigmaFinite_withNoneMeasure _
theorem forgetSubtype_eq_inl_iff {S : Type} {P : S → Prop} {m : WithNone {s // P s}} :
    forgetSubtype m = Sum.inl () ↔ m = Sum.inl () := by
  rcases m with u | s <;> simp [forgetSubtype]
theorem partitionFunction_eq_lintegral (G : GasGround R n) (S0 : GasSupport R n → Prop)
    (hS : ∀ θ, G.IsGasSupport θ ↔ S0 θ)
    (A : Finset (TorusSite n)) (hF : Measurable (valuesWeight G : SupportValues S0 → ℝ≥0∞))
    (hA : ∀ i : SupportIndex S0, MeasurableSet {s | G.IsAllowed i.1 s})
    (hg : ∀ i : SupportIndex S0, Measurable (G.activity i.1)) :
    G.partitionFunction A = ∫⁻ τ : SupportValues S0,
      (∏ i : SupportIndex S0, ENNReal.ofReal (supportDensity G i.1 (τ i))) * valuesWeight G τ
      ∂Measure.pi (valuesReference S0 A) := by
  classical
  obtain rfl : S0 = G.IsGasSupport := funext fun θ => propext (hS θ).symm
  have hd : ∀ i : SupportIndex G.IsGasSupport, Measurable (supportDensity G i.1) := fun i =>
    measurable_const.sumElim (Measurable.ite (hA i) (hg i) measurable_const)
  have key : ∀ σ : G.Config, G.pairConstraint.weightDensity G.weight σ =
      valuesWeight G (fun i : SupportIndex G.IsGasSupport => forgetSubtype (σ i)) := by
    intro σ
    have hg' : familyOfValues (fun i : SupportIndex G.IsGasSupport => forgetSubtype (σ i)) = G.familyOf σ := by
      funext θ
      unfold familyOfValues GasGround.familyOf
      by_cases h : G.IsGasSupport θ
      · simp only [dif_pos h]
        cases σ ⟨θ, h⟩ <;> rfl
      · simp only [dif_neg h]
    have hok : AllValuesAllowed G (fun i : SupportIndex G.IsGasSupport => forgetSubtype (σ i)) := by
      intro i s hs
      have hs' : forgetSubtype (σ i) = Sum.inr s := hs
      rcases hσ : σ i with u | v
      · rw [hσ] at hs'
        simp [forgetSubtype] at hs'
      · rw [hσ] at hs'
        have e : v.1 = s := Sum.inr.inj hs'
        exact e ▸ v.2
    have hadm : ValuesCompatible (fun i : SupportIndex G.IsGasSupport => forgetSubtype (σ i)) ↔
        G.pairConstraint.IsAdmissible σ := by
      constructor
      · intro h i j hij
        rcases h i j hij with h | h | h
        · exact Or.inl (forgetSubtype_eq_inl_iff.mp h)
        · exact Or.inr (Or.inl (forgetSubtype_eq_inl_iff.mp h))
        · exact Or.inr (Or.inr h)
      · intro h i j hij
        rcases h i j hij with h | h | h
        · exact Or.inl (forgetSubtype_eq_inl_iff.mpr h)
        · exact Or.inr (Or.inl (forgetSubtype_eq_inl_iff.mpr h))
        · exact Or.inr (Or.inr h)
    unfold PairConstraint.weightDensity valuesWeight GasGround.weight
    by_cases ha : G.pairConstraint.IsAdmissible σ
    · rw [if_pos ha, if_pos ha, if_pos ⟨hok, hadm.mpr ha⟩, hg']
    · rw [if_neg ha, if_neg (fun h => ha (hadm.mp h.2))]
  unfold GasGround.partitionFunction
  rw [lintegral_congr key]
  refine lintegral_pi_transport (A := fun i : SupportIndex G.IsGasSupport => G.SpinValue i)
    (B := fun i => WithNone (SupportState i.1)) (G.referenceMeasure A) (valuesReference _ A)
    (fun i => forgetSubtype)
    (fun i => measurable_forgetSubtype) (fun i => supportDensity G i.1) hd ?_ _ hF
  intro i
  by_cases ht : i.1.Touches A
  · have e1 : G.referenceMeasure A i = Measure.map Sum.inl (Measure.dirac ()) := if_pos ht
    have e2 : valuesReference _ A i = Measure.map Sum.inl (Measure.dirac ()) := if_pos ht
    rw [e1, e2, Measure.map_map measurable_forgetSubtype measurable_inl,
      withDensity_map_inl_dirac (fun x => ENNReal.ofReal (supportDensity G i.1 x))
        (ENNReal.measurable_ofReal.comp (hd i)) (by simp [supportDensity, withNoneDensity])]
    rfl
  · have e1 : G.referenceMeasure A i = withNoneMeasure (G.spinStateMeasure i) := if_neg ht
    have e2 : valuesReference _ A i = withNoneMeasure (supportStateMeasure i.1) := if_neg ht
    rw [e1, e2]
    exact map_forgetSubtype_withNoneMeasure (supportStateMeasure i.1) (G.IsAllowed i.1) (hA i) (G.activity i.1)
      (hg i) (hd i)
theorem measurable_familyOfValues {Z : Type} [MeasurableSpace Z] {τ : Z → SupportValues S0} (h : Measurable τ)
    (θ : GasSupport R n) : Measurable fun z => familyOfValues (τ z) θ := by
  classical
  unfold familyOfValues
  by_cases hθ : S0 θ
  · simp only [dif_pos hθ]
    exact (measurable_pi_apply _).comp h
  · simp only [dif_neg hθ]
    exact measurable_const
theorem measurableSet_value_vacant (i : SupportIndex S0) :
    MeasurableSet {τ : SupportValues S0 | τ i = Sum.inl ()} := by
  have e : {τ : SupportValues S0 | τ i = Sum.inl ()} =
      (fun τ : SupportValues S0 => τ i) ⁻¹' Set.range (Sum.inl : Unit → WithNone (SupportState i.1)) := by
    ext τ
    constructor
    · intro h
      exact ⟨(), Eq.symm h⟩
    · rintro ⟨u, h⟩
      exact Eq.symm h
  rw [e]
  exact measurable_pi_apply i measurableSet_range_inl
theorem measurableSet_valuesCompatible : MeasurableSet {τ : SupportValues S0 | ValuesCompatible τ} := by
  have e : {τ : SupportValues S0 | ValuesCompatible τ} =
      ⋂ (i : SupportIndex S0) (j : SupportIndex S0) (_ : i ≠ j),
      ({τ : SupportValues S0 | τ i = Sum.inl ()} ∪
        ({τ : SupportValues S0 | τ j = Sum.inl ()} ∪ {_τ : SupportValues S0 | i.1.FarApart j.1})) := by
    ext τ
    simp only [Set.mem_iInter]
    exact Iff.rfl
  rw [e]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    (measurableSet_value_vacant i).union ((measurableSet_value_vacant j).union (MeasurableSet.const _))
theorem measurableSet_occupies (θ : GasSupport R n) :
    MeasurableSet {τ : SupportValues S0 | (familyOfValues τ).Occupies θ} := by
  have e : {τ : SupportValues S0 | (familyOfValues τ).Occupies θ} =
      (fun τ : SupportValues S0 => familyOfValues τ θ) ⁻¹'
        Set.range (Sum.inr : SupportState θ → WithNone (SupportState θ)) := by
    ext τ
    constructor
    · intro h
      exact ⟨_, (Sum.inr_getRight _ h)⟩
    · rintro ⟨u, h⟩
      have h' : familyOfValues τ θ = Sum.inr u := h.symm
      show (familyOfValues τ θ).isRight = true
      rw [h']
      rfl
  rw [e]
  exact measurable_familyOfValues measurable_id θ measurableSet_range_inr
section Joint
variable {X : Type} [MeasurableSpace X] {Gf : X → GasGround R n} {C₀ : Finset (TorusSite n)}
  {Y₀ : Finset (TorusSite (n * R.params.side))} {B₀ F₀ : Finset (TorusBond (n * R.params.side))}
  {b₀ : BaseChoice R.params.side n}
  (hT : TameFamily Gf C₀ Y₀ B₀ F₀ b₀)
  (hfit : R.params.Admissible)
  (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
    R.siteDensity)
  (hside : IsBlockTorusSide R.params (n * R.params.side))
  (hCC : ChartCoordMeasurable) (hK : BondKernelBorel) (hcut : IsCutoff R.ballRadius R.barrierFn)
include hT hfit hr hside hCC hK hcut
theorem measurable_supportDensity_pair (θ : GasSupport R n) :
    Measurable fun p : X × WithNone (SupportState θ) => supportDensity (Gf p.1) θ p.2 := by
  classical
  refine measurable_withNone_of_sides
    (f := fun p : X × WithNone (SupportState θ) => supportDensity (Gf p.1) θ p.2) ?_ ?_
  · show Measurable fun _ : X => (1 : ℝ)
    exact measurable_const
  · have hT' := hT.comp (measurable_fst (α := X) (β := SupportState θ))
    have hs : Measurable fun y : X × SupportState θ => y.2 := measurable_snd
    have e : (fun y : X × SupportState θ => supportDensity (Gf y.1) θ (Sum.inr y.2)) = fun y =>
        if (Gf y.1).IsAllowed θ y.2 then (Gf y.1).activity θ y.2 else 0 := by
      funext y
      by_cases h : (Gf y.1).IsAllowed θ y.2
      · simp [supportDensity, withNoneDensity, h]
      · simp [supportDensity, withNoneDensity, h]
    rw [e]
    exact Measurable.ite (measurableSet_isAllowed_single hT' hs hfit hr hside hCC hK hcut)
      (measurable_activity_single hT' hs hr hside hCC hK hcut) measurable_const
theorem measurableSet_valueAllowed_pair (θ : GasSupport R n) :
    MeasurableSet {p : X × WithNone (SupportState θ) | ValueAllowed (Gf p.1) θ p.2} := by
  classical
  refine measurableSet_setOf.mpr (measurable_withNone_of_sides
    (f := fun p : X × WithNone (SupportState θ) => ValueAllowed (Gf p.1) θ p.2) ?_ ?_)
  · have e : (fun x : X => ValueAllowed (Gf x) θ (Sum.inl ())) = fun _ => True := by
      funext x
      simp [ValueAllowed]
    rw [e]
    exact measurable_const
  · have hT' := hT.comp (measurable_fst (α := X) (β := SupportState θ))
    have hs : Measurable fun y : X × SupportState θ => y.2 := measurable_snd
    have e : (fun y : X × SupportState θ => ValueAllowed (Gf y.1) θ (Sum.inr y.2)) =
        fun y => (Gf y.1).IsAllowed θ y.2 := by
      funext y
      simp [ValueAllowed]
    rw [e]
    exact measurableSet_setOf.mp (measurableSet_isAllowed_single hT' hs hfit hr hside hCC hK hcut)
theorem measurableSet_allowed_compatible :
    MeasurableSet {p : X × SupportValues S0 | AllValuesAllowed (Gf p.1) p.2 ∧ ValuesCompatible p.2} := by
  have e : {p : X × SupportValues S0 | AllValuesAllowed (Gf p.1) p.2 ∧ ValuesCompatible p.2} =
      (⋂ i : SupportIndex S0, (fun p : X × SupportValues S0 => (p.1, p.2 i)) ⁻¹'
        {p | ValueAllowed (Gf p.1) i.1 p.2}) ∩
        Prod.snd ⁻¹' {τ : SupportValues S0 | ValuesCompatible τ} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [e]
  refine (MeasurableSet.iInter fun i => ?_).inter (measurable_snd measurableSet_valuesCompatible)
  exact (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
    (measurableSet_valueAllowed_pair hT hfit hr hside hCC hK hcut i.1)
variable (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0) (hS : SharesSumToAction)
  (hM : MeasurableContourMeanStatement) (ha : 0 ≤ R.params.coupling) (hL : 0 < R.params.side)
  (hm : 2 ≤ n * R.params.side)
include hflat hS hM ha hL hm
theorem measurable_valuesWeight_pair
    (hset : ∀ x (τ : SupportValues S0), AllValuesAllowed (Gf x) τ → ValuesCompatible τ →
      ((Gf x).settingOf (familyOfValues τ)).IsAdmissible) :
    Measurable fun p : X × SupportValues S0 => valuesWeight (Gf p.1) p.2 := by
  classical
  have hQ := measurableSet_allowed_compatible (S0 := S0) hT hfit hr hside hCC hK hcut
  let Q : Set (X × SupportValues S0) := {p | AllValuesAllowed (Gf p.1) p.2 ∧ ValuesCompatible p.2}
  have hP : ∀ H : Set (GasSupport R n),
      MeasurableSet {p : X × SupportValues S0 | ∀ θ, (familyOfValues p.2).Occupies θ ↔ θ ∈ H} := by
    intro H
    have e : {p : X × SupportValues S0 | ∀ θ, (familyOfValues p.2).Occupies θ ↔ θ ∈ H} =
        ⋂ θ : GasSupport R n, {p : X × SupportValues S0 | (familyOfValues p.2).Occupies θ ↔ θ ∈ H} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [e]
    refine MeasurableSet.iInter fun θ => ?_
    by_cases hθ : θ ∈ H
    · simp only [hθ, iff_true]
      exact measurable_snd (measurableSet_occupies θ)
    · simp only [hθ, iff_false]
      exact (measurable_snd (measurableSet_occupies θ)).compl
  refine measurable_of_countable_cover (ι := Option (Set (GasSupport R n)))
    (fun o => o.elim Qᶜ fun H => Q ∩ {p | ∀ θ, (familyOfValues p.2).Occupies θ ↔ θ ∈ H}) ?_ ?_ ?_
  · rintro (_ | H)
    · exact hQ.compl
    · exact hQ.inter (hP H)
  · intro p
    by_cases h : p ∈ Q
    · exact ⟨some {θ | (familyOfValues p.2).Occupies θ}, h, fun θ => Iff.rfl⟩
    · exact ⟨none, h⟩
  · rintro (_ | H)
    · have e : (fun a : (Qᶜ : Set (X × SupportValues S0)) => valuesWeight (Gf a.1.1) a.1.2) = fun _ => 0 :=
        funext fun a => if_neg a.2
      exact e ▸ measurable_const
    · let X1 : Set (X × SupportValues S0) := Q ∩ {p | ∀ θ, (familyOfValues p.2).Occupies θ ↔ θ ∈ H}
      have hsub : Measurable fun a : X1 => a.1 := measurable_subtype_coe
      have hT1 : TameFamily (fun a : X1 => Gf a.1.1) C₀ Y₀ B₀ F₀ b₀ := hT.comp (measurable_fst.comp hsub)
      have hγ1 : ∀ θ, Measurable fun a : X1 => familyOfValues a.1.2 θ := fun θ =>
        measurable_familyOfValues (measurable_snd.comp hsub) θ
      have hH1 : ∀ (a : X1) θ, (familyOfValues a.1.2).Occupies θ ↔ θ ∈ H := fun a => a.2.2
      have hc := countable_baseChoice R.params.side n
      have hmass : Measurable fun a : X1 => settingMass ((Gf a.1.1).settingOf (familyOfValues a.1.2)) := by
        refine measurable_of_countable_cover
          (fun b => {a : X1 | ((Gf a.1.1).settingOf (familyOfValues a.1.2)).bases = b})
          (fun b => measurableSet_bases_eq hT1 (fun a : X1 => familyOfValues a.1.2) H hγ1 hH1 b)
          (fun a => ⟨_, rfl⟩) fun b => ?_
        exact measurable_mass_gas (hT1.comp measurable_subtype_coe) (fun a => familyOfValues a.1.1.2) H
          (fun θ => (hγ1 θ).comp measurable_subtype_coe) (fun a => hH1 a.1) hr hside hflat hS hM hcut ha hL hm b
          (fun a => a.2) (fun a => hset _ _ a.1.2.1.1 a.1.2.1.2)
      have e : (fun a : X1 => valuesWeight (Gf a.1.1) a.1.2) = fun a =>
          ENNReal.ofReal (settingMass ((Gf a.1.1).settingOf (familyOfValues a.1.2))).toReal :=
        funext fun a => if_pos a.2.1
      show Measurable fun a : X1 => valuesWeight (Gf a.1.1) a.1.2
      rw [e]
      exact ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp hmass)
theorem measurable_partitionFunction_family (hSup : ∀ x θ, (Gf x).IsGasSupport θ ↔ S0 θ)
    (hset : ∀ x (τ : SupportValues S0), AllValuesAllowed (Gf x) τ → ValuesCompatible τ →
      ((Gf x).settingOf (familyOfValues τ)).IsAdmissible)
    (A : Finset (TorusSite n)) : Measurable fun x => (Gf x).partitionFunction A := by
  have hW := measurable_valuesWeight_pair (S0 := S0) hT hfit hr hside hCC hK hcut hflat hS hM ha hL hm hset
  have hD1 : ∀ i : SupportIndex S0,
      Measurable fun p : X × SupportValues S0 => supportDensity (Gf p.1) i.1 (p.2 i) := by
    intro i
    have h1 := (measurable_supportDensity_pair hT hfit hr hside hCC hK hcut i.1).comp
      ((measurable_fst (α := X) (β := SupportValues S0)).prodMk ((measurable_pi_apply i).comp measurable_snd))
    exact h1
  have hD : Measurable fun p : X × SupportValues S0 =>
      ∏ i : SupportIndex S0, ENNReal.ofReal (supportDensity (Gf p.1) i.1 (p.2 i)) :=
    Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp (hD1 i)
  have hWx : ∀ x, Measurable (valuesWeight (Gf x) : SupportValues S0 → ℝ≥0∞) := by
    intro x
    have h1 := hW.comp (measurable_prodMk_left (x := x))
    exact h1
  have hx : ∀ (x : X) (θ : GasSupport R n), TameFamily (fun _ : SupportState θ => Gf x) C₀ Y₀ B₀ F₀ b₀ :=
    fun x θ => hT.comp (measurable_const (a := x))
  have e : (fun x => (Gf x).partitionFunction A) = fun x => ∫⁻ τ : SupportValues S0,
      (∏ i : SupportIndex S0, ENNReal.ofReal (supportDensity (Gf x) i.1 (τ i))) * valuesWeight (Gf x) τ
        ∂Measure.pi (valuesReference S0 A) :=
    funext fun x => partitionFunction_eq_lintegral (Gf x) S0 (hSup x) A (hWx x)
      (fun i => measurableSet_isAllowed_single (hx x i.1) measurable_id hfit hr hside hCC hK hcut)
      (fun i => measurable_activity_single (hx x i.1) measurable_id hr hside hCC hK hcut)
  rw [e]
  exact (hD.mul hW).lintegral_prod_right'
omit hfit hCC hK in
theorem measurable_coldWeight_family (hset : ∀ x, ((Gf x).settingOf GasFamily.empty).IsAdmissible) :
    Measurable fun x => (Gf x).coldWeight := by
  classical
  have hnone : ∀ (x : X), (Gf x).familyOf (Gf x).allVacant = GasFamily.empty := by
    intro x
    funext θ
    unfold GasGround.familyOf
    by_cases h : (Gf x).IsGasSupport θ
    · rw [dif_pos h]
      rfl
    · rw [dif_neg h]
      rfl
  have hadm : ∀ x, (Gf x).pairConstraint.IsAdmissible (Gf x).allVacant := fun x i j _ => Or.inl rfl
  have e : (fun x => (Gf x).coldWeight) = fun x => (settingMass ((Gf x).settingOf GasFamily.empty)).toReal := by
    funext x
    show (Gf x).weight (Gf x).allVacant = _
    unfold GasGround.weight
    rw [if_pos (hadm x), hnone x]
  rw [e]
  have hγ : ∀ θ : GasSupport R n, Measurable fun _ : X => (GasFamily.empty : GasFamily R n) θ :=
    fun θ => measurable_const
  have hH : ∀ (x : X) θ, (GasFamily.empty : GasFamily R n).Occupies θ ↔ θ ∈ (∅ : Set (GasSupport R n)) := by
    intro x θ
    simp [GasFamily.Occupies, GasFamily.empty]
  have hb : ∀ x, ((Gf x).settingOf GasFamily.empty).bases = b₀ := by
    intro x
    funext c
    rw [bases_settingOf_apply hT (fun _ => GasFamily.empty) c x]
    have : (GasFamily.empty : GasFamily R n).baseAt
        (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) = Sum.inl () := by
      unfold GasFamily.baseAt
      rw [dif_neg]
      rintro ⟨θ', h1, -⟩
      simp [GasFamily.Occupies, GasFamily.empty] at h1
    rw [this]
    rfl
  exact ENNReal.measurable_toReal.comp (measurable_mass_gas hT (fun _ => GasFamily.empty) ∅ hγ hH hr hside hflat hS
    hM hcut ha hL hm b₀ hb hset)
end Joint
end Fixed
section Density
variable [NeZero n] {S0 : GasSupport R n → Prop}
theorem measurableSet_precedingBlocks_eq (y : TorusSite n) (A : Finset (TorusSite n)) :
    MeasurableSet {u : TorusSite n → ℝ | precedingBlocks u y = A} := by
  classical
  have e : {u : TorusSite n → ℝ | precedingBlocks u y = A} =
      ⋂ i, {u : TorusSite n → ℝ | (u i < u y) ↔ i ∈ A} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.ext_iff]
    simp [precedingBlocks]
  rw [e]
  refine MeasurableSet.iInter fun i => ?_
  by_cases h : i ∈ A
  · simp only [h, iff_true]
    exact measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply y)
  · simp only [h, iff_false]
    exact (measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply y)).compl
variable {X : Type} [MeasurableSpace X] {Gf : X → GasGround R n} {C₀ : Finset (TorusSite n)}
  {Y₀ : Finset (TorusSite (n * R.params.side))} {B₀ F₀ : Finset (TorusBond (n * R.params.side))}
  {b₀ : BaseChoice R.params.side n}
  (hT : TameFamily Gf C₀ Y₀ B₀ F₀ b₀)
  (hfit : R.params.Admissible)
  (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
    R.siteDensity)
  (hside : IsBlockTorusSide R.params (n * R.params.side))
  (hCC : ChartCoordMeasurable) (hK : BondKernelBorel) (hcut : IsCutoff R.ballRadius R.barrierFn)
  (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0) (hS : SharesSumToAction)
  (hM : MeasurableContourMeanStatement) (ha : 0 ≤ R.params.coupling) (hL : 0 < R.params.side)
  (hm : 2 ≤ n * R.params.side)
  (hSup : ∀ x θ, (Gf x).IsGasSupport θ ↔ S0 θ)
  (hset : ∀ x (τ : SupportValues S0), AllValuesAllowed (Gf x) τ → ValuesCompatible τ →
    ((Gf x).settingOf (familyOfValues τ)).IsAdmissible)
  (hset0 : ∀ x, ((Gf x).settingOf GasFamily.empty).IsAdmissible)
include hT hfit hr hside hCC hK hcut hflat hS hM ha hL hm hSup hset hset0
theorem measurable_xi_family (A : Finset (TorusSite n)) : Measurable fun x => (Gf x).xi A := by
  have h1 := measurable_partitionFunction_family hT hfit hr hside hCC hK hcut hflat hS hM ha hL hm hSup hset A
  have h2 := measurable_coldWeight_family hT hr hside hcut hflat hS hM ha hL hm hset0
  show Measurable fun x => ((Gf x).partitionFunction A).toReal / (Gf x).coldWeight
  exact (ENNReal.measurable_toReal.comp h1).div h2
theorem measurable_blockDensity_family (y : TorusSite n) : Measurable fun x => (Gf x).blockDensity y := by
  classical
  have hξ := measurable_xi_family hT hfit hr hside hCC hK hcut hflat hS hM ha hL hm hSup hset hset0
  have hj : Measurable fun p : X × (TorusSite n → ℝ) => Real.log ((Gf p.1).xi (precedingBlocks p.2 y)) -
      Real.log ((Gf p.1).xi (insert y (precedingBlocks p.2 y))) := by
    refine measurable_of_countable_cover
      (fun A : Finset (TorusSite n) => {p : X × (TorusSite n → ℝ) | precedingBlocks p.2 y = A})
      (fun A => measurable_snd (measurableSet_precedingBlocks_eq y A)) (fun p => ⟨_, rfl⟩) fun A => ?_
    have e : (fun a : {p : X × (TorusSite n → ℝ) | precedingBlocks p.2 y = A} =>
        Real.log ((Gf a.1.1).xi (precedingBlocks a.1.2 y)) -
          Real.log ((Gf a.1.1).xi (insert y (precedingBlocks a.1.2 y)))) = fun a =>
        Real.log ((Gf a.1.1).xi A) - Real.log ((Gf a.1.1).xi (insert y A)) := by
      funext a
      rw [show precedingBlocks a.1.2 y = A from a.2]
    show Measurable fun a : {p : X × (TorusSite n → ℝ) | precedingBlocks p.2 y = A} =>
      Real.log ((Gf a.1.1).xi (precedingBlocks a.1.2 y)) -
        Real.log ((Gf a.1.1).xi (insert y (precedingBlocks a.1.2 y)))
    rw [e]
    have hs : Measurable fun a : {p : X × (TorusSite n → ℝ) | precedingBlocks p.2 y = A} => a.1.1 :=
      measurable_fst.comp measurable_subtype_coe
    exact (Real.measurable_log.comp ((hξ A).comp hs)).sub (Real.measurable_log.comp ((hξ _).comp hs))
  have hfin : SFinite (randomOrderLaw n) := by
    unfold randomOrderLaw
    infer_instance
  exact (hj.stronglyMeasurable.integral_prod_right' (ν := randomOrderLaw n)).measurable
end Density
section Shapes
variable [NeZero n]
theorem shapeEquivalent_of_labelShape_eq {R : StepSetup} {n : ℕ} [NeZero n] {Z : Finset (TorusSite n)}
    {ω ω' : Z → CoarseLabel R.labels.Ω R.params.side} (e : ∀ y, markShape (ω y) = markShape (ω' y)) :
    ShapeEquivalent (⟨Z, ω⟩ : CoarseState R n) ⟨Z, ω'⟩ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.shapeEquivalent_of <;> assumption
variable {G G' : GasGround R n} (hC : G.cut = G'.cut) (h : ShapeEquivalent G.state G'.state)
include h
theorem recordedSites_eq_of_shape : G.recordedSites = G'.recordedSites := by
  classical
  unfold GasGround.recordedSites
  refine Finset.filter_congr fun z _ => ?_
  rw [labelAt_isRight_eq h z]
theorem recordedBad_eq_of_shape : G.recordedBad = G'.recordedBad := by
  classical
  unfold GasGround.recordedBad
  refine Finset.filter_congr fun b _ => ?_
  rcases markAt_shape h (parentBlock R.params.side b.1) with ⟨h1, h2⟩ | ⟨s, s', h1, h2, _, h3, _⟩
  · simp [h1, h2]
  · simp [h1, h2, h3]
theorem isRecorded_iff_of_shape (b : TorusBond (n * R.params.side)) : G.IsRecorded b ↔ G'.IsRecorded b := by
  unfold GasGround.IsRecorded
  rcases markAt_shape h (parentBlock R.params.side b.1) with ⟨h1, h2⟩ | ⟨s, s', h1, h2, _, _, _, _, h3⟩
  · simp [h1, h2]
  · simp [h1, h2, h3]
theorem groundBases_eq_of_shape : G.groundBases = G'.groundBases := by
  funext c
  unfold GasGround.groundBases
  rcases markAt_shape h (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
    ⟨h1, h2⟩ | ⟨s, s', h1, h2, _, _, _, h3, _⟩
  · simp only [h1, h2]
  · simp only [h1, h2, h3]
include hC
theorem freeBonds_eq_of_shape : G.freeBonds = G'.freeBonds := by
  classical
  unfold GasGround.freeBonds
  rw [hC]
  exact Finset.filter_congr fun b _ => not_congr (isRecorded_iff_of_shape h b)
theorem anchorSites_eq_of_shape : G.anchorSites = G'.anchorSites := by
  unfold GasGround.anchorSites
  rw [hC, recordedBad_eq_of_shape h, recordedSites_eq_of_shape h]
theorem isGasSupport_iff_of_shape (θ : GasSupport R n) : G.IsGasSupport θ ↔ G'.IsGasSupport θ := by
  have h1 := freeBonds_eq_of_shape hC h
  have h2 := anchorSites_eq_of_shape hC h
  constructor
  · intro k
    exact ⟨k.isCluster, h1 ▸ k.bad_subset_free, h2 ▸ k.far_from_anchor⟩
  · intro k
    exact ⟨k.isCluster, h1 ▸ k.bad_subset_free, h2 ▸ k.far_from_anchor⟩
end Shapes
section Frames
variable [NeZero n]
theorem measurableQuaternion_of_continuousOn {β α : Type} [TopologicalSpace β] [MeasurableSpace β]
    [OpensMeasurableSpace β]
    [MeasurableSpace α] {U : Set β} {f : β → ℍ[ℝ]} (hU : ContinuousOn f U) {v : α → β} (hv : Measurable v)
    (hmem : ∀ a, v a ∈ U) : MeasurableQuaternion fun a => f (v a) := by
  have hc := continuousOn_iff_continuous_restrict.mp hU
  have hv' : Measurable fun a => (⟨v a, hmem a⟩ : U) := hv.subtype_mk
  exact ⟨(Quaternion.continuous_re.comp hc).measurable.comp hv',
    (Quaternion.continuous_imI.comp hc).measurable.comp hv',
    (Quaternion.continuous_imJ.comp hc).measurable.comp hv',
    (Quaternion.continuous_imK.comp hc).measurable.comp hv'⟩
theorem mem_hotCoreSites_of_curvature (hfit : R.params.Admissible) (hLn : R.params.side ∣ n) {V : TorusField n}
    {x : TorusSite n} {μ ν : Fin 4}
    (hlt : μ < ν) (hs : R.params.threshold ≤ curvature V x μ ν) {y : TorusSite n}
    (hy : supDist y x ≤ 2 * R.nextRange) : y ∈ hotCoreSites R V := by
  classical
  refine (mem_thickening _ _ _).mpr ⟨x, ?_, hy⟩
  exact Finset.mem_biUnion.mpr ⟨torusLumpOf R.params x,
    (mem_torusHotLumps_iff R.params hfit hLn V _).mpr
      ⟨x, μ, ν, hlt, hs, x, base_mem_plaquetteVertices x μ ν, rfl⟩, mem_torusLumpOf_self x⟩
theorem coldNearSite_of_not_mem (hfit : R.params.Admissible) (hLn : R.params.side ∣ n) {V : TorusField n}
    {y : TorusSite n} (hC : y ∉ hotCoreSites R V)
    (hm : R.frameReach ≤ 2 * R.nextRange) : ColdNearSite R.params.threshold R.frameReach y V := by
  intro a μ ν hlt hcorn
  by_contra hcon
  have hs : R.params.threshold ≤ curvature V (y + siteOfInt a) μ ν := not_lt.mp hcon
  have h0 := hcorn 0 (by simp [plaquetteOffsets])
  have hb : supDist y (y + siteOfInt a) ≤ R.frameReach := by
    refine supDist_add_siteOfInt_le _ _ _ fun i => ?_
    have h1 := h0 i
    rw [add_zero] at h1
    have h2 := abs_le.mp h1
    omega
  exact hC (mem_hotCoreSites_of_curvature hfit hLn hlt hs (hb.trans hm))
theorem supDist_le_half (x z : TorusSite n) : supDist x z ≤ n / 2 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.supDist_le_half_card <;> assumption
theorem isCold_of_not_mem (hfit : R.params.Admissible) (hLn : R.params.side ∣ n) {V : TorusField n}
    {y : TorusSite n} (hC : y ∉ hotCoreSites R V)
    (hn : n / 2 ≤ 2 * R.nextRange) : IsCold R.params.threshold V := by
  intro x μ ν hlt
  by_contra hcon
  exact hC (mem_hotCoreSites_of_curvature hfit hLn hlt (not_lt.mp hcon) ((supDist_le_half y x).trans hn))
theorem measurable_frameCoord_piece (hFC : continuousOn_frameCoord_of_cold) {δ lam σA cg : ℝ} {N : ℕ → ℝ}
    (hfit : R.params.Admissible) (hLn : R.params.side ∣ n)
    (hch : ColdChainConstants R.params.coupling δ R.params.side lam R.anchorRadius σA cg N)
    (hσ : R.params.threshold ≤ σA) (hm : 16 ≤ R.frameReach) (hn : 64 ≤ n) (hm2 : R.frameReach ≤ 2 * R.nextRange)
    (hsm : ¬ 4 * R.frameReach + 5 < n → n / 2 ≤ 2 * R.nextRange) {α : Type} [MeasurableSpace α]
    {v : α → TorusField n}
    (hv : Measurable v) {C₀ : Finset (TorusSite n)} (hC : ∀ a, hotCoreSites R (v a) = C₀)
    {b : TorusBond (n * R.params.side)}
    (hb : b ∈ markedBonds R C₀) :
    MeasurableQuaternion fun a =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v a) b : imaginaryQuaternions) : ℍ[ℝ]) := by
  classical
  have hb' := Finset.mem_filter.mp hb
  obtain ⟨c1, c2⟩ := hFC R.params δ lam R.anchorRadius σA cg N hfit hch hσ R.depth R.frameReach n hm hn b hb'.1
  by_cases hbig : 4 * R.frameReach + 5 < n
  · exact measurableQuaternion_of_continuousOn (β := TorusField n)
      (U := {V | ColdNearSite R.params.threshold R.frameReach (parentBlock R.params.side b.1) V})
      (f := fun V : TorusField n =>
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ]))
      (c1 hbig) hv
      fun a => coldNearSite_of_not_mem hfit hLn (by rw [hC a]; exact hb'.2) hm2
  · exact measurableQuaternion_of_continuousOn (β := TorusField n) (U := {V | IsCold R.params.threshold V})
      (f := fun V : TorusField n =>
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ]))
      (c2 hbig) hv
      fun a => isCold_of_not_mem hfit hLn (by rw [hC a]; exact hb'.2) (hsm hbig)
end Frames
section Values
variable [NeZero n]
theorem isAdmissible_of_values (G : GasGround R n) (S0 : GasSupport R n → Prop)
    (hS : ∀ θ, G.IsGasSupport θ ↔ S0 θ)
    (hC : ∀ σ : G.Config, G.pairConstraint.IsAdmissible σ → (G.settingOf (G.familyOf σ)).IsAdmissible)
    (τ : SupportValues S0)
    (hok : AllValuesAllowed G τ) (hadm : ValuesCompatible τ) : (G.settingOf (familyOfValues τ)).IsAdmissible := by
  classical
  obtain rfl : S0 = G.IsGasSupport := funext fun θ => propext (hS θ).symm
  have hex : ∀ i : SupportIndex G.IsGasSupport, ∃ v : G.SpinValue i, forgetSubtype v = τ i := by
    intro i
    rcases h : τ i with u | s
    · exact ⟨Sum.inl u, rfl⟩
    · exact ⟨Sum.inr ⟨s, hok i s h⟩, rfl⟩
  choose σ hσ using hex
  have hg' : familyOfValues τ = G.familyOf σ := by
    funext θ
    unfold familyOfValues GasGround.familyOf
    by_cases h : G.IsGasSupport θ
    · simp only [dif_pos h]
      rw [← hσ ⟨θ, h⟩]
      cases σ ⟨θ, h⟩ <;> rfl
    · simp only [dif_neg h]
  have ha : G.pairConstraint.IsAdmissible σ := by
    intro i j hij
    rcases hadm i j hij with h | h | h
    · exact Or.inl (forgetSubtype_eq_inl_iff.mp ((hσ i).trans h))
    · exact Or.inr (Or.inl (forgetSubtype_eq_inl_iff.mp ((hσ j).trans h)))
    · exact Or.inr (Or.inr h)
  rw [hg']
  exact hC σ ha
theorem isAdmissible_of_empty (G : GasGround R n)
    (hC : ∀ σ : G.Config, G.pairConstraint.IsAdmissible σ → (G.settingOf (G.familyOf σ)).IsAdmissible) :
    (G.settingOf GasFamily.empty).IsAdmissible := by
  classical
  have hnone : G.familyOf G.allVacant = GasFamily.empty := by
    funext θ
    unfold GasGround.familyOf
    by_cases h : G.IsGasSupport θ
    · rw [dif_pos h]
      rfl
    · rw [dif_neg h]
      rfl
  have h := hC G.allVacant fun i j _ => Or.inl rfl
  rwa [hnone] at h
end Values
section Piece
variable [NeZero n] {Y : Finset (TorusSite n)}
variable (R) in
abbrev hotGroundOf (p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side)) : GasGround R n :=
  hotCaseGround R p.1 ⟨Y, p.2⟩
theorem tameFamily_piece (hFC : continuousOn_frameCoord_of_cold) {δ lam σA cg : ℝ} {N : ℕ → ℝ}
    (hfit : R.params.Admissible) (hLn : R.params.side ∣ n)
    (hch : ColdChainConstants R.params.coupling δ R.params.side lam R.anchorRadius σA cg N)
    (hσ : R.params.threshold ≤ σA) (hm : 16 ≤ R.frameReach) (hn : 64 ≤ n) (hm2 : R.frameReach ≤ 2 * R.nextRange)
    (hsm : ¬ 4 * R.frameReach + 5 < n → n / 2 ≤ 2 * R.nextRange)
    (S : Set (TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side)))
    (p₀ : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side))
    (hhot : ∀ p ∈ S, torusHotLumps R.params p.1 = torusHotLumps R.params p₀.1)
    (hsh : ∀ p ∈ S, ∀ y, markShape (p.2 y) = markShape (p₀.2 y)) :
    TameFamily (fun x : S => hotGroundOf R x.1) (hotCoreSites R p₀.1) (hotGroundOf R p₀).recordedSites
      (hotGroundOf R p₀).recordedBad (hotGroundOf R p₀).freeBonds (hotGroundOf R p₀).groundBases := by
  classical
  have hC : ∀ x : S, hotCoreSites R x.1.1 = hotCoreSites R p₀.1 := by
    intro x
    unfold hotCoreSites torusHotSites
    rw [hhot _ x.2]
  have hC' : ∀ x : S, (hotGroundOf R x.1).cut = (hotGroundOf R p₀).cut := hC
  have same : ∀ x : S, ShapeEquivalent (hotGroundOf R x.1).state (hotGroundOf R p₀).state := fun x =>
    shapeEquivalent_of_labelShape_eq fun y => hsh _ x.2 y
  have hs2 : Measurable fun x : S => x.1.2 := measurable_snd.comp measurable_subtype_coe
  have hs1 : Measurable fun x : S => x.1.1 := measurable_fst.comp measurable_subtype_coe
  refine ⟨hC, fun x => recordedSites_eq_of_shape (same x), fun x => recordedBad_eq_of_shape (same x),
    fun x => freeBonds_eq_of_shape (hC' x) (same x), fun x => groundBases_eq_of_shape (same x),
    Finset.filter_subset _ _, hs1, ?_, ?_, ?_⟩
  · have h := (measurable_storedField (R := R) Y).comp hs2
    exact h
  · intro z _ h'
    have h1 := (measurable_labelAt (R := R) Y z).comp hs2
    exact measurable_getRight_of_isRight h1 fun x => (Finset.mem_filter.mp (h' x)).2
  · intro b hb
    exact measurable_frameCoord_piece hFC hfit hLn hch hσ hm hn hm2 hsm hs1 hC hb
end Piece
theorem le_mul_of_clusterRange_le {x x' : ℝ} (hx : (2 : ℝ) ^ 2000 ≤ x)
    (hr : clusterRange x' ≤ clusterRange x + 1) : x' ≤ 1.01 * x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  rcases le_or_gt x' 0 with h | hpos
  · exact h.trans (by positivity)
  have t0 : 0 ≤ x ^ ((1 : ℝ) / 100) := Real.rpow_nonneg hx0.le _
  have t'0 : 0 ≤ x' ^ ((1 : ℝ) / 100) := Real.rpow_nonneg hpos.le _
  have e1 : (x ^ ((1 : ℝ) / 100)) ^ 100 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have e2 : (x' ^ ((1 : ℝ) / 100)) ^ 100 = x' := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
  have hr' : ⌈x' ^ ((1 : ℝ) / 100)⌉₊ ≤ ⌈x ^ ((1 : ℝ) / 100)⌉₊ + 1 := hr
  generalize x ^ ((1 : ℝ) / 100) = t at t0 e1 hr'
  generalize x' ^ ((1 : ℝ) / 100) = t' at t'0 e2 hr'
  have hbig : (2 : ℝ) ^ 20 ≤ t := by
    have h1 : ((2 : ℝ) ^ 20) ^ 100 ≤ t ^ 100 := by
      rw [e1, ← pow_mul]
      exact hx
    exact (pow_le_pow_iff_left₀ (by positivity) t0 (by norm_num)).mp h1
  have hle : t' ≤ t + 2 := by
    have h1 : t' ≤ ⌈t'⌉₊ := Nat.le_ceil _
    have h2 : (⌈t'⌉₊ : ℝ) ≤ ⌈t⌉₊ + 1 := by exact_mod_cast hr'
    have h3 : (⌈t⌉₊ : ℝ) < t + 1 := Nat.ceil_lt_add_one t0
    linarith
  have h4 : x' ≤ (t + 2) ^ 100 := by
    rw [← e2]
    exact pow_le_pow_left₀ t'0 hle 100
  have h5 : t + 2 ≤ (1 + 1 / 2 ^ 19) * t := by
    have h6 : (2 : ℝ) ^ 20 = 2 ^ 19 * 2 := by norm_num
    have h7 : (2 : ℝ) ≤ 1 / 2 ^ 19 * t := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      linarith
    linarith
  have h6 : (t + 2) ^ 100 ≤ ((1 + 1 / 2 ^ 19) * t) ^ 100 := pow_le_pow_left₀ (by positivity) h5 100
  rw [mul_pow, e1] at h6
  have h7 : ((1 : ℝ) + 1 / 2 ^ 19) ^ 100 ≤ 1.01 := by norm_num
  calc x' ≤ _ := h4
    _ ≤ _ := h6
    _ ≤ 1.01 * x := mul_le_mul_of_nonneg_right h7 hx0.le
end GroundDensityMeasurability
open GroundDensityMeasurability in
theorem groundBlockDensityMeasurable_holds (hC : GasConfigIsAdmissibleSetting)
    (hHG : HullStateIsHotCase) (hF : CoarseFactorExpansionMeasurable)
    (hM : MeasurableContourMeanStatement) (hS : SharesSumToAction)
    (hCC : ChartCoordMeasurable) (hFC : continuousOn_frameCoord_of_cold)
    (hK : BondKernelBorel) : GroundBlockDensityMeasurable := by
  intro T hT
  obtain ⟨y₁, h₁⟩ := hC T hT
  obtain ⟨y₂, h₂⟩ := hHG T hT
  obtain ⟨y₃, h₃⟩ := hF T hT
  refine ⟨max (max y₁ y₂) (max y₃ ((2 : ℝ) ^ 2000)), fun y hy R htab hform n _ hB Y y' => ?_⟩
  classical
  have hy₁ : y₁ ≤ y := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hy
  have hy₂ : y₂ ≤ y := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hy
  have hy₃ : y₃ ≤ y := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hy
  have hy₄ : (2 : ℝ) ^ 2000 ≤ y := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hy
  have hfit := hform.admissible
  have hLn : R.params.side ∣ n := hB.1
  have hLpos : 0 < R.params.side := hfit.L_odd.pos
  haveI hnz : NeZero (n * R.params.side) := ⟨mul_ne_zero (NeZero.ne n) hLpos.ne'⟩
  have hl := htab.params_eq
  have hch : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    have e1 : R.params.coupling = T.coupling := by rw [hl]; rfl
    have e2 : R.params.side = T.side := by rw [hl]; rfl
    rw [e1, e2, htab.anchorRadius_eq]
    exact hT.chain
  have hσ : R.params.threshold ≤ T.σA := by
    have e1 : R.params.threshold = T.threshold := by rw [hl]; rfl
    have h1 := hT.σ_le
    have h2 := hT.σ_pos
    rw [e1]
    linarith
  have hcut := hform.isCutoff
  have hrb : 2 ^ 40 * R.params.side ≤ R.range := hform.range_ge_side
  have hra : R.range ≤ R.nextRange + 1 := hform.range_le
  have hm : 16 ≤ R.frameReach := by
    show 16 ≤ R.range / 2 ^ 11
    have : 2 ^ 40 ≤ R.range := le_trans (Nat.le_mul_of_pos_right _ hLpos) hrb
    omega
  have hn64 : 64 ≤ n := by
    have h1 : R.params.side * R.params.n₀ ≤ n := hB.2
    have h2 : 4096 ≤ R.params.n₀ := hfit.n₀_ge
    have h3 : R.params.n₀ ≤ R.params.side * R.params.n₀ := Nat.le_mul_of_pos_left _ hLpos
    omega
  have hm2 : R.frameReach ≤ 2 * R.nextRange := by
    show R.range / 2 ^ 11 ≤ 2 * R.nextRange
    omega
  have hsm : ¬ 4 * R.frameReach + 5 < n → n / 2 ≤ 2 * R.nextRange := by
    intro h
    have h1 : R.frameReach = R.range / 2 ^ 11 := rfl
    omega
  have hrow := hform.hasExpansions
  have hn0 : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hLpos) hB.2
  have hblock : IsBlockTorusSide R.params (n * R.params.side) := by
    refine ⟨Dvd.intro_left _ rfl, ?_⟩
    rw [mul_comm n]
    exact Nat.mul_le_mul_left _ hn0
  have hnL : R.params.n₀ ≤ n * R.params.side := le_trans hn0 (Nat.le_mul_of_pos_right _ hLpos)
  have hmn : 2 ≤ n * R.params.side := by
    have h2 : 4096 ≤ R.params.n₀ := hfit.n₀_ge
    omega
  have ha : 0 ≤ R.params.coupling := by
    rw [hl]
    exact le_trans zero_le_one hT.a_ge
  have hσp : 0 < R.params.threshold := by
    rw [hl]
    exact hT.σ_pos
  have hcold : IsCold R.params.threshold (trivialField (n * R.params.side)) := by
    intro x μ ν _
    simpa [curvature, holonomy, trivialField] using hσp
  have hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0 :=
    (hrow.1.positive (n * R.params.side) hnL _ hcold).ne'
  have hx' : R.nextCoupling ≤ 1.01 * R.coupling :=
    le_mul_of_clusterRange_le (hy₄.trans htab.le_coupling) hform.nextRange_le
  have hval : ∀ (p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side)) (X : Finset (TorusSite n)),
      coarseFactorExpansion R n p.1 Y p.2 X = coarseFactor p.1 (⟨Y, p.2⟩ : CoarseState R n) X := fun p X =>
    dif_neg (NeZero.ne n)
  let Gd : Set (TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side)) :=
    {p | IsHullState R.params R.nextRange p.1 Y ∧
      ∀ X ∈ chainComponents R.nextRange Y, coarseFactorExpansion R n p.1 Y p.2 X ≠ 0}
  have hGd : MeasurableSet Gd := by
    have e : Gd = (Prod.fst ⁻¹' {V | IsHullState R.params R.nextRange V Y}) ∩
        ⋂ X ∈ chainComponents R.nextRange Y, {p | coarseFactorExpansion R n p.1 Y p.2 X ≠ 0} := by
      ext p
      simp [Gd]
    rw [e]
    refine (measurable_fst (measurableSet_isHullState hfit hLn _ Y)).inter
      (Finset.measurableSet_biInter _ fun X _ => ?_)
    exact ((h₃ y hy₃ R htab hform n hB Y X) (measurableSet_singleton 0)).compl
  let S : Finset (Finset (TorusSite n)) × (Y → CoarseStateShape R.params.side) →
      Set (TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side)) := fun i =>
    Gd ∩ ({p | torusHotLumps R.params p.1 = i.1} ∩ {p | ∀ z, markShape (p.2 z) = i.2 z})
  have hSm : ∀ i, MeasurableSet (S i) := by
    intro i
    refine hGd.inter ((measurable_fst (measurableSet_torusHotLumps_eq hfit hLn i.1)).inter ?_)
    have e : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | ∀ z, markShape (p.2 z) = i.2 z} =
        ⋂ z, {p | markShape (p.2 z) = i.2 z} := by
      ext p
      simp
    rw [e]
    refine MeasurableSet.iInter fun z => ?_
    have hz : Measurable fun p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) => p.2 z :=
      (measurable_pi_apply z).comp measurable_snd
    exact hz (measurableSet_configShape (i.2 z))
  refine measurable_of_countable_cover
    (ι := Option (Finset (Finset (TorusSite n)) × (Y → CoarseStateShape R.params.side)))
    (fun o => o.elim Gdᶜ S) ?_ ?_ ?_
  · rintro (_ | i)
    · exact hGd.compl
    · exact hSm i
  · intro p
    by_cases h : p ∈ Gd
    · exact ⟨some (torusHotLumps R.params p.1, fun z => markShape (p.2 z)), h, rfl, fun z => rfl⟩
    · exact ⟨none, h⟩
  · rintro (_ | i)
    · have e : (fun x : (Gdᶜ : Set (TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side))) =>
          if IsHullState R.params R.nextRange x.1.1 Y ∧
              ∀ X ∈ chainComponents R.nextRange Y, coarseFactorExpansion R n x.1.1 Y x.1.2 X ≠ 0
          then (hotCaseGround R x.1.1 ⟨Y, x.1.2⟩).blockDensity y' else 0) = fun _ => 0 :=
        funext fun x => if_neg x.2
      exact e ▸ measurable_const
    · rcases isEmpty_or_nonempty (S i) with he | ⟨⟨p₀, hp₀⟩⟩
      · exact @measurable_of_empty _ _ _ _ he _
      have hhot : ∀ p ∈ S i, torusHotLumps R.params p.1 = torusHotLumps R.params p₀.1 := fun p hp =>
        hp.2.1.trans hp₀.2.1.symm
      have hsh : ∀ p ∈ S i, ∀ z, markShape (p.2 z) = markShape (p₀.2 z) := fun p hp z =>
        (hp.2.2 z).trans (hp₀.2.2 z).symm
      have hTm := tameFamily_piece hFC hfit hLn hch hσ hm hn64 hm2 hsm (S i) p₀ hhot hsh
      have hcfg : ∀ (x : S i) (σ : (hotGroundOf R x.1).Config), (hotGroundOf R x.1).pairConstraint.IsAdmissible σ →
          ((hotGroundOf R x.1).settingOf ((hotGroundOf R x.1).familyOf σ)).IsAdmissible := by
        intro x σ hσa
        have hg := h₂ y hy₂ R htab hform n hB x.1.1 ⟨Y, x.1.2⟩ x.2.1.1 fun X hX => by
          have h := x.2.1.2 X hX
          rwa [hval] at h
        exact h₁ y hy₁ R htab hx' n (hotGroundOf R x.1) (Or.inr hg) σ hσa
      have hC' : ∀ x : S i, (hotGroundOf R x.1).cut = (hotGroundOf R p₀).cut := fun x => hTm.cut_eq x
      have same : ∀ x : S i, ShapeEquivalent (hotGroundOf R x.1).state (hotGroundOf R p₀).state := fun x =>
        shapeEquivalent_of_labelShape_eq fun z => hsh _ x.2 z
      have hSup : ∀ (x : S i) θ, (hotGroundOf R x.1).IsGasSupport θ ↔ (hotGroundOf R p₀).IsGasSupport θ :=
        fun x θ => isGasSupport_iff_of_shape (hC' x) (same x) θ
      have hd := measurable_blockDensity_family hTm hfit hrow.2 hblock hCC hK hcut hflat hS hM ha hLpos hmn hSup
        (fun x τ h1 h2 => isAdmissible_of_values _ _ (hSup x) (hcfg x) τ h1 h2)
        (fun x => isAdmissible_of_empty _ (hcfg x)) y'
      have e : (fun x : S i =>
          if IsHullState R.params R.nextRange x.1.1 Y ∧
              ∀ X ∈ chainComponents R.nextRange Y, coarseFactorExpansion R n x.1.1 Y x.1.2 X ≠ 0
          then (hotCaseGround R x.1.1 ⟨Y, x.1.2⟩).blockDensity y' else 0) =
          fun x => (hotGroundOf R x.1).blockDensity y' :=
        funext fun x => if_pos x.2.1
      exact e ▸ hd
end ClusterExpansionOfAStep
end YangMills.Construction
end
