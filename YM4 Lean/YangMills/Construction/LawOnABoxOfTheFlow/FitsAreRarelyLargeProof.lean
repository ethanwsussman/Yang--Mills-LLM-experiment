import YangMills.Construction.ResponseInTheExpansion.TheScoreOfABondProof
import YangMills.Construction.ClusterExpansionOfAStep.OmGrowsLikeALogarithm
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsBorel
import YangMills.Construction.FreeEnergiesOfTheFlow.ThePastIsFreeGivenTheStateProof
import YangMills.Construction.LawOnABoxOfTheFlow.FitsAreRarelyLarge
import YangMills.Construction.ResponseInTheExpansion.ProductsOfScoresAtAStepProof
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheMeanOfABond
import YangMills.Construction.ResponseInTheExpansion.TwoSumsOfScoresAtAStepProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.BoxLaws
open BlockAverages WeightedResponses StepSettings StepCosts TorusLumps TorusFields ColdStepAtMirrorFrames
variable {n : ℕ} [NeZero n]
private local instance : MeasurableSpace ℍ[ℝ] := borel _
private local instance : BorelSpace ℍ[ℝ] := ⟨rfl⟩
private theorem measurable_bondMean (hB : BondKernelBorel) (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (b : BaseChoice ℓ.side n)
    (c : TorusBond n) :
    Measurable fun W : TorusField (n * ℓ.side) =>
      bondMean ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W) b c := by apply _root_.YangMills.Construction.WeightedResponses.BondScore.measurable_bondMean <;> assumption
private theorem measurable_bondFit (hB : BondKernelBorel) (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (b : BaseChoice ℓ.side n)
    (c : TorusBond n) :
    Measurable fun p : TorusField (n * ℓ.side) × TorusField n => bondFit ℓ p.1 p.2 b c := by
  have hq := measurable_bondMean hB ℓ b c
  have hel : Measurable fun p : TorusField (n * ℓ.side) × TorusField n => p.2 c.1 c.2 :=
    (measurable_pi_apply c.2).comp ((measurable_pi_apply c.1).comp measurable_snd)
  have hΨ : Continuous fun r : ℍ[ℝ] × UnitQuaternion => (r.1 * ((r.2⁻¹ : UnitQuaternion) : ℍ[ℝ])).re :=
    Quaternion.continuous_re.comp (continuous_fst.mul
      (continuous_subtype_val.comp (continuous_inv.comp continuous_snd)))
  have hre : Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
      (bondMean ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 p.1) b c *
        (((p.2 c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re :=
    hΨ.measurable.comp ((hq.comp measurable_fst).prodMk hel)
  have he : (fun p : TorusField (n * ℓ.side) × TorusField n => bondFit ℓ p.1 p.2 b c) = fun p =>
      ‖bondMean ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 p.1) b c‖ -
        (bondMean ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 p.1) b c *
          (((p.2 c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re := by
    funext p
    rw [bondFit_eq_fitOfElement]
    rfl
  rw [he]
  exact (hq.comp measurable_fst).norm.sub hre
private theorem kernelOfElement_le_exp (hK : BondKernelProperties) {C : ℝ} (hC0 : 0 < C)
    (hO : ∀ s : ℝ, 0 ≤ s → logPartitionGap s ≤ C * Real.log (2 + s)) (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters)
    (ha : 1 ≤ ℓ.coupling) {x : ℝ} (hx : 0 ≤ x)
    (w : (stepBlockFrame ℓ.side n).GaugeField 0) (b : BaseChoice ℓ.side n) (c : TorusBond n) (f : ℝ)
    (g : UnitQuaternion) (hf : f < fitOfElement ℓ w b c g) :
    kernelOfElement ℓ x w b c g ≤ Real.exp (C * Real.log (2 + ℓ.coupling * x) - ℓ.coupling * x * f) := by
  have hax : 0 ≤ ℓ.coupling * x := mul_nonneg (by linarith) hx
  set m := bondMean ℓ w b c with hm
  set s := ℓ.coupling * x * ‖m‖ with hs
  have hs0 : 0 ≤ s := mul_nonneg hax (norm_nonneg _)
  have hz : 1 ≤ partitionFn s := (hK.1 s hs0).1
  have hzp : 0 < partitionFn s := by linarith
  have hr : ‖m‖ ≤ 1 := norm_bondMean_le ℓ w b c
  have hss : s ≤ ℓ.coupling * x := by
    have := mul_le_mul_of_nonneg_left hr hax
    simpa [hs] using this
  have hom : logPartitionGap s ≤ C * Real.log (2 + ℓ.coupling * x) := by
    refine (hO s hs0).trans (mul_le_mul_of_nonneg_left ?_ hC0.le)
    exact Real.log_le_log (by linarith) (by linarith)
  have hk : kernelOfElement ℓ x w b c g =
      Real.exp (logPartitionGap s - ℓ.coupling * x * fitOfElement ℓ w b c g) := by
    unfold kernelOfElement fitOfElement logPartitionGap
    rw [← hm, ← hs]
    have e : s - Real.log (partitionFn s) - ℓ.coupling * x * (‖m‖ - (m * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) =
        ℓ.coupling * x * (m * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re - Real.log (partitionFn s) := by
      rw [hs]
      ring
    rw [e, Real.exp_sub, Real.exp_log hzp]
  rw [hk]
  refine Real.exp_le_exp.2 ?_
  have := mul_le_mul_of_nonneg_left hf.le hax
  linarith
private theorem integral_kernelOfElement (hK : BondKernelProperties) (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (x : ℝ)
    (w : (stepBlockFrame ℓ.side n).GaugeField 0) (b : BaseChoice ℓ.side n) (c : TorusBond n) :
    ∫ g, kernelOfElement ℓ x w b c g ∂haarUnit = 1 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.ScoreProducts.integral_kernelOfElement_eq_one <;> assumption
private theorem integral_prod_bonds (K : TorusBond n → UnitQuaternion → ℝ) :
    ∫ V : TorusField n, ∏ c : TorusBond n, K c (V c.1 c.2) ∂(fieldHaar n) =
      ∏ c : TorusBond n, ∫ g, K c g ∂haarUnit := by apply _root_.YangMills.Construction.WeightedResponses.ScoreSums.integral_prod_over_bonds <;> assumption
private theorem integral_event_le (hK : BondKernelProperties) {C : ℝ} (hC0 : 0 < C)
    (hO : ∀ s : ℝ, 0 ≤ s → logPartitionGap s ≤ C * Real.log (2 + s)) (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters)
    (ha : 1 ≤ ℓ.coupling) {x : ℝ} (hx : 0 ≤ x)
    (W : TorusField (n * ℓ.side)) (b : BaseChoice ℓ.side n) (c : TorusBond n) (f : ℝ) :
    ∫ V : TorusField n, (open Classical in if f < bondFit ℓ W V b c then
        ∏ c' : (stepBlockFrame ℓ.side n).Cell × Fin 4,
          bondKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
            (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c' else 0) ∂(fieldHaar n) ≤
      Real.exp (C * Real.log (2 + ℓ.coupling * x) - ℓ.coupling * x * f) := by
  classical
  set w := readAtLevel (stepBlockFrame ℓ.side n) 0 W with hw
  set E := Real.exp (C * Real.log (2 + ℓ.coupling * x) - ℓ.coupling * x * f) with hE
  set K : TorusBond n → UnitQuaternion → ℝ := fun c' g =>
    if c' = c then (if f < fitOfElement ℓ w b c g then kernelOfElement ℓ x w b c g else 0)
    else kernelOfElement ℓ x w b c' g with hKdef
  have hprod : ∀ V : TorusField n, ∏ c' : (stepBlockFrame ℓ.side n).Cell × Fin 4,
      bondKernel ℓ x w (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c' =
        ∏ c' : TorusBond n, kernelOfElement ℓ x w b c' (V c'.1 c'.2) := by
    intro V
    rw [← (Equiv.prodCongr (torusSiteEquivCell (L := ℓ.side) (n := n)) (Equiv.refl (Fin 4))).prod_comp]
    refine Finset.prod_congr rfl fun c' _ => ?_
    exact bondKernelAt_eq_kernelOfElement ℓ x W V b c'
  have hsplit : ∀ V : TorusField n, (if f < bondFit ℓ W V b c then
      ∏ c' : (stepBlockFrame ℓ.side n).Cell × Fin 4,
        bondKernel ℓ x w (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c' else 0) =
      ∏ c' : TorusBond n, K c' (V c'.1 c'.2) := by
    intro V
    rw [hprod, bondFit_eq_fitOfElement, ← hw, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c),
      ← Finset.mul_prod_erase Finset.univ (fun c' : TorusBond n => K c' (V c'.1 c'.2)) (Finset.mem_univ c)]
    have hrest : ∏ c' ∈ Finset.univ.erase c, K c' (V c'.1 c'.2) =
        ∏ c' ∈ Finset.univ.erase c, kernelOfElement ℓ x w b c' (V c'.1 c'.2) :=
      Finset.prod_congr rfl fun c' hc' => by simp [hKdef, Finset.ne_of_mem_erase hc']
    rw [hrest]
    simp only [hKdef, if_true]
    split_ifs <;> simp
  simp only [hsplit]
  rw [integral_prod_bonds]
  have hother : ∀ c' ∈ Finset.univ.erase c, ∫ g, K c' g ∂haarUnit = 1 := by
    intro c' hc'
    have : ∀ g, K c' g = kernelOfElement ℓ x w b c' g := fun g => by simp [hKdef, Finset.ne_of_mem_erase hc']
    simp only [this]
    exact integral_kernelOfElement hK ℓ x w b c'
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c), Finset.prod_eq_one hother, mul_one]
  have hKc : ∀ g, K c g = if f < fitOfElement ℓ w b c g then kernelOfElement ℓ x w b c g else 0 :=
    fun g => by simp [hKdef]
  simp only [hKc]
  have hpos : ∀ g, 0 ≤ kernelOfElement ℓ x w b c g := fun g => by
    unfold kernelOfElement
    have hz := (hK.1 (ℓ.coupling * x * ‖bondMean ℓ w b c‖)
      (mul_nonneg (mul_nonneg (by linarith) hx) (norm_nonneg _))).1
    exact div_nonneg (Real.exp_pos _).le (by linarith)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hle : ∫ g, (if f < fitOfElement ℓ w b c g then kernelOfElement ℓ x w b c g else 0) ∂haarUnit ≤
      ∫ _g : UnitQuaternion, E ∂haarUnit := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => ?_) (integrable_const _)
      (Filter.Eventually.of_forall fun g => ?_)
    · show 0 ≤ (if f < fitOfElement ℓ w b c g then kernelOfElement ℓ x w b c g else 0)
      split_ifs
      · exact hpos g
      · exact le_rfl
    · show (if f < fitOfElement ℓ w b c g then kernelOfElement ℓ x w b c g else 0) ≤ E
      split_ifs with h
      · exact kernelOfElement_le_exp hK hC0 hO ℓ ha hx w b c f g h
      · exact hE0
  simpa using hle
section Marks
private theorem cutoffFactor_mem_Icc {ρ : ℝ} {p : ℝ → ℝ} (h : IsCutoff ρ p) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ cutoffFactor ρ p u ∧ cutoffFactor ρ p u ≤ 1 := by apply _root_.YangMills.SharedProofs.p2957 <;> assumption
variable (R : StepSetup)
private theorem markLaw_nonneg (hc : IsCutoff R.ballRadius R.barrierFn) (W : TorusField (n * R.params.side))
    (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side))) : 0 ≤ markLaw R W V bad := by
  unfold markLaw
  split_ifs
  · unfold markProduct
    refine Finset.prod_nonneg fun b _ => ?_
    have hb : 0 ≤ bondMark R V W b ∧ bondMark R V W b ≤ 1 := cutoffFactor_mem_Icc hc (norm_nonneg _)
    split_ifs <;> linarith [hb.1, hb.2]
  · exact le_rfl
  · exact zero_le_one
  · exact le_rfl
private theorem sum_powerset_prod_ite {ι : Type} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ) :
    ∑ t ∈ s.powerset, ∏ i ∈ s, (if i ∈ t then f i else g i) = ∏ i ∈ s, (f i + g i) := by apply _root_.YangMills.SharedProofs.p12670 <;> assumption
private theorem sum_markLaw (W : TorusField (n * R.params.side)) (V : TorusField n) :
    ∑ bad : Finset (TorusBond (n * R.params.side)), markLaw R W V bad = 1 := by
  classical
  by_cases hn : R.params.side ∣ n ∧ 64 ≤ n
  swap
  · simp only [markLaw, if_neg hn]
    simp
  have e : ∀ bad : Finset (TorusBond (n * R.params.side)), markLaw R W V bad =
      if bad ∈ (markedBonds R (hotCoreSites R V)).powerset then
        ∏ b ∈ markedBonds R (hotCoreSites R V), (if b ∈ bad then 1 - bondMark R V W b else bondMark R V W b)
      else 0 := by
    intro bad
    simp only [markLaw, markProduct, Finset.mem_powerset, if_pos hn]
  simp only [e]
  rw [Finset.sum_ite_mem Finset.univ, Finset.univ_inter, sum_powerset_prod_ite]
  simp
end Marks
section Outcomes
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters}
private instance (L m : ℕ) : DiscreteMeasurableSpace (BaseChoice L m) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance (m : ℕ) : DiscreteMeasurableSpace (BondSet m) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance (m : ℕ) [NeZero m] : Fintype (BondSet m) := inferInstanceAs (Fintype (Finset (TorusBond m)))
private instance (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (m : ℕ) [NeZero m] : IsFiniteMeasure (stepReferenceMeasure ℓ m) := by
  unfold stepReferenceMeasure
  infer_instance
private theorem measurable_of_slices {X : Type} [MeasurableSpace X] {f : X × StepOutcome ℓ n → ℝ}
    (h : ∀ (b : BaseChoice ℓ.side n) (bad : BondSet (n * ℓ.side)),
      Measurable fun p : X × TorusField n => f (p.1, (b, p.2, bad))) : Measurable f := by
  have h1 : Measurable fun z : (BaseChoice ℓ.side n × BondSet (n * ℓ.side)) × (X × TorusField n) =>
      f (z.2.1, (z.1.1, z.2.2, z.1.2)) :=
    measurable_from_prod_countable_right fun x => h x.1 x.2
  have h2 : Measurable fun u : X × StepOutcome ℓ n =>
      (((u.2.1, u.2.2.2), (u.1, u.2.2.1)) : (BaseChoice ℓ.side n × BondSet (n * ℓ.side)) × (X × TorusField n)) :=
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
      (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  exact h1.comp h2
private theorem measurable_comp_pair {X Y Z E : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace E] {g : Y × Z → E} (hg : Measurable g) {A : X → Y} {B : X → Z} (hA : Measurable A)
    (hB : Measurable B) :
    Measurable fun x => g (A x, B x) :=
  hg.comp (hA.prodMk hB)
private theorem measurable_topField (s m : ℕ) : Measurable (topField ℓ s m) := by apply _root_.YangMills.SharedProofs.p12845 <;> assumption
private theorem stage_isCutoff (T : StageTower ℓ) (h : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (t : ℕ) :
    IsCutoff (T.stage t).toStepSetup.ballRadius (T.stage t).toStepSetup.barrierFn := by apply _root_.YangMills.SharedProofs.p16 <;> assumption
private theorem withDensity_prod_le {A D : Type} [MeasurableSpace A] [MeasurableSpace D] {μ : Measure A}
    [IsProbabilityMeasure μ] {ρ : Measure D} [SFinite ρ] {w : A × D → ENNReal} (hw : Measurable w)
    {S : Set (A × D)} (hS : MeasurableSet S) {e : ENNReal}
    (h : ∀ a, ∫⁻ d, S.indicator w (a, d) ∂ρ ≤ e) : (μ.prod ρ).withDensity w S ≤ e := by
  rw [withDensity_apply _ hS, ← lintegral_indicator hS, lintegral_prod _ (hw.indicator hS).aemeasurable]
  calc ∫⁻ a, ∫⁻ d, S.indicator w (a, d) ∂ρ ∂μ ≤ ∫⁻ _a, e ∂μ := lintegral_mono h
    _ = e := by simp
set_option maxHeartbeats 400000 in
private theorem lintegral_event_le (hS : StepTransitionDensityBounds) (hK : BondKernelProperties)
    (hB : BondKernelBorel) {C : ℝ} (hC0 : 0 < C)
    (hO : ∀ s : ℝ, 0 ≤ s → logPartitionGap s ≤ C * Real.log (2 + s)) (R : StepSetup)
    (ha : 1 ≤ R.params.coupling) (hx : 0 ≤ R.coupling)
    (hc : IsCutoff R.ballRadius R.barrierFn)
    (hmark : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (W : TorusField (n * R.params.side)) (c : TorusBond n) (f : ℝ) :
    ∫⁻ d : StepOutcome R.params n, (if f < bondFit R.params W d.2.1 d.1 c then
        ENNReal.ofReal (stepOutcomeDensity R W d) else 0) ∂(stepReferenceMeasure R.params n) ≤
      ENNReal.ofReal (Real.exp (C * Real.log (2 + R.params.coupling * R.coupling) -
        R.params.coupling * R.coupling * f)) := by
  classical
  set E := Real.exp (C * Real.log (2 + R.params.coupling * R.coupling) - R.params.coupling * R.coupling * f)
    with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hsl : ∀ (b : BaseChoice R.params.side n), Measurable fun V : TorusField n => bondFit R.params W V b c :=
    fun b => measurable_comp_pair
      (g := fun p : TorusField (n * R.params.side) × TorusField n => bondFit R.params p.1 p.2 b c)
      (measurable_bondFit hB R.params b c) measurable_const measurable_id
  have hsd : ∀ b : BaseChoice R.params.side n, Measurable fun V : TorusField n =>
      WeightedResponses.stepTransitionDensity R.params R.coupling W b V :=
    fun b => measurable_comp_pair (g := fun p : TorusField (n * R.params.side) × TorusField n =>
        WeightedResponses.stepTransitionDensity R.params R.coupling p.1 b p.2)
      ((hS R.params R.coupling n).1 b) measurable_const measurable_id
  have hcn : ∀ bad : BondSet (n * R.params.side), Measurable fun V : TorusField n => markLaw R W V bad :=
    fun bad => measurable_comp_pair (g := fun p : TorusField (n * R.params.side) × TorusField n =>
      markLaw R p.1 p.2 bad) (hmark bad) measurable_const measurable_id
  set G : StepOutcome R.params n → ℝ := fun d =>
    if f < bondFit R.params W d.2.1 d.1 c then stepOutcomeDensity R W d else 0 with hG
  have hGm : Measurable G := by
    have h0 : Measurable fun p : Unit × StepOutcome R.params n => G p.2 := by
      refine measurable_of_slices fun b bad => ?_
      exact Measurable.ite (measurableSet_lt measurable_const ((hsl b).comp measurable_snd))
        (((hsd b).comp measurable_snd).mul ((hcn bad).comp measurable_snd)) measurable_const
    exact measurable_comp_pair (g := fun p : Unit × StepOutcome R.params n => G p.2) h0 (A := fun _ => ())
      (B := id) measurable_const measurable_id
  have hFG : ∀ d : StepOutcome R.params n, (if f < bondFit R.params W d.2.1 d.1 c then
      ENNReal.ofReal (stepOutcomeDensity R W d) else 0) = ENNReal.ofReal (G d) := by
    intro d
    simp only [hG]
    split_ifs <;> simp
  simp only [hFG]
  obtain ⟨C₀, hC₀⟩ := (hS R.params R.coupling n).2
  set H : BaseChoice R.params.side n → TorusField n → ℝ := fun b V =>
    if f < bondFit R.params W V b c then WeightedResponses.stepTransitionDensity R.params R.coupling W b V else 0
    with hH
  have hHnn : ∀ b V, 0 ≤ H b V := by
    intro b V
    simp only [hH]
    split_ifs
    · exact (hC₀ W b V).1
    · exact le_rfl
  have hHm : ∀ b, Measurable (H b) := fun b =>
    Measurable.ite (measurableSet_lt measurable_const (hsl b)) (hsd b) measurable_const
  have hHi : ∀ b, Integrable (H b) (fieldHaar n) := fun b =>
    Integrable.of_bound (hHm b).aestronglyMeasurable C₀ (Filter.Eventually.of_forall fun V => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hHnn b V)]
      simp only [hH]
      split_ifs
      · exact (hC₀ W b V).2
      · exact (hC₀ W b V).1.trans (hC₀ W b V).2)
  have hbad : ∀ (b : BaseChoice R.params.side n) (V : TorusField n),
      ∫⁻ bad : BondSet (n * R.params.side), ENNReal.ofReal (G (b, V, bad)) ∂Measure.count =
        ENNReal.ofReal (H b V) := by
    intro b V
    rw [lintegral_count, tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      simp only [hG, hH]
      split_ifs with h
      · show ∑ bad : BondSet (n * R.params.side),
            WeightedResponses.stepTransitionDensity R.params R.coupling W b V * markLaw R W V bad = _
        have hs : ∑ bad : BondSet (n * R.params.side), markLaw R W V bad = 1 := sum_markLaw R W V
        exact (Finset.mul_sum _ _ _).symm.trans (by rw [hs, mul_one])
      · simp
    · intro bad _
      simp only [hG]
      split_ifs
      · exact mul_nonneg (hC₀ W b V).1 (markLaw_nonneg R hc W V bad)
      · exact le_rfl
  have hb : ∀ b : BaseChoice R.params.side n,
      ∫⁻ y, ENNReal.ofReal (G (b, y)) ∂((fieldHaar n).prod Measure.count) =
        ENNReal.ofReal (∫ V, H b V ∂(fieldHaar n)) := by
    intro b
    have hm : Measurable fun y : TorusField n × BondSet (n * R.params.side) => ENNReal.ofReal (G (b, y)) :=
      (hGm.comp measurable_prodMk_left).ennreal_ofReal
    rw [lintegral_prod _ hm.aemeasurable,
      ofReal_integral_eq_lintegral_ofReal (hHi b) (Filter.Eventually.of_forall (hHnn b))]
    exact lintegral_congr fun V => hbad b V
  unfold stepReferenceMeasure
  rw [lintegral_prod _ hGm.ennreal_ofReal.aemeasurable, lintegral_count, tsum_fintype]
  simp only [hb]
  rw [← ENNReal.ofReal_sum_of_nonneg fun b _ => integral_nonneg (hHnn b)]
  refine ENNReal.ofReal_le_ofReal ?_
  set Bs := baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) with hBs
  have hterm : ∀ b : BaseChoice R.params.side n, ∫ V, H b V ∂(fieldHaar n) ≤
      if b ∈ Bs then (1 / (Bs.card : ℝ)) * E else 0 := by
    intro b
    by_cases hbB : b ∈ Bs
    · rw [if_pos hbB]
      have he : ∀ V, H b V = (1 / (Bs.card : ℝ)) * (if f < bondFit R.params W V b c then
          ∏ c' : (stepBlockFrame R.params.side n).Cell × Fin 4,
            bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
              (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c' else 0) := by
        intro V
        simp only [hH]
        unfold WeightedResponses.stepTransitionDensity
        rw [if_pos hbB]
        split_ifs <;> simp [hBs]
      simp only [he]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_event_le hK hC0 hO R.params ha hx W b c f) (by positivity)
    · rw [if_neg hbB]
      have he : ∀ V, H b V = 0 := by
        intro V
        simp only [hH]
        unfold WeightedResponses.stepTransitionDensity
        rw [if_neg hbB]
        simp
      simp [he]
  refine (Finset.sum_le_sum fun b _ => hterm b).trans ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos Bs.card with h0 | h0
  · simp [h0, hE0]
  · have : (Bs.card : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
    field_simp
    exact le_rfl
end Outcomes
set_option maxHeartbeats 400000 in
theorem bondFitTailBound_holds (hS : StepTransitionDensityBounds) (hK : BondKernelProperties)
    (hB : BondKernelBorel) (hO : LogPartitionGapLogGrowth) : BondFitTailBound := by
  obtain ⟨C, hC0, hOm⟩ := hO
  refine ⟨C, hC0, ?_⟩
  intro ℓ ha T β hcut hmark j n _ hp hx c f
  classical
  refine ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le ?_
  set R := (T.stage j).toStepSetup with hR
  set w : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n → ENNReal := fun u =>
    ENNReal.ofReal (stepOutcomeDensity R (topField ℓ j (n * ℓ.side) u.1) u.2) with hw
  have hwm : Measurable w := by
    have h1 : Measurable fun p : TorusField (n * ℓ.side) × StepOutcome ℓ n => stepOutcomeDensity R p.1 p.2 :=
      measurable_of_slices fun b bad => ((hS ℓ R.coupling n).1 b).mul (hmark j n bad)
    exact (measurable_comp_pair
      (g := fun p : TorusField (n * ℓ.side) × StepOutcome ℓ n => stepOutcomeDensity R p.1 p.2) h1
      ((measurable_topField j (n * ℓ.side)).comp measurable_fst) measurable_snd).ennreal_ofReal
  set S : Set (MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n) :=
    {u | f < bondFit ℓ (topField ℓ j (n * ℓ.side) u.1) u.2.2.1 u.2.1 c} with hSdef
  have hSm : MeasurableSet S := by
    refine measurableSet_lt measurable_const ?_
    refine measurable_of_slices (f := fun u : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n =>
      bondFit ℓ (topField ℓ j (n * ℓ.side) u.1) u.2.2.1 u.2.1 c) fun b _ => ?_
    exact measurable_comp_pair (g := fun p : TorusField (n * ℓ.side) × TorusField n => bondFit ℓ p.1 p.2 b c)
      (measurable_bondFit hB ℓ b c) ((measurable_topField j (n * ℓ.side)).comp measurable_fst) measurable_snd
  refine withDensity_prod_le (μ := markedSampleLaw T β j (n * ℓ.side)) (ρ := stepReferenceMeasure ℓ n) hwm hSm
    fun a => ?_
  have e : ∀ d : StepOutcome ℓ n, S.indicator w (a, d) =
      if f < bondFit ℓ (topField ℓ j (n * ℓ.side) a) d.2.1 d.1 c then
        ENNReal.ofReal (stepOutcomeDensity R (topField ℓ j (n * ℓ.side) a) d) else 0 := by
    intro d
    simp only [Set.indicator, hSdef, Set.mem_setOf_eq, hw]
  simp only [e]
  exact lintegral_event_le hS hK hB hC0 hOm R ha hx (stage_isCutoff T hcut j) (fun bad => hmark j n bad) _ c f
end YangMills.Construction.BoxLaws
end
