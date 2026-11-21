import YangMills.Construction.FreeEnergiesOfTheFlow.CompletedObservablesAreBoundedProof
import YangMills.Construction.FreeEnergiesOfTheFlow.FittedResponsesAreMeansProof
import YangMills.Construction.FreeEnergiesOfTheFlow.MeansGivenAStateReadTheCasesProof
import YangMills.Construction.FreeEnergiesOfTheFlow.StateOfAStepIsBorel
import YangMills.Construction.ResponseInTheExpansion.MeanOfScoresOverAStep
import YangMills.Construction.ResponseInTheExpansion.TheStepDensity
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.FreeEnergiesOfTheFlow
open StepSettings TorusLumps TorusFields WeightedResponses StepCosts BlockAverages ColdStepAtMirrorFrames
section Abstract
variable {A D Q Q' : Type} [mA : MeasurableSpace A] [MeasurableSpace D] [MeasurableSpace Q] [MeasurableSpace Q']
  {μ : Measure A} {ρ : Measure D} [SFinite ρ] [IsProbabilityMeasure μ]
private theorem isProbabilityMeasure_densityProd {w : A × D → ℝ} (hw : Measurable w)
    (h1 : ∀ a, ∫⁻ d, ENNReal.ofReal (w (a, d)) ∂ρ = 1) :
    IsProbabilityMeasure ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_prod _ hw.ennreal_ofReal.aemeasurable]
  simp [h1]
abbrev _root_.YangMills.SharedProofs.p11113 := @isProbabilityMeasure_densityProd
private theorem measurePreserving_fst_densityProd {w : A × D → ℝ} (hw : Measurable w)
    (h1 : ∀ a, ∫⁻ d, ENNReal.ofReal (w (a, d)) ∂ρ = 1) :
    MeasurePreserving (Prod.fst : A × D → A) ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)) μ := by
  refine ⟨measurable_fst, ?_⟩
  ext B hB
  have hS : MeasurableSet ((Prod.fst : A × D → A) ⁻¹' B) := measurable_fst hB
  have hin : ∀ a, ∫⁻ d, ((Prod.fst : A × D → A) ⁻¹' B).indicator
      (fun u => ENNReal.ofReal (w u)) (a, d) ∂ρ = B.indicator 1 a := by
    intro a
    by_cases ha : a ∈ B
    · have e : ∀ d, ((Prod.fst : A × D → A) ⁻¹' B).indicator (fun u => ENNReal.ofReal (w u)) (a, d) =
          ENNReal.ofReal (w (a, d)) := fun d =>
        Set.indicator_of_mem (show (a, d) ∈ (Prod.fst : A × D → A) ⁻¹' B from ha) _
      simp only [e, h1, Set.indicator_of_mem ha, Pi.one_apply]
    · have e : ∀ d, ((Prod.fst : A × D → A) ⁻¹' B).indicator (fun u => ENNReal.ofReal (w u)) (a, d) = 0 :=
        fun d => Set.indicator_of_notMem (show (a, d) ∉ (Prod.fst : A × D → A) ⁻¹' B from ha) _
      simp only [e, lintegral_zero, Set.indicator_of_notMem ha]
  rw [Measure.map_apply measurable_fst hB, withDensity_apply _ hS, ← lintegral_indicator hS,
    lintegral_prod _ (hw.ennreal_ofReal.indicator hS).aemeasurable]
  simp only [hin]
  exact lintegral_indicator_one hB
abbrev _root_.YangMills.SharedProofs.p1188 := @measurePreserving_fst_densityProd
private theorem integral_densityProd {w : A × D → ℝ} (hw : Measurable w) (h0 : ∀ u, 0 ≤ w u) {g : A × D → ℝ}
    (hg : Integrable g ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u))) :
    ∫ u, g u ∂((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)) =
      ∫ a, ∫ d, w (a, d) * g (a, d) ∂ρ ∂μ := by
  have hm : Measurable fun u => (w u).toNNReal := hw.real_toNNReal
  have hν : ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)) =
      (μ.prod ρ).withDensity fun u => ((w u).toNNReal : ENNReal) := rfl
  rw [hν] at hg ⊢
  have hint := (integrable_withDensity_iff_integrable_smul hm).1 hg
  rw [integral_withDensity_eq_integral_smul hm g, integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun d => ?_)
  show (w (a, d)).toNNReal • g (a, d) = w (a, d) * g (a, d)
  rw [NNReal.smul_def, Real.coe_toNNReal _ (h0 _), smul_eq_mul]
abbrev _root_.YangMills.SharedProofs.p3265 := @integral_densityProd
private def kernelAverage (ρ : Measure D) (w c : Q × D → ℝ) (q : Q) : ℝ := ∫ d, w (q, d) * c (q, d) ∂ρ
private theorem kernelAverage_measurable {w c : Q × D → ℝ} (hw : Measurable w) (hc : Measurable c) :
    Measurable (kernelAverage ρ w c) := by
  have h : StronglyMeasurable (Function.uncurry fun (q : Q) (d : D) => w (q, d) * c (q, d)) :=
    (hw.mul hc).stronglyMeasurable
  exact (h.integral_prod_right (ν := ρ)).measurable
private theorem kernelAverage_abs_le {w c : Q × D → ℝ} (hw : Measurable w) (h0 : ∀ p, 0 ≤ w p)
    (h1 : ∀ q, ∫⁻ d, ENNReal.ofReal (w (q, d)) ∂ρ = 1) {C : ℝ} (hC : ∀ p, |c p| ≤ C) (q : Q) :
    |kernelAverage ρ w c q| ≤ C := by
  have hm : Measurable fun d => w (q, d) := hw.comp measurable_prodMk_left
  have hfin : HasFiniteIntegral (fun d => w (q, d)) ρ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun d => h0 (q, d))).2 (by rw [h1 q]; simp)
  have hI : Integrable (fun d => w (q, d)) ρ := ⟨hm.aestronglyMeasurable, hfin⟩
  have hone : ∫ d, w (q, d) ∂ρ = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun d => h0 (q, d))
      hm.aestronglyMeasurable, h1 q]
    simp
  have hb : ‖∫ d, w (q, d) * c (q, d) ∂ρ‖ ≤ ∫ d, w (q, d) * C ∂ρ :=
    norm_integral_le_of_norm_le (hI.mul_const C) (Filter.Eventually.of_forall fun d => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h0 (q, d))]
      exact mul_le_mul_of_nonneg_left (hC _) (h0 (q, d)))
  rw [Real.norm_eq_abs] at hb
  rw [integral_mul_const, hone, one_mul] at hb
  exact hb
private def comapField {X Z : Type} [MeasurableSpace Z] (t : X → Z) : MeasurableSpace X :=
  MeasurableSpace.comap t inferInstance
private theorem condExp_mul_state_eq (τ : A → Q) (hτ : Measurable τ) {w : Q × D → ℝ} (hw : Measurable w)
    (h0 : ∀ p, 0 ≤ w p) (h1 : ∀ q, ∫⁻ d, ENNReal.ofReal (w (q, d)) ∂ρ = 1) {Ξ : Q × D → Q'} (hΞ : Measurable Ξ)
    {f : A → ℝ} (hf : Measurable f) {g : Q × D → ℝ} (hg : Measurable g) {C : ℝ}
    (hfC : ∀ a, |f a| ≤ C) (hgC : ∀ p, |g p| ≤ C) :
    ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w (τ u.1, u.2)))[fun u : A × D => f u.1 * g (τ u.1, u.2) |
        comapField fun u : A × D => Ξ (τ u.1, u.2)] =ᵐ[(μ.prod ρ).withDensity fun u => ENNReal.ofReal (w (τ u.1, u.2))]
      ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w (τ u.1, u.2)))[fun u : A × D => (μ[f | comapField τ]) u.1 * g (τ u.1, u.2) |
        comapField fun u : A × D => Ξ (τ u.1, u.2)] := by
  set P := (μ.prod ρ).withDensity fun u : A × D => ENNReal.ofReal (w (τ u.1, u.2)) with hPdef
  have hπ : Measurable fun u : A × D => (τ u.1, u.2) := (hτ.comp measurable_fst).prodMk measurable_snd
  have hW : Measurable fun u : A × D => w (τ u.1, u.2) := hw.comp hπ
  have h1' : ∀ a, ∫⁻ d, ENNReal.ofReal (w (τ (a, d).1, (a, d).2)) ∂ρ = 1 := fun a => h1 (τ a)
  have hP : IsProbabilityMeasure P := isProbabilityMeasure_densityProd hW h1'
  have hfst : MeasurePreserving (Prod.fst : A × D → A) P μ := measurePreserving_fst_densityProd hW h1'
  have hm : comapField τ ≤ mA := hτ.comap_le
  have hm' : comapField (fun u : A × D => Ξ (τ u.1, u.2)) ≤ Prod.instMeasurableSpace := (hΞ.comp hπ).comap_le
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hgC (τ (Classical.choice (by
    by_contra hne
    have : IsEmpty A := not_nonempty_iff.1 hne
    have h := measure_univ (μ := μ)
    rw [Set.univ_eq_empty_iff.2 this, measure_empty] at h
    exact zero_ne_one h)), Classical.choice (by
    by_contra hne
    have : IsEmpty D := not_nonempty_iff.1 hne
    have h := h1 (τ (Classical.choice (by
      by_contra hne'
      have : IsEmpty A := not_nonempty_iff.1 hne'
      have h := measure_univ (μ := μ)
      rw [Set.univ_eq_empty_iff.2 this, measure_empty] at h
      exact zero_ne_one h)))
    have e : ρ = 0 := Measure.eq_zero_of_isEmpty ρ
    rw [e] at h
    simp at h)))
  have hfi : Integrable f μ :=
    Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs]; exact hfC a)
  have hGi : Integrable (μ[f | comapField τ]) μ := integrable_condExp
  have hint : ∀ (h : A → ℝ), Integrable h μ → ∀ (c : Q × D → ℝ), Measurable c → ∀ C' : ℝ, (∀ p, |c p| ≤ C') →
      Integrable (fun u : A × D => h u.1 * c (τ u.1, u.2)) P := by
    intro h hh c hc C' hC'
    have h2 : Integrable (fun u : A × D => h u.1) P := (hfst.integrable_comp hh.aestronglyMeasurable).2 hh
    refine Integrable.mono' (h2.norm.mul_const C') (h2.aestronglyMeasurable.mul (hc.comp hπ).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC' _) (abs_nonneg _)
  have key : ∀ (h : A → ℝ), Integrable h μ → ∀ (c : Q × D → ℝ), Measurable c → ∀ C' : ℝ, (∀ p, |c p| ≤ C') →
      ∫ u, h u.1 * c (τ u.1, u.2) ∂P = ∫ a, h a * kernelAverage ρ w c (τ a) ∂μ := by
    intro h hh c hc C' hC'
    have e := integral_densityProd (μ := μ) (ρ := ρ) (w := fun u : A × D => w (τ u.1, u.2)) hW (fun u => h0 _)
      (hint h hh c hc C' hC')
    refine e.trans (integral_congr_ae (Filter.Eventually.of_forall fun a => ?_))
    show ∫ d, w (τ a, d) * (h a * c (τ a, d)) ∂ρ = h a * ∫ d, w (τ a, d) * c (τ a, d) ∂ρ
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun d => ?_)
    show w (τ a, d) * (h a * c (τ a, d)) = h a * (w (τ a, d) * c (τ a, d))
    ring
  have pull : ∀ (c : Q × D → ℝ), Measurable c → ∀ C' : ℝ, (∀ p, |c p| ≤ C') →
      ∫ a, f a * kernelAverage ρ w c (τ a) ∂μ = ∫ a, (μ[f | comapField τ]) a * kernelAverage ρ w c (τ a) ∂μ := by
    intro c hc C' hC'
    have hK := kernelAverage_measurable (ρ := ρ) hw hc
    have hk : StronglyMeasurable[comapField τ] fun a => kernelAverage ρ w c (τ a) :=
      (hK.comp (comap_measurable τ)).stronglyMeasurable
    have hki : Measurable fun a => kernelAverage ρ w c (τ a) := hK.comp hτ
    have hfk : Integrable (f * fun a => kernelAverage ρ w c (τ a)) μ :=
      Integrable.of_bound (hf.mul hki).aestronglyMeasurable (C * C') (Filter.Eventually.of_forall fun a => by
        show ‖f a * kernelAverage ρ w c (τ a)‖ ≤ C * C'
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hfC a) (kernelAverage_abs_le hw h0 h1 hC' _) (abs_nonneg _) hC0)
    have e := condExp_mul_of_stronglyMeasurable_right (m := comapField τ) hk hfk hfi
    calc ∫ a, f a * kernelAverage ρ w c (τ a) ∂μ = ∫ a, (μ[f * fun a => kernelAverage ρ w c (τ a) | comapField τ]) a ∂μ :=
          (integral_condExp hm).symm
      _ = ∫ a, (μ[f | comapField τ]) a * kernelAverage ρ w c (τ a) ∂μ := integral_congr_ae e
  have hφ₁ : Integrable (fun u : A × D => f u.1 * g (τ u.1, u.2)) P := hint f hfi g hg C hgC
  have hφ₂ : Integrable (fun u : A × D => (μ[f | comapField τ]) u.1 * g (τ u.1, u.2)) P := hint _ hGi g hg C hgC
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm' hφ₁ (fun s _ _ => integrable_condExp.integrableOn)
    (fun s hs _ => ?_) stronglyMeasurable_condExp.aestronglyMeasurable).symm
  rw [setIntegral_condExp hm' hφ₂ hs]
  have hs0 : MeasurableSet[MeasurableSpace.comap (fun u : A × D => Ξ (τ u.1, u.2)) inferInstance] s := hs
  obtain ⟨E, hE, rfl⟩ := hs0
  have hE' : MeasurableSet (Ξ ⁻¹' E) := hΞ hE
  have hs' : MeasurableSet ((fun u : A × D => Ξ (τ u.1, u.2)) ⁻¹' E) := (hΞ.comp hπ) hE
  have hc : Measurable ((Ξ ⁻¹' E).indicator g) := hg.indicator hE'
  have hcC : ∀ p, |(Ξ ⁻¹' E).indicator g p| ≤ C := by
    intro p
    by_cases hp : p ∈ Ξ ⁻¹' E
    · rw [Set.indicator_of_mem hp]; exact hgC p
    · rw [Set.indicator_of_notMem hp, abs_zero]; exact hC0
  have ind : ∀ h : A → ℝ, ∫ u in (fun u : A × D => Ξ (τ u.1, u.2)) ⁻¹' E, h u.1 * g (τ u.1, u.2) ∂P =
      ∫ u, h u.1 * (Ξ ⁻¹' E).indicator g (τ u.1, u.2) ∂P := by
    intro h
    rw [← integral_indicator hs']
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    by_cases hu : u ∈ (fun u : A × D => Ξ (τ u.1, u.2)) ⁻¹' E
    · have hu' : (τ u.1, u.2) ∈ Ξ ⁻¹' E := hu
      rw [Set.indicator_of_mem hu]
      show h u.1 * g (τ u.1, u.2) = h u.1 * (Ξ ⁻¹' E).indicator g (τ u.1, u.2)
      rw [Set.indicator_of_mem hu']
    · have hu' : (τ u.1, u.2) ∉ Ξ ⁻¹' E := hu
      rw [Set.indicator_of_notMem hu]
      show 0 = h u.1 * (Ξ ⁻¹' E).indicator g (τ u.1, u.2)
      rw [Set.indicator_of_notMem hu', mul_zero]
  rw [ind, ind, key _ hGi _ hc C hcC, key _ hfi _ hc C hcC, pull _ hc C hcC]
private theorem condExp_mul_state_eq' (τ : A → Q) (hτ : Measurable τ) {w : Q × D → ℝ} (hw : Measurable w)
    (h0 : ∀ p, 0 ≤ w p) (h1 : ∀ q, ∫⁻ d, ENNReal.ofReal (w (q, d)) ∂ρ = 1) {Ξ : Q × D → Q'} (hΞ : Measurable Ξ)
    {f : A → ℝ} (hf : Measurable f) {g : Q × D → ℝ} (hg : Measurable g) {C : ℝ}
    (hfC : ∀ a, |f a| ≤ C) (hgC : ∀ p, |g p| ≤ C) (wt : A × D → ℝ) (hwt : ∀ u, wt u = w (τ u.1, u.2))
    (t' : A × D → Q') (ht' : ∀ u, t' u = Ξ (τ u.1, u.2)) :
    ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (wt u))[fun u : A × D => f u.1 * g (τ u.1, u.2) |
        MeasurableSpace.comap t' inferInstance] =ᵐ[(μ.prod ρ).withDensity fun u => ENNReal.ofReal (wt u)]
      ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (wt u))[fun u : A × D =>
          (μ[f | MeasurableSpace.comap τ inferInstance]) u.1 * g (τ u.1, u.2) |
        MeasurableSpace.comap t' inferInstance] := by
  obtain rfl : wt = fun u => w (τ u.1, u.2) := funext hwt
  obtain rfl : t' = fun u => Ξ (τ u.1, u.2) := funext ht'
  exact condExp_mul_state_eq τ hτ hw h0 h1 hΞ hf hg hfC hgC
end Abstract
section Cutoff
private theorem cutoffFactor_mem_unit {ρ : ℝ} {p : ℝ → ℝ} (h : IsCutoff ρ p) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ cutoffFactor ρ p u ∧ cutoffFactor ρ p u ≤ 1 := by apply _root_.YangMills.SharedProofs.p2957 <;> assumption
end Cutoff
section Marks
variable (R : StepSetup) {n : ℕ} [NeZero n]
private theorem bondMark_mem_unit (hc : IsCutoff R.ballRadius R.barrierFn) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (b : TorusBond (n * R.params.side)) :
    0 ≤ bondMark R V W b ∧ bondMark R V W b ≤ 1 :=
  cutoffFactor_mem_unit hc (norm_nonneg _)
private theorem markLaw_nonneg (hc : IsCutoff R.ballRadius R.barrierFn) (W : TorusField (n * R.params.side))
    (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side))) :
    0 ≤ markLaw R W V bad := by
  unfold markLaw
  split_ifs
  · unfold markProduct
    refine Finset.prod_nonneg fun b _ => ?_
    have := bondMark_mem_unit R hc V W b
    split_ifs <;> linarith [this.1, this.2]
  · exact le_rfl
  · exact zero_le_one
  · exact le_rfl
abbrev _root_.YangMills.SharedProofs.p19776 := @markLaw_nonneg
private theorem sum_powerset_prod_ite {ι : Type} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ) :
    ∑ t ∈ s.powerset, ∏ i ∈ s, (if i ∈ t then f i else g i) = ∏ i ∈ s, (f i + g i) := by
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hts : t ⊆ s := Finset.mem_powerset.1 ht
  rw [← Finset.prod_sdiff hts, mul_comm]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => by simp [hi]
  · exact Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_sdiff.1 hi).2]
abbrev _root_.YangMills.SharedProofs.p12670 := @sum_powerset_prod_ite
private theorem sum_markLaw (W : TorusField (n * R.params.side)) (V : TorusField n) :
    ∑ bad : Finset (TorusBond (n * R.params.side)), markLaw R W V bad = 1 := by
  classical
  by_cases hg : R.params.side ∣ n ∧ 64 ≤ n
  · have e : ∀ bad : Finset (TorusBond (n * R.params.side)), markLaw R W V bad =
        if bad ∈ (markedBonds R (hotCoreSites R V)).powerset then
          ∏ b ∈ markedBonds R (hotCoreSites R V), (if b ∈ bad then 1 - bondMark R V W b else bondMark R V W b)
        else 0 := by
      intro bad
      simp only [markLaw, markProduct, Finset.mem_powerset, if_pos hg]
    simp only [e]
    rw [Finset.sum_ite_mem Finset.univ, Finset.univ_inter, sum_powerset_prod_ite]
    simp
  · have e : ∀ bad : Finset (TorusBond (n * R.params.side)), markLaw R W V bad = if bad = ∅ then 1 else 0 := by
      intro bad
      simp only [markLaw, if_neg hg]
    simp only [e]
    simp
abbrev _root_.YangMills.SharedProofs.p2142 := @sum_markLaw
private theorem markLaw_le_one (hc : IsCutoff R.ballRadius R.barrierFn) (W : TorusField (n * R.params.side))
    (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side))) :
    markLaw R W V bad ≤ 1 := by
  rw [← sum_markLaw R W V]
  exact Finset.single_le_sum (f := markLaw R W V) (fun b _ => markLaw_nonneg R hc W V b) (Finset.mem_univ bad)
abbrev _root_.YangMills.SharedProofs.p42074 := @markLaw_le_one
end Marks
section Outcomes
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters}
private instance (L n : ℕ) : DiscreteMeasurableSpace (BaseChoice L n) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance (m : ℕ) : DiscreteMeasurableSpace (BondSet m) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance (m : ℕ) [NeZero m] : Fintype (BondSet m) := inferInstanceAs (Fintype (Finset (TorusBond m)))
private instance (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (n : ℕ) [NeZero n] : IsFiniteMeasure (stepReferenceMeasure ℓ n) := by
  unfold stepReferenceMeasure
  infer_instance
private theorem measurable_slice {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {f : X × Y → ℝ}
    (hf : Measurable f) (x : X) : Measurable fun y => f (x, y) :=
  hf.comp measurable_prodMk_left
private theorem measurable_of_stepOutcome {X : Type} [MeasurableSpace X] {n : ℕ} [NeZero n]
    {f : X × StepOutcome ℓ n → ℝ}
    (h : ∀ (b : BaseChoice ℓ.side n) (bad : BondSet (n * ℓ.side)),
      Measurable fun p : X × TorusField n => f (p.1, (b, p.2, bad))) : Measurable f := by apply _root_.YangMills.SharedProofs.p21057 <;> assumption
private theorem integral_stepReferenceMeasure {n : ℕ} [NeZero n] {g : StepOutcome ℓ n → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : ∀ d, |g d| ≤ C) :
    ∫ d, g d ∂(stepReferenceMeasure ℓ n) =
      ∑ b : BaseChoice ℓ.side n, ∫ V : TorusField n, ∑ bad : BondSet (n * ℓ.side), g (b, V, bad) ∂(fieldHaar n) := by
  have hI : Integrable g (stepReferenceMeasure ℓ n) :=
    Integrable.of_bound hg.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun d => by rw [Real.norm_eq_abs]; exact hC d)
  unfold stepReferenceMeasure at hI ⊢
  rw [integral_prod _ hI, integral_count]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hIb : Integrable (fun y : TorusField n × BondSet (n * ℓ.side) => g (b, y))
      ((fieldHaar n).prod (Measure.count : Measure (BondSet (n * ℓ.side)))) :=
    Integrable.of_bound (hg.comp measurable_prodMk_left).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun d => by rw [Real.norm_eq_abs]; exact hC _)
  rw [integral_prod _ hIb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  exact integral_count _
end Outcomes
section OneStep
variable (R : StepSetup) {n : ℕ} [NeZero n]
private theorem measurable_stepOutcomeDensity (hS : StepTransitionDensityBounds)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad) :
    Measurable fun p : TorusField (n * R.params.side) × StepOutcome R.params n => stepOutcomeDensity R p.1 p.2 :=
  measurable_of_stepOutcome fun b bad => ((hS R.params R.coupling n).1 b).mul (hB bad)
private theorem stepOutcomeDensity_nonneg (hS : StepTransitionDensityBounds)
    (hc : IsCutoff R.ballRadius R.barrierFn)
    (W : TorusField (n * R.params.side)) (d : StepOutcome R.params n) : 0 ≤ stepOutcomeDensity R W d := by
  obtain ⟨C, hC⟩ := (hS R.params R.coupling n).2
  exact mul_nonneg (hC _ _ _).1 (markLaw_nonneg R hc _ _ _)
abbrev _root_.YangMills.SharedProofs.p6753 := @stepOutcomeDensity_nonneg
private theorem integral_stepOutcomeDensity_mul (hS : StepTransitionDensityBounds)
    (hc : IsCutoff R.ballRadius R.barrierFn)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (W : TorusField (n * R.params.side)) {g : BaseChoice R.params.side n → TorusField n → ℝ}
    (hG : Measurable fun d : StepOutcome R.params n => g d.1 d.2.1) {C : ℝ} (hC : ∀ b V, |g b V| ≤ C) :
    ∫ d, stepOutcomeDensity R W d * g d.1 d.2.1 ∂(stepReferenceMeasure R.params n) =
      ∑ b : BaseChoice R.params.side n, ∫ V : TorusField n, g b V *
        stepTransitionDensity R.params R.coupling W b V ∂(fieldHaar n) := by
  obtain ⟨C₀, hC₀⟩ := (hS R.params R.coupling n).2
  have hm : Measurable fun d : StepOutcome R.params n => stepOutcomeDensity R W d * g d.1 d.2.1 :=
    (measurable_slice
      (f := fun p : TorusField (n * R.params.side) × StepOutcome R.params n => stepOutcomeDensity R p.1 p.2)
      (measurable_stepOutcomeDensity R hS hB) W).mul hG
  have hbd : ∀ d : StepOutcome R.params n, |stepOutcomeDensity R W d * g d.1 d.2.1| ≤ C₀ * C := by
    intro d
    have h1 : 0 ≤ stepOutcomeDensity R W d := stepOutcomeDensity_nonneg R hS hc W d
    have h2 : stepOutcomeDensity R W d ≤ C₀ := by
      have hs := hC₀ W d.1 d.2.1
      have hk := markLaw_le_one R hc W d.2.1 d.2.2
      calc stepOutcomeDensity R W d ≤ stepTransitionDensity R.params R.coupling W d.1 d.2.1 * 1 :=
            mul_le_mul_of_nonneg_left hk hs.1
        _ ≤ C₀ := by rw [mul_one]; exact hs.2
    rw [abs_mul, abs_of_nonneg h1]
    exact mul_le_mul h2 (hC _ _) (abs_nonneg _) (h1.trans h2)
  rw [integral_stepReferenceMeasure hm hbd]
  refine Finset.sum_congr rfl fun b _ => integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  have hs : ∑ bad : BondSet (n * R.params.side), markLaw R W V bad = 1 := sum_markLaw R W V
  have e : ∀ bad : BondSet (n * R.params.side), stepOutcomeDensity R W (b, V, bad) * g b V =
      (g b V * stepTransitionDensity R.params R.coupling W b V) * markLaw R W V bad := by
    intro bad
    show stepTransitionDensity R.params R.coupling W b V * markLaw R W V bad * _ = _
    ring
  show ∑ bad : BondSet (n * R.params.side), stepOutcomeDensity R W (b, V, bad) * g b V = _
  simp only [e]
  exact (Finset.mul_sum _ _ _).symm.trans (by rw [hs, mul_one])
abbrev _root_.YangMills.SharedProofs.p19566 := @integral_stepOutcomeDensity_mul
private theorem stepTransitionDensity_mass (hM : ScoreProductStepMean)
    (hf : R.params.Admissible) (hfl : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side)
    (W : TorusField (n * R.params.side)) :
    ∑ b : BaseChoice R.params.side n, ∫ V : TorusField n,
      (1 : ℝ) * stepTransitionDensity R.params R.coupling W b V ∂(fieldHaar n) = 1 :=
  hM R.params hf hfl R.coupling n W 0 Fin.elim0 (fun i => i.elim0) (fun _ i => i.elim0)
private theorem stepOutcomeDensity_integrable (hS : StepTransitionDensityBounds)
    (hc : IsCutoff R.ballRadius R.barrierFn)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (W : TorusField (n * R.params.side)) :
    Integrable (fun d : StepOutcome R.params n => stepOutcomeDensity R W d) (stepReferenceMeasure R.params n) := by
  obtain ⟨C₀, hC₀⟩ := (hS R.params R.coupling n).2
  have hm : Measurable fun d : StepOutcome R.params n => stepOutcomeDensity R W d :=
    measurable_slice
      (f := fun p : TorusField (n * R.params.side) × StepOutcome R.params n => stepOutcomeDensity R p.1 p.2)
      (measurable_stepOutcomeDensity R hS hB) W
  refine Integrable.of_bound hm.aestronglyMeasurable C₀ (Filter.Eventually.of_forall fun d => ?_)
  have hs := hC₀ W d.1 d.2.1
  have hk := markLaw_le_one R hc W d.2.1 d.2.2
  rw [Real.norm_eq_abs, abs_of_nonneg (stepOutcomeDensity_nonneg R hS hc W d)]
  calc stepOutcomeDensity R W d ≤ stepTransitionDensity R.params R.coupling W d.1 d.2.1 * 1 :=
        mul_le_mul_of_nonneg_left hk hs.1
    _ ≤ C₀ := by rw [mul_one]; exact hs.2
private theorem stepOutcomeDensity_integral (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean)
    (hf : R.params.Admissible) (hfl : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side)
    (hc : IsCutoff R.ballRadius R.barrierFn)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (W : TorusField (n * R.params.side)) :
    ∫ d, stepOutcomeDensity R W d ∂(stepReferenceMeasure R.params n) = 1 := by
  have h1 := integral_stepOutcomeDensity_mul R hS hc hB W (g := fun _ _ => 1) measurable_const (C := 1)
    (fun _ _ => (abs_one (α := ℝ)).le)
  have e : ∫ d, stepOutcomeDensity R W d ∂(stepReferenceMeasure R.params n) =
      ∫ d, stepOutcomeDensity R W d * 1 ∂(stepReferenceMeasure R.params n) :=
    integral_congr_ae (Filter.Eventually.of_forall fun d => (mul_one _).symm)
  exact e.trans (h1.trans (stepTransitionDensity_mass R hM hf hfl W))
private theorem stepOutcomeDensity_lintegral (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean)
    (hf : R.params.Admissible) (hfl : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side)
    (hc : IsCutoff R.ballRadius R.barrierFn)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (W : TorusField (n * R.params.side)) :
    ∫⁻ d, ENNReal.ofReal (stepOutcomeDensity R W d) ∂(stepReferenceMeasure R.params n) = 1 := by
  have h := ofReal_integral_eq_lintegral_ofReal (stepOutcomeDensity_integrable R hS hc hB W)
    (Filter.Eventually.of_forall fun d => stepOutcomeDensity_nonneg R hS hc W d)
  rw [← h, stepOutcomeDensity_integral R hS hM hf hfl hc hB W, ENNReal.ofReal_one]
abbrev _root_.YangMills.SharedProofs.p27860 := @stepOutcomeDensity_lintegral
end OneStep
section Stages
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters}
private theorem measurable_topField (s n : ℕ) : Measurable (topField ℓ s n) := by apply _root_.YangMills.SharedProofs.p12845 <;> assumption
private theorem stage_isCutoff (T : StageTower ℓ) (h : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (t : ℕ) :
    IsCutoff (T.stage t).toStepSetup.ballRadius (T.stage t).toStepSetup.barrierFn := by apply _root_.YangMills.SharedProofs.p16 <;> assumption
private def stageStepDensity (T : StageTower ℓ) (s n : ℕ) [NeZero n]
    (u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n) : ℝ :=
  stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2
private theorem stageState_fst (T : StageTower ℓ) (s n : ℕ) [NeZero n] (a : MarkedSample ℓ s n) :
    (stageState T s n a).1 = topField ℓ s n a := by apply _root_.YangMills.SharedProofs.p2480 <;> assumption
end Stages
theorem markovPropertyOfStageStates_holds (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean)
    (hSt : ResponseInTheExpansion.StageStatesMeasurableStatement) (hB : MeasurableNextStageState)
    (hT : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement) : MarkovPropertyOfStageStates := by
  intro ℓ hf hfl T hcut hcoin β s n _
  have hprob : IsProbabilityMeasure (markedSampleLaw T β s (n * ℓ.side)) :=
    (hT ℓ hf hfl T hcut hcoin β (fun _ => 0) s (n * ℓ.side)).1
  have hτ : Measurable (stageState T s (n * ℓ.side)) := hSt ℓ hf T s (n * ℓ.side)
  have hΞ := hB ℓ hf T s n
  have hm1 := measurable_stepOutcomeDensity (T.stage s).toStepSetup (n := n) hS (fun bad => hcoin s n bad)
  have hw : Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n =>
      stepOutcomeDensity (T.stage s).toStepSetup p.1.1 p.2 := by
    have h2 : Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n =>
        ((p.1.1, p.2) : TorusField (n * ℓ.side) × StepOutcome ℓ n) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    have h3 := hm1.comp h2
    exact h3
  have h0 : ∀ p : StageState T s (n * ℓ.side) × StepOutcome ℓ n,
      0 ≤ stepOutcomeDensity (T.stage s).toStepSetup p.1.1 p.2 := fun p =>
    stepOutcomeDensity_nonneg (T.stage s).toStepSetup hS (stage_isCutoff T hcut s) _ _
  have h1 : ∀ q : StageState T s (n * ℓ.side),
      ∫⁻ d, ENNReal.ofReal (stepOutcomeDensity (T.stage s).toStepSetup q.1 d) ∂(stepReferenceMeasure ℓ n) = 1 :=
    fun q => stepOutcomeDensity_lintegral (T.stage s).toStepSetup hS hM hf hfl (stage_isCutoff T hcut s)
      (fun bad => hcoin s n bad) q.1
  have hmT : Measurable (stageStepDensity T s n) := by
    have h2 : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
        ((topField ℓ s (n * ℓ.side) u.1, u.2) : TorusField (n * ℓ.side) × StepOutcome ℓ n) :=
      ((measurable_topField s (n * ℓ.side)).comp measurable_fst).prodMk measurable_snd
    have h3 := hm1.comp h2
    exact h3
  have hmass : ∀ a, ∫⁻ d, ENNReal.ofReal (stageStepDensity T s n (a, d)) ∂(stepReferenceMeasure ℓ n) = 1 :=
    fun a => stepOutcomeDensity_lintegral (T.stage s).toStepSetup hS hM hf hfl (stage_isCutoff T hcut s)
      (fun bad => hcoin s n bad) (topField ℓ s (n * ℓ.side) a)
  constructor
  · exact measurePreserving_fst_densityProd (μ := markedSampleLaw T β s (n * ℓ.side))
      (ρ := stepReferenceMeasure ℓ n) (w := stageStepDensity T s n) hmT hmass
  · intro f g C hfm hgm hfC hgC
    have key := condExp_mul_state_eq' (μ := markedSampleLaw T β s (n * ℓ.side)) (ρ := stepReferenceMeasure ℓ n)
      (stageState T s (n * ℓ.side)) hτ (w := fun p => stepOutcomeDensity (T.stage s).toStepSetup p.1.1 p.2)
      hw h0 h1 hΞ hfm hgm hfC hgC
      (stageStepDensity T s n) (fun u => by
        show stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2 =
          stepOutcomeDensity (T.stage s).toStepSetup (stageState T s (n * ℓ.side) u.1).1 u.2
        rw [stageState_fst])
      (fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => stageState T (s + 1) n u) (fun u => rfl)
    exact key
end YangMills.Construction.FreeEnergiesOfTheFlow
end
