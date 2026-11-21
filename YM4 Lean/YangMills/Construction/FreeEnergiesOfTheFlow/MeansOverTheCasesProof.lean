import YangMills.Construction.FreeEnergiesOfTheFlow.MeansOverTheCases
import YangMills.Construction.ResponseInTheExpansion.ManyLevelsOfSeveralSupportsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace YangMills.Construction.FreeEnergies
open StepSettings TorusFields TorusLumps WeightedResponses StepCosts
variable {R : StepSetup} {n : ℕ} [NeZero n] {C : Finset (TorusSite n)} {V : TorusField n} {q : CoarseState R n}
private theorem caseIntegral_eq_sum_integral_prod {F : CaseFunction R n} (hF : CaseIntegrable R C V q F) :
    caseIntegral R C V q F = ∑ bad ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
      ∑ b : BaseChoice R.params.side n, ∫ p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω),
        caseTerm R C V q F bad Yt b p.1 p.2
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) := by apply _root_.YangMills.SharedProofs.p48600 <;> assumption
private theorem caseTerm_congr_of_pos {F G : CaseFunction R n}
    (h : ∀ W Yt ωt bad b, IsHullState R.params R.range W Yt → 0 < stepWeight R C V W Yt ωt bad b →
      F W Yt ωt bad b = G W Yt ωt bad b)
    (h0 : ∀ W Yt ωt bad b, IsHullState R.params R.range W Yt → 0 ≤ stepWeight R C V W Yt ωt bad b) bad Yt b W ν :
    caseTerm R C V q F bad Yt b W ν = caseTerm R C V q G bad Yt b W ν := by
  unfold caseTerm
  split_ifs with hc
  · rcases (h0 (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b hc.1).eq_or_lt with hw | hw
    · rw [← hw, mul_zero, mul_zero]
    · rw [h _ _ _ _ _ hc.1 hw]
  · rfl
private theorem caseTerm_add (F G : CaseFunction R n) bad Yt b W ν :
    caseTerm R C V q (fun W Yt ωt bad b => F W Yt ωt bad b + G W Yt ωt bad b) bad Yt b W ν =
      caseTerm R C V q F bad Yt b W ν + caseTerm R C V q G bad Yt b W ν := by apply _root_.YangMills.SharedProofs.p58450 <;> assumption
private theorem caseTerm_const_mul (c : ℝ) (F : CaseFunction R n) bad Yt b W ν :
    caseTerm R C V q (fun W Yt ωt bad b => c * F W Yt ωt bad b) bad Yt b W ν =
      c * caseTerm R C V q F bad Yt b W ν := by apply _root_.YangMills.SharedProofs.p17898 <;> assumption
private theorem caseTerm_mono_of_pos {F G : CaseFunction R n}
    (h : ∀ W Yt ωt bad b, IsHullState R.params R.range W Yt → 0 < stepWeight R C V W Yt ωt bad b →
      F W Yt ωt bad b ≤ G W Yt ωt bad b)
    (h0 : ∀ W Yt ωt bad b, IsHullState R.params R.range W Yt → 0 ≤ stepWeight R C V W Yt ωt bad b) bad Yt b W ν :
    caseTerm R C V q F bad Yt b W ν ≤ caseTerm R C V q G bad Yt b W ν := by
  unfold caseTerm
  split_ifs with hc
  · rcases (h0 (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b hc.1).eq_or_lt with hw | hw
    · rw [← hw, mul_zero, mul_zero]
    · exact mul_le_mul_of_nonneg_right (h _ _ _ _ _ hc.1 hw) hw.le
  · exact le_rfl
private theorem caseTerm_one_nonneg
    (h0 : ∀ W Yt ωt bad b, IsHullState R.params R.range W Yt → 0 ≤ stepWeight R C V W Yt ωt bad b) bad Yt b W ν :
    0 ≤ caseTerm R C V q (fun _ _ _ _ _ => 1) bad Yt b W ν := by
  unfold caseTerm
  split_ifs with hc
  · rw [one_mul]
    exact h0 _ _ _ _ _ hc.1
  · exact le_rfl
private theorem coarseStateWeight_nonneg : 0 ≤ coarseStateWeight R C V q := ENNReal.toReal_nonneg
private theorem lintegral_indicator_weight_eq
    (h0 : ∀ W Yt ωt bad b, IsHullState R.params R.range W Yt → 0 ≤ stepWeight R C V W Yt ωt bad b)
    (h1 : CaseIntegrable R C V q (fun _ _ _ _ _ => 1)) bad (hb : bad ∈ (markedBonds R C).powerset) Yt b :
    (∫⁻ W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
      (open Classical in if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
          coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q then
        ENNReal.ofReal (stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) else 0)
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))) =
    ENNReal.ofReal (∫ p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω),
      caseTerm R C V q (fun _ _ _ _ _ => 1) bad Yt b p.1 p.2
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ))) := by
  classical
  have hI := h1 bad hb Yt b
  rw [ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun p => caseTerm_one_nonneg h0 bad Yt b p.1 p.2),
    lintegral_prod _ hI.aemeasurable.ennreal_ofReal]
  refine lintegral_congr fun W => lintegral_congr fun ν => ?_
  unfold caseTerm
  split_ifs with hc
  · rw [one_mul]
  · simp
private theorem caseIntegral_one_eq_weight
    (h0 : ∀ W Yt ωt bad b, IsHullState R.params R.range W Yt → 0 ≤ stepWeight R C V W Yt ωt bad b)
    (h1 : CaseIntegrable R C V q (fun _ _ _ _ _ => 1)) :
    caseIntegral R C V q (fun _ _ _ _ _ => 1) = coarseStateWeight R C V q := by
  classical
  rw [caseIntegral_eq_sum_integral_prod h1]
  have e : coarseStateMass R C V q = ∑ bad ∈ (markedBonds R C).powerset,
      ∑ Yt : Finset (TorusSite (n * R.params.side)),
      ∑ b : BaseChoice R.params.side n,
        ENNReal.ofReal (∫ p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω),
        caseTerm R C V q (fun _ _ _ _ _ => 1) bad Yt b p.1 p.2
          ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ))) := by
    unfold coarseStateMass
    exact Finset.sum_congr rfl fun bad hb => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ =>
      lintegral_indicator_weight_eq h0 h1 bad hb Yt b
  have hnn : ∀ bad Yt b, 0 ≤ ∫ p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω),
      caseTerm R C V q (fun _ _ _ _ _ => 1) bad Yt b p.1 p.2
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) := fun bad Yt b =>
    integral_nonneg fun p => caseTerm_one_nonneg h0 bad Yt b p.1 p.2
  unfold coarseStateWeight
  rw [e, ENNReal.toReal_sum (fun bad _ => ENNReal.sum_ne_top.2 fun Yt _ => ENNReal.sum_ne_top.2 fun b _ =>
    ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun bad _ => ?_
  rw [ENNReal.toReal_sum (fun Yt _ => ENNReal.sum_ne_top.2 fun b _ => ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun Yt _ => ?_
  rw [ENNReal.toReal_sum (fun b _ => ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ENNReal.toReal_ofReal (hnn bad Yt b)]
private theorem clamp_mul_of_nonneg (r x w : ℝ) (hw : 0 ≤ w) :
    max (-r) (min r x) * w = max (-(r * w)) (min (r * w) (x * w)) := by
  rw [max_mul_of_nonneg _ _ hw, min_mul_of_nonneg _ _ hw, neg_mul]
private theorem caseTerm_truncate
    (h0 : ∀ W Yt ωt bad b, IsHullState R.params R.range W Yt → 0 ≤ stepWeight R C V W Yt ωt bad b)
    (r : ℝ) (F : CaseFunction R n) bad Yt b W ν :
    caseTerm R C V q (truncateCases r F) bad Yt b W ν =
      max (-(r * caseTerm R C V q (fun _ _ _ _ _ => 1) bad Yt b W ν))
        (min (r * caseTerm R C V q (fun _ _ _ _ _ => 1) bad Yt b W ν) (caseTerm R C V q F bad Yt b W ν)) := by
  unfold caseTerm
  split_ifs with hc
  · rw [one_mul]
    exact clamp_mul_of_nonneg _ _ _ (h0 _ _ _ _ _ hc.1)
  · simp
private theorem abs_clamp_le (r x : ℝ) (hr : 0 ≤ r) : |max (-r) (min r x)| ≤ |x| := by
  rw [abs_le]
  constructor
  · rcases le_total r |x| with h | h
    · exact le_trans (by linarith) (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      exact le_min (by linarith [abs_nonneg x]) (neg_abs_le x)
  · exact max_le (by linarith [abs_nonneg x]) ((min_le_right _ _).trans (le_abs_self x))
theorem caseMeanProperties_holds : caseMeanProperties := by
  intro R n _ C V q h0
  have hcongr : ∀ F G : CaseFunction R n,
      (∀ W Yt ωt bad b, IsHullState R.params R.range W Yt → 0 < stepWeight R C V W Yt ωt bad b →
        F W Yt ωt bad b = G W Yt ωt bad b) →
      (CaseIntegrable R C V q F → CaseIntegrable R C V q G) ∧ caseMean R C V q F = caseMean R C V q G := by
    intro F G h
    have ht := caseTerm_congr_of_pos (q := q) h h0
    constructor
    · intro hF bad hb Yt b
      have e : (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
          caseTerm R C V q G bad Yt b p.1 p.2) =
          fun p => caseTerm R C V q F bad Yt b p.1 p.2 := funext fun p => (ht bad Yt b p.1 p.2).symm
      rw [e]
      exact hF bad hb Yt b
    · unfold caseMean caseIntegral
      simp only [ht]
  have hadd : ∀ F G : CaseFunction R n, CaseIntegrable R C V q F → CaseIntegrable R C V q G →
      CaseIntegrable R C V q (fun W Yt ωt bad b => F W Yt ωt bad b + G W Yt ωt bad b) ∧
      caseMean R C V q (fun W Yt ωt bad b => F W Yt ωt bad b + G W Yt ωt bad b) =
        caseMean R C V q F + caseMean R C V q G := by
    intro F G hF hG
    have hI : CaseIntegrable R C V q (fun W Yt ωt bad b => F W Yt ωt bad b + G W Yt ωt bad b) := by
      intro bad hb Yt b
      have e : (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
          caseTerm R C V q (fun W Yt ωt bad b => F W Yt ωt bad b + G W Yt ωt bad b) bad Yt b p.1 p.2) =
          fun p => caseTerm R C V q F bad Yt b p.1 p.2 + caseTerm R C V q G bad Yt b p.1 p.2 :=
        funext fun p => caseTerm_add F G bad Yt b p.1 p.2
      rw [e]
      exact (hF bad hb Yt b).add (hG bad hb Yt b)
    refine ⟨hI, ?_⟩
    unfold caseMean
    rw [caseIntegral_eq_sum_integral_prod hI, caseIntegral_eq_sum_integral_prod hF,
      caseIntegral_eq_sum_integral_prod hG, ← add_div]
    congr 1
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun bad hb => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← integral_add (hF bad hb Yt b) (hG bad hb Yt b)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => caseTerm_add F G bad Yt b p.1 p.2)
  have hmul : ∀ (c : ℝ) (F : CaseFunction R n), CaseIntegrable R C V q F →
      CaseIntegrable R C V q (fun W Yt ωt bad b => c * F W Yt ωt bad b) ∧
      caseMean R C V q (fun W Yt ωt bad b => c * F W Yt ωt bad b) = c * caseMean R C V q F := by
    intro c F hF
    have hI : CaseIntegrable R C V q (fun W Yt ωt bad b => c * F W Yt ωt bad b) := by
      intro bad hb Yt b
      have e : (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
          caseTerm R C V q (fun W Yt ωt bad b => c * F W Yt ωt bad b) bad Yt b p.1 p.2) =
          fun p => c * caseTerm R C V q F bad Yt b p.1 p.2 :=
        funext fun p => caseTerm_const_mul c F bad Yt b p.1 p.2
      rw [e]
      exact (hF bad hb Yt b).const_mul c
    refine ⟨hI, ?_⟩
    unfold caseMean
    rw [caseIntegral_eq_sum_integral_prod hI, caseIntegral_eq_sum_integral_prod hF, ← mul_div_assoc]
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun bad hb => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => caseTerm_const_mul c F bad Yt b p.1 p.2)
  have hmono : ∀ F G : CaseFunction R n, CaseIntegrable R C V q F → CaseIntegrable R C V q G →
      (∀ W Yt ωt bad b, IsHullState R.params R.range W Yt → 0 < stepWeight R C V W Yt ωt bad b →
        F W Yt ωt bad b ≤ G W Yt ωt bad b) →
      caseMean R C V q F ≤ caseMean R C V q G := by
    intro F G hF hG h
    unfold caseMean
    rw [caseIntegral_eq_sum_integral_prod hF, caseIntegral_eq_sum_integral_prod hG]
    refine div_le_div_of_nonneg_right ?_ coarseStateWeight_nonneg
    refine Finset.sum_le_sum fun bad hb => Finset.sum_le_sum fun Yt _ => Finset.sum_le_sum fun b _ => ?_
    exact integral_mono (hF bad hb Yt b) (hG bad hb Yt b) fun p => caseTerm_mono_of_pos h h0 bad Yt b p.1 p.2
  refine ⟨hcongr, hadd, hmul, hmono, ?_, ?_⟩
  · intro h1 hne
    unfold caseMean
    rw [caseIntegral_one_eq_weight h0 h1, div_self hne]
  · intro h1 F hF
    have hcut : ∀ r : ℝ, 0 ≤ r → CaseIntegrable R C V q (truncateCases r F) := by
      intro r hr bad hb Yt b
      have e : (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
          caseTerm R C V q (truncateCases r F) bad Yt b p.1 p.2) =
          fun p => max (-(r * caseTerm R C V q (fun _ _ _ _ _ => 1) bad Yt b p.1 p.2))
            (min (r * caseTerm R C V q (fun _ _ _ _ _ => 1) bad Yt b p.1 p.2)
              (caseTerm R C V q F bad Yt b p.1 p.2)) :=
        funext fun p => caseTerm_truncate h0 r F bad Yt b p.1 p.2
      rw [e]
      have h2 := (h1 bad hb Yt b).const_mul r
      exact h2.neg.sup (h2.inf (hF bad hb Yt b))
    refine ⟨hcut, ?_⟩
    unfold caseMean
    have hk : ∀ k : ℕ, caseIntegral R C V q (truncateCases (k : ℝ) F) = _ := fun k =>
      caseIntegral_eq_sum_integral_prod (hcut k (Nat.cast_nonneg k))
    simp only [hk]
    rw [caseIntegral_eq_sum_integral_prod hF]
    refine Tendsto.div_const ?_ _
    refine tendsto_finsetSum _ fun bad hb => tendsto_finsetSum _ fun Yt _ => tendsto_finsetSum _ fun b _ => ?_
    refine tendsto_integral_of_dominated_convergence
      (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
        |caseTerm R C V q F bad Yt b p.1 p.2|)
      (fun k => (hcut k (Nat.cast_nonneg k) bad hb Yt b).aestronglyMeasurable) (hF bad hb Yt b).abs ?_ ?_
    · intro k
      refine Filter.Eventually.of_forall fun p => ?_
      rw [Real.norm_eq_abs]
      unfold caseTerm
      split_ifs with hc
      · rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right (abs_clamp_le _ _ (Nat.cast_nonneg k)) (abs_nonneg _)
      · simp
    · refine Filter.Eventually.of_forall fun p => ?_
      unfold caseTerm
      split_ifs with hc
      · refine tendsto_const_nhds.congr' ?_
        obtain ⟨N, hN⟩ := exists_nat_ge |F (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b|
        filter_upwards [Filter.eventually_ge_atTop N] with k hk
        have hk' : |F (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b| ≤ (k : ℝ) :=
          hN.trans (Nat.cast_le.2 hk)
        have h3 := abs_le.1 hk'
        unfold truncateCases
        rw [min_eq_right h3.2, max_eq_right h3.1]
      · exact tendsto_const_nhds
end YangMills.Construction.FreeEnergies
end
