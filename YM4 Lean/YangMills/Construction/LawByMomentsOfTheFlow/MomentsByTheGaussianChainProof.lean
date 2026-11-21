import YangMills.Construction.LawByMomentsOfTheFlow.GoodStatesAreLikely
import YangMills.Construction.LawByMomentsOfTheFlow.LeadingMomentsOfTheResponses
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsByTheGaussianChain
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsOfTheResponsesInALimitFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps StepSettings WeightedResponses ResponseInTheExpansion BlockAverages LumpContours
section Borel
variable {Ω₀ : Type} [MeasurableSpace Ω₀]
private theorem measurable_curvature {n : ℕ} {V : Ω₀ → TorusField n} (hV : Measurable V) (x : TorusSite n)
    (μ ν : Fin 4) : Measurable fun a => TorusFields.curvature (V a) x μ ν := by apply _root_.YangMills.SharedProofs.p35643 <;> assumption
private theorem measurable_toColourForm_cutoffCoords
    (hlog : MeasurableQuaternion (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])))
    (ℓ : TorusLumps.StepParameters) {n : ℕ} [NeZero n] (o : TorusSite n) (m : ℕ) :
    Measurable fun W : TorusField n => (toColourForm (cutoffCoords ℓ W o m) : ColourForm n) := by apply _root_.YangMills.SharedProofs.p107287 <;> assumption
private theorem measurable_boxCurvature {n : ℕ} [NeZero n] (o : TorusSite n) (r : ℝ) :
    Measurable fun W : TorusField n => boxCurvature o r W := by apply _root_.YangMills.DeltaSharedProofs.p12736 <;> assumption
end Borel
section Abstract
private theorem abs_integral_sub_le_of_condExp {Ω : Type} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ) {f c h E : Ω → ℝ} {G : Set Ω} (hG : MeasurableSet G) {M a b : ℝ}
    (hf : Measurable f) (hfM : ∀ w, |f w| ≤ M) (hc : μ[f|m] =ᵐ[μ] c) (hh : Integrable h μ)
    (hoff : ∀ w, w ∉ G → h w = 0) (hon : ∀ᵐ w ∂μ, w ∈ G → |c w - h w| ≤ E w) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hE : ∫⁻ w, G.indicator (fun w => ENNReal.ofReal (E w)) w ∂μ ≤ ENNReal.ofReal a)
    (hGc : ENNReal.ofReal M * μ Gᶜ ≤ ENNReal.ofReal b) :
    |∫ w, f w ∂μ - ∫ w, h w ∂μ| ≤ a + b := by
  have e1 : ∫ w, f w ∂μ = ∫ w, c w ∂μ := by
    rw [← integral_condExp hm]
    exact integral_congr_ae hc
  have hcI : Integrable c μ := integrable_condExp.congr hc
  rw [e1, ← integral_sub hcI hh]
  have hb2 : ∀ᵐ w ∂μ, |c w| ≤ M := by
    have h0 : ∀ᵐ w ∂μ, |f w| ≤ (M.toNNReal : ℝ) := ae_of_all _ fun w =>
      (hfM w).trans (Real.le_coe_toNNReal M)
    have h1 := ae_bdd_condExp_of_ae_bdd (m := m) h0
    filter_upwards [h1, hc] with w hw hcw
    rw [← hcw]
    refine hw.trans ?_
    rw [Real.coe_toNNReal _ ((abs_nonneg _).trans (hfM w))]
  have hle : ∫⁻ w, ENNReal.ofReal ‖c w - h w‖ ∂μ ≤
      ∫⁻ w, (G.indicator (fun w => ENNReal.ofReal (E w)) w + Gᶜ.indicator (fun _ => ENNReal.ofReal M) w) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hon, hb2] with w hw hcw
    by_cases hwG : w ∈ G
    · rw [Set.indicator_of_mem hwG, Set.indicator_of_notMem (by simpa using hwG), add_zero]
      exact ENNReal.ofReal_le_ofReal (hw hwG)
    · rw [Set.indicator_of_notMem hwG, Set.indicator_of_mem (by simpa using hwG), zero_add, hoff w hwG, sub_zero]
      exact ENNReal.ofReal_le_ofReal hcw
  rw [lintegral_add_right _ (measurable_const.indicator hG.compl), lintegral_indicator_const hG.compl] at hle
  have hfin : ∫⁻ w, ENNReal.ofReal ‖c w - h w‖ ∂μ ≤ ENNReal.ofReal (a + b) := by
    rw [ENNReal.ofReal_add ha hb]
    exact hle.trans (add_le_add hE hGc)
  have hn := norm_integral_le_lintegral_norm (μ := μ) (fun w => c w - h w)
  rw [Real.norm_eq_abs] at hn
  exact hn.trans (ENNReal.toReal_le_of_le_ofReal (add_nonneg ha hb) hfin)
end Abstract
namespace MomentPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem measurable_formProductMean (d n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)) :
    Measurable (S.formProductMean d n B) := by apply _root_.YangMills.SharedProofs.p14233 <;> assumption
private def goodSet (u n : ℕ) [NeZero n] : Set (MarkedSample Λ.stepParams u n) :=
  {w | S.IsGoodConfig u n (S.state u n w).1 (S.state u n w).2.1}
private theorem measurableSet_sigma_fst_eq {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
private theorem measurable_localCurvature (u n : ℕ) [NeZero n] : Measurable (S.localCurvature u n) :=
  measurable_boxCurvature _ _
private theorem measurableSet_goodSet (u n : ℕ) [NeZero n] (hq : Measurable (stageState S.tower u n)) :
    MeasurableSet (S.goodSet u n) := by apply _root_.YangMills.DeltaSharedProofs.p501697 <;> assumption
private def cutoffMean (u d n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)) (w : MarkedSample Λ.stepParams u n) : ℝ :=
  S.formProductMean d n B (S.cutoffColourForm u n (S.state u n w).1)
private def stageMean (u d n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)) : ℝ :=
  ∫ w, (S.goodSet u n).indicator (S.cutoffMean u d n B) w ∂(S.law u n)
private theorem measurable_cutoffColourForm
    (hlog : MeasurableQuaternion (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])))
    (u n : ℕ) [NeZero n] : Measurable (S.cutoffColourForm u n) :=
  measurable_toColourForm_cutoffCoords hlog Λ.stepParams (S.originSite u n) S.rangeSq
private theorem measurable_cutoffMean
    (hlog : MeasurableQuaternion (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])))
    (u d n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)) (hq : Measurable (stageState S.tower u n)) :
    Measurable (S.cutoffMean u d n B) :=
  (S.measurable_formProductMean d n B).comp ((S.measurable_cutoffColourForm hlog _ n).comp (measurable_fst.comp hq))
private theorem distanceWeight_le_one (hrt : 0 ≤ Λ.stepParams.rt) (u n : ℕ) [NeZero n] (p : TorusPlaquette n) :
    S.distanceWeight u n p ≤ 1 := by apply _root_.YangMills.SharedProofs.p40065 <;> assumption
end MomentPoint
section Norms
private theorem weightedCurvatureNorm_le_eLpNorm {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ} [NeZero n]
    {ω : TorusPlaquette n → ℝ} (hω : ∀ p, ω p ≤ 1) (q : ENNReal) (X : Ω → ColourForm n) (g : Ω → ℝ)
    (hg : ∀ w (p : OrientedPlaquette n), curlNorm (X w) p.1 ≤ g w) :
    weightedCurvatureNorm μ ω q X ≤ eLpNorm g q μ := by apply _root_.YangMills.SharedProofs.p17835 <;> assumption
end Norms
section Tower
variable {ℓ : TorusLumps.StepParameters}
private theorem stageState_fst (T : StageTower ℓ) (s n : ℕ) [NeZero n] (w : MarkedSample ℓ s n) :
    (stageState T s n w).1 = topField ℓ s n w := by apply _root_.YangMills.SharedProofs.p2480 <;> assumption
private def liftCases (T : StageTower ℓ) (s n : ℕ) [NeZero n]
    (F : TorusField n → CaseFunction (T.stage s).toStepSetup n) (u : MarkedSample ℓ (s + 1) n) : ℝ :=
  F u.2.2.1 (topField ℓ s (n * ℓ.side) u.1) (stageState T s (n * ℓ.side) u.1).2.1
    (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1
private theorem coarseStateWeight_pos_ae (T : StageTower ℓ) (β : ℝ) (s n : ℕ) [NeZero n]
    [IsProbabilityMeasure (markedSampleLaw T β (s + 1) n)]
    (hm : stageSigma T (s + 1) n ≤ markedSampleMeasurableSpace ℓ (s + 1) n)
    (hw : ∀ (C : Finset (TorusSite n)) (V : TorusField n) W Yt ωt bad b,
      0 ≤ stepWeight (T.stage s).toStepSetup C V W Yt ωt bad b)
    (h1 : (markedSampleLaw T β (s + 1) n)[liftCases T s n (fun _ _ _ _ _ _ => 1) | stageSigma T (s + 1) n]
      =ᵐ[markedSampleLaw T β (s + 1) n]
      fun u => caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
        (stageState T (s + 1) n u).2 (fun _ _ _ _ _ => 1)) :
    ∀ᵐ u ∂(markedSampleLaw T β (s + 1) n),
      0 < coarseStateWeight (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
        (stageState T (s + 1) n u).2 := by
  have e1 : liftCases T s n (fun _ _ _ _ _ _ => 1) = fun _ => (1 : ℝ) := rfl
  rw [e1] at h1
  filter_upwards [h1] with u hu
  rw [condExp_const hm (1 : ℝ)] at hu
  have hnn : 0 ≤ caseIntegral (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
      (stageState T (s + 1) n u).2 (fun _ _ _ _ _ => 1) := by
    unfold caseIntegral
    refine Finset.sum_nonneg fun bad _ => Finset.sum_nonneg fun Yt _ => Finset.sum_nonneg fun b _ => ?_
    refine integral_nonneg fun W => integral_nonneg fun ν => ?_
    unfold caseTerm
    split_ifs
    · rw [one_mul]
      exact hw _ _ _ _ _ _ _
    · exact le_rfl
  have hu' : (1 : ℝ) = caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
      (stageState T (s + 1) n u).2 (fun _ _ _ _ _ => 1) := hu
  unfold caseMean at hu'
  have hne : coarseStateWeight (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
      (stageState T (s + 1) n u).2 ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hu'
    exact one_ne_zero hu'
  have he := (div_eq_one_iff_eq hne).1 hu'.symm
  rw [he] at hnn
  exact lt_of_le_of_ne hnn (Ne.symm hne)
end Tower
namespace MomentPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private def cutoffCaseFn (u d n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)) :
    CaseFunction (S.tower.stage u).toStepSetup n :=
  fun W Yt _ _ _ => open Classical in if S.IsGoodConfig u (n * Λ.stepParams.side) W Yt then
    S.formProductMean d (n * Λ.stepParams.side) B (S.cutoffColourForm u (n * Λ.stepParams.side) W) else 0
private theorem liftCases_cutoffCaseFn (u d n : ℕ) [NeZero n] (B : Finset (Fin Λ.k))
    (z : MarkedSample Λ.stepParams (u + 1) n) :
    liftCases S.tower u n (fun _ => S.cutoffCaseFn u d n B) z =
      (S.goodSet u (n * Λ.stepParams.side)).indicator (S.cutoffMean u d (n * Λ.stepParams.side) B) z.1 := by
  classical
  unfold liftCases cutoffCaseFn goodSet cutoffMean
  simp only [Set.indicator_apply, Set.mem_setOf_eq, MomentPoint.state]
  rw [stageState_fst]
private theorem abs_stageMean_sub_succ_le
    (hlog : MeasurableQuaternion (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])))
    (u d n : ℕ) [NeZero n] (B : Finset (Fin Λ.k))
    [hP : IsProbabilityMeasure (S.law (u + 1) n)]
    (hmap : (S.law (u + 1) n).map (fun z : MarkedSample Λ.stepParams (u + 1) n => z.1) =
      S.law u (n * Λ.stepParams.side))
    (hq0 : Measurable (stageState S.tower u (n * Λ.stepParams.side)))
    (hq1 : Measurable (stageState S.tower (u + 1) n))
    (hMG : ∀ F : TorusField n → CaseFunction (S.tower.stage u).toStepSetup n, Measurable (liftCases S.tower u n F) →
      (∃ C : ℝ, ∀ z, |liftCases S.tower u n F z| ≤ C) →
      (S.law (u + 1) n)[liftCases S.tower u n F | stageSigma S.tower (u + 1) n] =ᵐ[S.law (u + 1) n]
        fun z => caseMean (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup z.2.2.1) z.2.2.1
          (stageState S.tower (u + 1) n z).2 (F z.2.2.1))
    (hw : ∀ (C : Finset (TorusSite n)) (V : TorusField n) W Yt ωt bad b,
      0 ≤ stepWeight (S.tower.stage u).toStepSetup C V W Yt ωt bad b)
    {M Co a b : ℝ}
    (hM0 : ∀ w, |(S.goodSet u (n * Λ.stepParams.side)).indicator (S.cutoffMean u d (n * Λ.stepParams.side) B) w| ≤ M)
    (hM1 : ∀ w, |(S.goodSet (u + 1) n).indicator (S.cutoffMean (u + 1) (d + 1) n B) w| ≤ M)
    (hOne : ∀ (V : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → (S.tower.stage (u + 1)).labels.Ω),
      S.IsGoodConfig (u + 1) n V Y →
      0 < coarseStateWeight (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup V) V ⟨Y, ω⟩ →
      |caseMean (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup V) V ⟨Y, ω⟩
          (S.cutoffCaseFn u d n B) -
        S.formProductMean (d + 1) n B (S.cutoffColourForm (u + 1) n V)| ≤
      Co * (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature (u + 1) n V) ^ (2 * B.card + 1))
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hE : ∫⁻ w, (S.goodSet (u + 1) n).indicator (fun w => ENNReal.ofReal
      (Co * (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature (u + 1) n (S.state (u + 1) n w).1) ^
        (2 * B.card + 1))) w ∂(S.law (u + 1) n) ≤ ENNReal.ofReal a)
    (hGc : ENNReal.ofReal M * (S.law (u + 1) n) (S.goodSet (u + 1) n)ᶜ ≤ ENNReal.ofReal b) :
    |S.stageMean u d (n * Λ.stepParams.side) B - S.stageMean (u + 1) (d + 1) n B| ≤ a + b := by
  have hm : stageSigma S.tower (u + 1) n ≤ markedSampleMeasurableSpace Λ.stepParams (u + 1) n := hq1.comap_le
  have hfst : Measurable fun z : MarkedSample Λ.stepParams (u + 1) n => z.1 := by
    let _ := markedSampleMeasurableSpace Λ.stepParams u (n * Λ.stepParams.side)
    exact measurable_fst
  have hf0 : Measurable ((S.goodSet u (n * Λ.stepParams.side)).indicator
      (S.cutoffMean u d (n * Λ.stepParams.side) B)) :=
    (S.measurable_cutoffMean hlog u d _ B hq0).indicator (S.measurableSet_goodSet _ _ hq0)
  have hf1 : Measurable ((S.goodSet (u + 1) n).indicator (S.cutoffMean (u + 1) (d + 1) n B)) :=
    (S.measurable_cutoffMean hlog (u + 1) (d + 1) _ B hq1).indicator (S.measurableSet_goodSet _ _ hq1)
  have el : liftCases S.tower u n (fun _ => S.cutoffCaseFn u d n B) =
      fun z => (S.goodSet u (n * Λ.stepParams.side)).indicator (S.cutoffMean u d (n * Λ.stepParams.side) B) z.1 :=
    funext (S.liftCases_cutoffCaseFn u d n B)
  have hlm : Measurable (liftCases S.tower u n (fun _ => S.cutoffCaseFn u d n B)) := by
    rw [el]
    exact hf0.comp hfst
  have hlb : ∀ z, |liftCases S.tower u n (fun _ => S.cutoffCaseFn u d n B) z| ≤ M := fun z => by
    rw [el]
    exact hM0 _
  have hc := hMG _ hlm ⟨M, hlb⟩
  have hone : liftCases S.tower u n (fun _ _ _ _ _ _ => 1) = fun _ => (1 : ℝ) := rfl
  have h1 := hMG (fun _ _ _ _ _ _ => 1) (by rw [hone]; exact measurable_const) ⟨1, fun z => by rw [hone]; simp⟩
  have hP' : IsProbabilityMeasure (markedSampleLaw S.tower S.β (u + 1) n) := hP
  have hpos : ∀ᵐ z ∂(S.law (u + 1) n), 0 < coarseStateWeight (S.tower.stage u).toStepSetup
      (hotCoreSites (S.tower.stage u).toStepSetup z.2.2.1) z.2.2.1 (stageState S.tower (u + 1) n z).2 :=
    coarseStateWeight_pos_ae S.tower S.β u n hm hw h1
  have e0 : S.stageMean u d (n * Λ.stepParams.side) B =
      ∫ w, liftCases S.tower u n (fun _ => S.cutoffCaseFn u d n B) w ∂(S.law (u + 1) n) := by
    unfold stageMean
    rw [← hmap, integral_map hfst.aemeasurable hf0.aestronglyMeasurable, el]
  have hint : Integrable ((S.goodSet (u + 1) n).indicator (S.cutoffMean (u + 1) (d + 1) n B)) (S.law (u + 1) n) :=
    Integrable.of_bound hf1.aestronglyMeasurable M (ae_of_all _ fun w => by simpa [Real.norm_eq_abs] using hM1 w)
  have e1 : S.stageMean (u + 1) (d + 1) n B =
      ∫ w, (S.goodSet (u + 1) n).indicator (S.cutoffMean (u + 1) (d + 1) n B) w ∂(S.law (u + 1) n) := rfl
  rw [e0, e1]
  refine abs_integral_sub_le_of_condExp hm (S.measurableSet_goodSet _ _ hq1) hlm hlb hc hint
    (fun w hw' => Set.indicator_of_notMem hw' _) ?_ ha hb hE hGc
  filter_upwards [hpos] with w hw' hg
  rw [Set.indicator_of_mem hg]
  exact hOne w.2.2.1 (stageState S.tower (u + 1) n w).2.1 (stageState S.tower (u + 1) n w).2.2 hg hw'
end MomentPoint
section Numbers
private theorem one_add_mul_le_rpow_quarter {x v : ℝ} (hx : 1 ≤ x) (hv0 : 0 ≤ v) (hv : v ≤ x ^ (-(1 / 4) : ℝ)) :
    1 + 120 * x ^ ((1 : ℝ) / 2) * v ≤ 121 * x ^ ((1 : ℝ) / 4) := by apply _root_.YangMills.SharedProofs.p117073 <;> assumption
private theorem pow_le_rpow_four {x : ℝ} (hx : 1 ≤ x) {j : ℕ} (hj : j ≤ 16) :
    (121 * x ^ ((1 : ℝ) / 4)) ^ j ≤ 121 ^ 16 * x ^ 4 := by apply _root_.YangMills.SharedProofs.p9016 <;> assumption
private theorem ofReal_mul_eLpNorm_le {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {Q : ℕ} (hQ : 0 < Q) {s c : ℝ}
    (hs : 0 ≤ s) (hc : 0 ≤ c) (g Y : Ω → ℝ) (G : Set Ω) (hY : ∀ w, 0 ≤ Y w)
    (hg : ∀ w, s * |g w| ≤ 60 * G.indicator Y w)
    (hm : ∫⁻ w, G.indicator (fun w => ENNReal.ofReal (Y w ^ Q)) w ∂μ ≤ ENNReal.ofReal c) :
    ENNReal.ofReal s * eLpNorm g (Q : ENNReal) μ ≤ ENNReal.ofReal (60 * (1 + c)) := by
  have hQ0 : (Q : ENNReal) ≠ 0 := by exact_mod_cast hQ.ne'
  have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hQ0 (ENNReal.natCast_ne_top Q), ENNReal.toReal_natCast]
  have e1 : ENNReal.ofReal s = (ENNReal.ofReal s ^ (Q : ℝ)) ^ (1 / (Q : ℝ)) := by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]
  rw [e1, ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  suffices hA : ENNReal.ofReal s ^ (Q : ℝ) * ∫⁻ w, ‖g w‖ₑ ^ (Q : ℝ) ∂μ ≤ ENNReal.ofReal (60 * (1 + c)) ^ (Q : ℝ) by
    refine (ENNReal.rpow_le_rpow hA (by positivity)).trans_eq ?_
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]
  rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top)]
  have hpt : ∀ w, ENNReal.ofReal s ^ (Q : ℝ) * ‖g w‖ₑ ^ (Q : ℝ) ≤
      ENNReal.ofReal (60 ^ Q) * G.indicator (fun w => ENNReal.ofReal (Y w ^ Q)) w := by
    intro w
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hq.le, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hs]
    have h1 := ENNReal.ofReal_le_ofReal (hg w)
    refine (ENNReal.rpow_le_rpow h1 hq.le).trans ?_
    rw [ENNReal.rpow_natCast]
    by_cases hw : w ∈ G
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, ← ENNReal.ofReal_pow (by have := hY w; positivity),
        mul_pow, ENNReal.ofReal_mul (by positivity)]
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
      simp [hQ.ne']
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul_right hm _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity), ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : (1 : ℝ) ≤ 1 + c := by linarith
  calc c ≤ 1 + c := by linarith
    _ ≤ (1 + c) ^ Q := le_self_pow₀ h1 hQ.ne'
end Numbers
namespace MomentPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem localCurvature_nonneg (u n : ℕ) [NeZero n] (W : TorusField n) : 0 ≤ S.localCurvature u n W :=
  Real.iSup_nonneg fun _ => norm_nonneg _
private theorem abs_formProductMean_le {d u n : ℕ} [NeZero n] {B : Finset (Fin Λ.k)} {C0 : ℝ}
    (hI : ∀ (A A' : Unit → ColourForm n), Measurable A → Measurable A' →
      ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w)| ∂(Measure.dirac ()) ≤
        ENNReal.ofReal (C0 * (S.range : ℝ) ^ (4 * B.card)) * (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm (Measure.dirac ()) (S.distanceWeight u n) (8 * (Λ.k : ENNReal)) A +
            weightedCurvatureNorm (Measure.dirac ()) (S.distanceWeight u n) (8 * (Λ.k : ENNReal)) A')) ^
          (2 * B.card))
    (hrt : 0 ≤ Λ.stepParams.rt) (X : ColourForm n) {v : ℝ} (hv : 0 ≤ v)
    (hX : ∀ p : OrientedPlaquette n, curlNorm X p.1 ≤ 60 * v) (hx : 0 ≤ S.scaleCoupling) :
    |S.formProductMean d n B X| ≤
      |C0| * (S.range : ℝ) ^ (4 * B.card) * (1 + 120 * S.scaleCoupling ^ ((1 : ℝ) / 2) * v) ^ (2 * B.card) := by
  have h := hI (fun _ => X) (fun _ => X) measurable_const measurable_const
  rw [lintegral_dirac] at h
  have hq0 : (8 * (Λ.k : ENNReal)) ≠ 0 := by
    have : (Λ.k : ENNReal) ≠ 0 := by exact_mod_cast NeZero.ne Λ.k
    simpa using this
  have hc : weightedCurvatureNorm (Measure.dirac ()) (S.distanceWeight u n) (8 * (Λ.k : ENNReal))
      (fun _ : Unit => X) ≤ ENNReal.ofReal (60 * v) := by
    refine (weightedCurvatureNorm_le_eLpNorm _ (fun p => S.distanceWeight_le_one hrt u n p) _ _ (fun _ => 60 * v)
      (fun _ p => hX p)).trans ?_
    rw [eLpNorm_const _ hq0 (by simp)]
    simp [Real.enorm_of_nonneg (show (0 : ℝ) ≤ 60 * v by positivity)]
  have hs : 0 ≤ S.scaleCoupling ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hx _
  have h2 : (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
      (weightedCurvatureNorm (Measure.dirac ()) (S.distanceWeight u n) (8 * (Λ.k : ENNReal)) (fun _ : Unit => X) +
        weightedCurvatureNorm (Measure.dirac ()) (S.distanceWeight u n) (8 * (Λ.k : ENNReal))
          (fun _ : Unit => X))) ≤
      ENNReal.ofReal (1 + 120 * S.scaleCoupling ^ ((1 : ℝ) / 2) * v) := by
    have e : (1 + 120 * S.scaleCoupling ^ ((1 : ℝ) / 2) * v) =
        1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * (60 * v + 60 * v) := by ring
    rw [e, ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_mul hs,
      ENNReal.ofReal_add (by positivity) (by positivity)]
    gcongr
  have h3 : ENNReal.ofReal |S.formProductMean d n B X| ≤ ENNReal.ofReal
      (|C0| * (S.range : ℝ) ^ (4 * B.card) * (1 + 120 * S.scaleCoupling ^ ((1 : ℝ) / 2) * v) ^ (2 * B.card)) := by
    refine h.trans ?_
    have hY0 : 0 ≤ 1 + 120 * S.scaleCoupling ^ ((1 : ℝ) / 2) * v := by positivity
    have e : ENNReal.ofReal (|C0| * (S.range : ℝ) ^ (4 * B.card) *
          (1 + 120 * S.scaleCoupling ^ ((1 : ℝ) / 2) * v) ^ (2 * B.card)) =
        ENNReal.ofReal (|C0| * (S.range : ℝ) ^ (4 * B.card)) *
          ENNReal.ofReal (1 + 120 * S.scaleCoupling ^ ((1 : ℝ) / 2) * v) ^ (2 * B.card) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hY0]
    rw [e]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (pow_le_pow_left' h2 _)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
private theorem abs_indicator_cutoffMean_le {d u n : ℕ} [NeZero n] {B : Finset (Fin Λ.k)} {C0 : ℝ}
    (hI : ∀ (A A' : Unit → ColourForm n), Measurable A → Measurable A' →
      ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w)| ∂(Measure.dirac ()) ≤
        ENNReal.ofReal (C0 * (S.range : ℝ) ^ (4 * B.card)) * (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm (Measure.dirac ()) (S.distanceWeight u n) (8 * (Λ.k : ENNReal)) A +
            weightedCurvatureNorm (Measure.dirac ()) (S.distanceWeight u n) (8 * (Λ.k : ENNReal)) A')) ^
          (2 * B.card))
    (hrt : 0 ≤ Λ.stepParams.rt) (hx : 1 ≤ S.scaleCoupling) (hB : B.card ≤ 8)
    (hcut : ∀ (W : TorusField n) (Y : Finset (TorusSite n)), S.IsGoodConfig u n W Y → ∀ p : OrientedPlaquette n,
      curlNorm (S.cutoffColourForm u n W) p.1 ≤ 60 * S.localCurvature u n W) (w : MarkedSample Λ.stepParams u n) :
    |(S.goodSet u n).indicator (S.cutoffMean u d n B) w| ≤
      |C0| * (S.range : ℝ) ^ (4 * B.card) * (121 ^ 16 * S.scaleCoupling ^ 4) := by
  have hnn : 0 ≤ |C0| * (S.range : ℝ) ^ (4 * B.card) * (121 ^ 16 * S.scaleCoupling ^ 4) := by
    have : 0 ≤ S.scaleCoupling := by linarith
    positivity
  by_cases hg : w ∈ S.goodSet u n
  · rw [Set.indicator_of_mem hg]
    have h1 := S.abs_formProductMean_le hI hrt (S.cutoffColourForm u n (S.state u n w).1)
      (S.localCurvature_nonneg u n _) (hcut _ _ hg) (by linarith)
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h2 := one_add_mul_le_rpow_quarter hx (S.localCurvature_nonneg u n (S.state u n w).1) hg.curvature_le
    have h3 : 0 ≤ 1 + 120 * S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature u n (S.state u n w).1 := by
      have := S.localCurvature_nonneg u n (S.state u n w).1
      have : 0 ≤ S.scaleCoupling ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
      positivity
    exact (pow_le_pow_left₀ h3 h2 _).trans (pow_le_rpow_four hx (by omega))
  · rw [Set.indicator_of_notMem hg, abs_zero]
    exact hnn
private theorem curlNorm_zero {n : ℕ} [NeZero n] (p : TorusPlaquette n) : curlNorm (0 : ColourForm n) p = 0 := by
  unfold curlNorm WeightedResponses.curl
  simp
private theorem abs_stageMean_sub_formProductMean_zero_le
    (hlog : MeasurableQuaternion (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])))
    (u d n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)) [hP : IsProbabilityMeasure (S.law u n)]
    (hq : Measurable (stageState S.tower u n)) {c2 c b M : ℝ}
    (hII : ∀ (A A' : MarkedSample Λ.stepParams u n → ColourForm n), Measurable A → Measurable A' →
      ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w) - S.formProductMean d n B 0| ∂(S.law u n) ≤
        ENNReal.ofReal c2 * (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm (S.law u n) (S.distanceWeight u n) (8 * (Λ.k : ENNReal)) A +
            weightedCurvatureNorm (S.law u n) (S.distanceWeight u n) (8 * (Λ.k : ENNReal)) A')) ^ (2 * B.card))
    (hrt : 0 ≤ Λ.stepParams.rt) (hx : 1 ≤ S.scaleCoupling) (hc2 : 0 ≤ c2) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hcut : ∀ (W : TorusField n) (Y : Finset (TorusSite n)), S.IsGoodConfig u n W Y → ∀ p : OrientedPlaquette n,
      curlNorm (S.cutoffColourForm u n W) p.1 ≤ 60 * S.localCurvature u n W)
    (hM : ∀ w, |(S.goodSet u n).indicator (S.cutoffMean u d n B) w| ≤ M)
    (hmom : ∫⁻ w, (S.goodSet u n).indicator (fun w => ENNReal.ofReal
      ((1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature u n (S.state u n w).1) ^ (8 * Λ.k))) w
        ∂(S.law u n) ≤ ENNReal.ofReal c)
    (hGc : ENNReal.ofReal |S.formProductMean d n B 0| * (S.law u n) (S.goodSet u n)ᶜ ≤ ENNReal.ofReal b) :
    |S.stageMean u d n B - S.formProductMean d n B 0| ≤ c2 * (1 + 120 * (1 + c)) ^ (2 * B.card) + b := by
  classical
  have hG := S.measurableSet_goodSet u n hq
  have hs : 0 ≤ S.scaleCoupling ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  let A : MarkedSample Λ.stepParams u n → ColourForm n :=
    (S.goodSet u n).indicator fun w => S.cutoffColourForm u n (S.state u n w).1
  have hA : Measurable A := ((S.measurable_cutoffColourForm hlog u n).comp (measurable_fst.comp hq)).indicator hG
  let g : MarkedSample Λ.stepParams u n → ℝ :=
    (S.goodSet u n).indicator fun w => 60 * S.localCurvature u n (S.state u n w).1
  have hcg : ∀ w (p : OrientedPlaquette n), curlNorm (A w) p.1 ≤ g w := by
    intro w p
    by_cases hw : w ∈ S.goodSet u n
    · simp only [A, g, Set.indicator_of_mem hw]
      exact hcut _ _ hw p
    · simp only [A, g, Set.indicator_of_notMem hw]
      rw [curlNorm_zero]
  have hcn := weightedCurvatureNorm_le_eLpNorm (S.law u n) (fun p => S.distanceWeight_le_one hrt u n p)
    (8 * (Λ.k : ENNReal)) A g hcg
  have hcoe : ((8 * Λ.k : ℕ) : ENNReal) = 8 * (Λ.k : ENNReal) := by push_cast; rfl
  have hT : ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) * eLpNorm g (8 * (Λ.k : ENNReal)) (S.law u n) ≤
      ENNReal.ofReal (60 * (1 + c)) := by
    rw [← hcoe]
    refine ofReal_mul_eLpNorm_le (S.law u n) (Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero (NeZero.ne Λ.k))) hs hc g
      (fun w => 1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature u n (S.state u n w).1) (S.goodSet u n)
      (fun w => by have := S.localCurvature_nonneg u n (S.state u n w).1; positivity) (fun w => ?_) hmom
    have hv := S.localCurvature_nonneg u n (S.state u n w).1
    by_cases hw : w ∈ S.goodSet u n
    · simp only [g, Set.indicator_of_mem hw]
      rw [abs_of_nonneg (by positivity)]
      nlinarith
    · simp only [g, Set.indicator_of_notMem hw]
      simp
  have hy : (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
      (weightedCurvatureNorm (S.law u n) (S.distanceWeight u n) (8 * (Λ.k : ENNReal)) A +
        weightedCurvatureNorm (S.law u n) (S.distanceWeight u n) (8 * (Λ.k : ENNReal)) A)) ≤
      ENNReal.ofReal (1 + 120 * (1 + c)) := by
    have h1 : ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
        weightedCurvatureNorm (S.law u n) (S.distanceWeight u n) (8 * (Λ.k : ENNReal)) A ≤
        ENNReal.ofReal (60 * (1 + c)) := (mul_le_mul_right hcn _).trans hT
    have e : (1 + 120 * (1 + c)) = 1 + (60 * (1 + c) + 60 * (1 + c)) := by ring
    rw [mul_add, e, ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_add (by positivity) (by positivity)]
    gcongr
  have h2 : ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w) - S.formProductMean d n B 0| ∂(S.law u n) ≤
      ENNReal.ofReal (c2 * (1 + 120 * (1 + c)) ^ (2 * B.card)) := by
    refine (hII A A hA hA).trans ?_
    rw [ENNReal.ofReal_mul hc2, ENNReal.ofReal_pow (by positivity)]
    exact mul_le_mul_right (pow_le_pow_left' hy _) _
  have hf : Measurable ((S.goodSet u n).indicator (S.cutoffMean u d n B)) :=
    (S.measurable_cutoffMean hlog u d n B hq).indicator hG
  have hint : Integrable ((S.goodSet u n).indicator (S.cutoffMean u d n B)) (S.law u n) :=
    Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ fun w => by simpa [Real.norm_eq_abs] using hM w)
  have e0 : S.stageMean u d n B - S.formProductMean d n B 0 =
      ∫ w, ((S.goodSet u n).indicator (S.cutoffMean u d n B) w - S.formProductMean d n B 0) ∂(S.law u n) := by
    rw [integral_sub hint (integrable_const _), integral_const]
    simp [stageMean]
  have hpt : ∫⁻ w, ENNReal.ofReal ‖(S.goodSet u n).indicator (S.cutoffMean u d n B) w -
        S.formProductMean d n B 0‖ ∂(S.law u n) ≤
      ∫⁻ w, (ENNReal.ofReal |S.formProductMean d n B (A w) - S.formProductMean d n B 0| +
        (S.goodSet u n)ᶜ.indicator (fun _ => ENNReal.ofReal |S.formProductMean d n B 0|) w) ∂(S.law u n) := by
    refine lintegral_mono fun w => ?_
    by_cases hw : w ∈ S.goodSet u n
    · have hn : w ∉ (S.goodSet u n)ᶜ := by simpa using hw
      simp only [A, Set.indicator_of_mem hw, Set.indicator_of_notMem hn, add_zero, Real.norm_eq_abs]
      exact le_rfl
    · have hn : w ∈ (S.goodSet u n)ᶜ := by simpa using hw
      simp only [A, Set.indicator_of_notMem hw, Set.indicator_of_mem hn, zero_sub, Real.norm_eq_abs, abs_neg]
      exact le_add_self
  rw [lintegral_add_right _ (measurable_const.indicator hG.compl), lintegral_indicator_const hG.compl] at hpt
  have hfin : ∫⁻ w, ENNReal.ofReal ‖(S.goodSet u n).indicator (S.cutoffMean u d n B) w -
        S.formProductMean d n B 0‖ ∂(S.law u n) ≤
      ENNReal.ofReal (c2 * (1 + 120 * (1 + c)) ^ (2 * B.card) + b) := by
    rw [ENNReal.ofReal_add (by positivity) hb]
    exact hpt.trans (add_le_add h2 hGc)
  have hn := norm_integral_le_lintegral_norm (μ := S.law u n)
    (fun w => (S.goodSet u n).indicator (S.cutoffMean u d n B) w - S.formProductMean d n B 0)
  rw [Real.norm_eq_abs, ← e0] at hn
  exact hn.trans (ENNReal.toReal_le_of_le_ofReal (by positivity) hfin)
private theorem stageMean_congr_side {u d m m' : ℕ} [NeZero m] [NeZero m'] (B : Finset (Fin Λ.k)) (h : m = m') :
    S.stageMean u d m B = S.stageMean u d m' B := by
  subst h
  rfl
private theorem levelSide_succ {u : ℕ} (h : u + 1 ≤ S.data.windowLevel) :
    S.levelSide u = S.levelSide (u + 1) * Λ.stepParams.side := by apply _root_.YangMills.SharedProofs.p19020 <;> assumption
end MomentPoint
section Chain
private theorem abs_sub_le_of_steps {D : ℕ → ℝ} {N : ℕ} {e : ℝ} (h : ∀ d, d < N → |D d - D (d + 1)| ≤ e) :
    ∀ d, d ≤ N → |D 0 - D d| ≤ d * e := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    have h2 := h d (by omega)
    have h3 := abs_sub_le (D 0) (D d) (D (d + 1))
    push_cast
    linarith
end Chain
section Scaled
private theorem lintegral_indicator_ofReal_const_mul_le {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {G : Set Ω}
    {f : Ω → ℝ} {Co c : ℝ} (hCo : 0 ≤ Co)
    (h : ∫⁻ w, G.indicator (fun w => ENNReal.ofReal (f w)) w ∂μ ≤ ENNReal.ofReal c) :
    ∫⁻ w, G.indicator (fun w => ENNReal.ofReal (Co * f w)) w ∂μ ≤ ENNReal.ofReal (Co * c) := by
  have e : (fun w => G.indicator (fun w => ENNReal.ofReal (Co * f w)) w) =
      fun w => ENNReal.ofReal Co * G.indicator (fun w => ENNReal.ofReal (f w)) w := by
    funext w
    by_cases hw : w ∈ G
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, ENNReal.ofReal_mul hCo]
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, mul_zero]
  rw [e, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hCo]
  exact mul_le_mul_right h _
end Scaled
namespace MomentPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem abs_stageMean_sub_top_le
    (hlog : MeasurableQuaternion (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])))
    (hrt : 0 ≤ Λ.stepParams.rt) (hk : Λ.k ≤ 8) (hx : 1 ≤ S.scaleCoupling) (B : Finset (Fin Λ.k))
    (hBorel : ∀ (u n : ℕ) [NeZero n], Measurable (stageState S.tower u n))
    (hProb : ∀ (u n : ℕ) [NeZero n], IsProbabilityMeasure (S.law u n))
    (hMap : ∀ (u n : ℕ) [NeZero n],
      (S.law (u + 1) n).map (fun z : MarkedSample Λ.stepParams (u + 1) n => z.1) = S.law u (n * Λ.stepParams.side))
    (hK : S.lastSeparated + 2 * S.logIndex + 3 ≤ S.data.windowLevel)
    (hMG : ∀ u, u + 2 ≤ S.data.windowLevel →
      ∀ F : TorusField (S.levelSide (u + 1)) → CaseFunction (S.tower.stage u).toStepSetup (S.levelSide (u + 1)),
      Measurable (liftCases S.tower u (S.levelSide (u + 1)) F) →
      (∃ C : ℝ, ∀ z, |liftCases S.tower u (S.levelSide (u + 1)) F z| ≤ C) →
      (S.law (u + 1) (S.levelSide (u + 1)))[liftCases S.tower u (S.levelSide (u + 1)) F |
          stageSigma S.tower (u + 1) (S.levelSide (u + 1))]
        =ᵐ[S.law (u + 1) (S.levelSide (u + 1))]
        fun z => caseMean (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup z.2.2.1) z.2.2.1
          (stageState S.tower (u + 1) (S.levelSide (u + 1)) z).2 (F z.2.2.1))
    (hWt : ∀ u, u + 2 ≤ S.data.windowLevel →
      ∀ (C : Finset (TorusSite (S.levelSide (u + 1)))) (V : TorusField (S.levelSide (u + 1))) W Yt ωt bad b,
      0 ≤ stepWeight (S.tower.stage u).toStepSetup C V W Yt ωt bad b)
    (hcut : ∀ u, S.lastSeparated ≤ u → u ≤ S.lastSeparated + 2 * S.logIndex + 3 → ∀ (n : ℕ) [NeZero n],
      n = S.levelSide u → ∀ (W : TorusField n) (Y : Finset (TorusSite n)),
      S.IsGoodConfig u n W Y → ∀ p : OrientedPlaquette n,
        curlNorm (S.cutoffColourForm u n W) p.1 ≤ 60 * S.localCurvature u n W)
    {CM CO : ℝ} {CG : ℕ → ℝ}
    (hMeans : ∀ (d n : ℕ) [NeZero n], d ≤ S.logIndex + 1 → n = S.levelSide (S.lastSeparated + d) →
      ∀ (B : Finset (Fin Λ.k)) (Ω : Type) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (A A' : Ω → ColourForm n), Measurable A → Measurable A' →
      ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w)| ∂μ ≤
        ENNReal.ofReal (CM * (S.range : ℝ) ^ (4 * B.card)) * (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A +
            weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A')) ^
          (2 * B.card) ∧
      ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w) - S.formProductMean d n B 0| ∂μ ≤
        ENNReal.ofReal (CM * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(d : ℝ) / 4)) *
          (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A +
            weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A')) ^
          (2 * B.card))
    (hOne : ∀ (d n : ℕ) [NeZero n], d < S.logIndex → n = S.levelSide (S.lastSeparated + d + 1) →
      ∀ (V : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → (S.tower.stage (S.lastSeparated + d + 1)).labels.Ω),
      S.IsGoodConfig (S.lastSeparated + d + 1) n V Y →
      0 < coarseStateWeight (S.tower.stage (S.lastSeparated + d)).toStepSetup
        (hotCoreSites (S.tower.stage (S.lastSeparated + d)).toStepSetup V) V ⟨Y, ω⟩ → ∀ B : Finset (Fin Λ.k),
      |caseMean (S.tower.stage (S.lastSeparated + d)).toStepSetup
            (hotCoreSites (S.tower.stage (S.lastSeparated + d)).toStepSetup V) V ⟨Y, ω⟩ (fun W Yt _ _ _ =>
            open Classical in if S.IsGoodConfig (S.lastSeparated + d) (n * Λ.stepParams.side) W Yt then
              S.formProductMean d (n * Λ.stepParams.side) B
                (S.cutoffColourForm (S.lastSeparated + d) (n * Λ.stepParams.side) W) else 0) -
          S.formProductMean (d + 1) n B (S.cutoffColourForm (S.lastSeparated + d + 1) n V)| ≤
        CO * (S.range : ℝ) ^ (4 * B.card + 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ) *
          (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature (S.lastSeparated + d + 1) n V) ^ (2 * B.card + 1))
    (hGood : ∀ u, S.lastSeparated ≤ u → u ≤ S.lastSeparated + S.logIndex + 1 →
      (∀ N : ℕ, S.law u (S.levelSide u)
          {w | ¬ S.IsGoodConfig u (S.levelSide u) (S.state u (S.levelSide u) w).1 (S.state u (S.levelSide u) w).2.1} ≤
        ENNReal.ofReal (CG N * S.scaleCoupling ^ (-(N : ℝ)))) ∧
      ∀ k : ℕ, ∫⁻ w, Set.indicator
          {w | S.IsGoodConfig u (S.levelSide u) (S.state u (S.levelSide u) w).1 (S.state u (S.levelSide u) w).2.1}
          (fun w => ENNReal.ofReal ((1 + S.scaleCoupling ^ ((1 : ℝ) / 2) *
            S.localCurvature u (S.levelSide u) (S.state u (S.levelSide u) w).1) ^ k)) w
          ∂(S.law u (S.levelSide u)) ≤ ENNReal.ofReal (CG k * S.scaleCoupling ^ ((1 : ℝ) / 4000))) :
    |S.stageMean S.lastSeparated 0 (S.levelSide S.lastSeparated) B -
        S.formProductMean S.logIndex (S.levelSide (S.lastSeparated + S.logIndex)) B 0| ≤
      (S.logIndex : ℝ) * (|CO| * (S.range : ℝ) ^ (4 * B.card + 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ) *
          (|CG (2 * B.card + 1)| * S.scaleCoupling ^ ((1 : ℝ) / 4000)) +
        |CM| * (S.range : ℝ) ^ (4 * B.card) * (121 ^ 16 * S.scaleCoupling ^ 4) *
          (|CG 5| * S.scaleCoupling ^ (-((5 : ℕ) : ℝ)))) +
      (|CM| * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) *
          (1 + 120 * (1 + |CG (8 * Λ.k)| * S.scaleCoupling ^ ((1 : ℝ) / 4000))) ^ (2 * B.card) +
        |CM| * (S.range : ℝ) ^ (4 * B.card) * (|CG 1| * S.scaleCoupling ^ (-((1 : ℕ) : ℝ)))) := by
  have hx0 : 0 ≤ S.scaleCoupling := by linarith
  have hB : B.card ≤ 8 := by
    have := Finset.card_le_univ B
    simp only [Fintype.card_fin] at this
    omega
  have hr0 : (0 : ℝ) ≤ S.range := Nat.cast_nonneg _
  have hI : ∀ (u d n : ℕ) [NeZero n], u = S.lastSeparated + d → d ≤ S.logIndex + 1 → n = S.levelSide u →
      ∀ (A A' : Unit → ColourForm n), Measurable A → Measurable A' →
      ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w)| ∂(Measure.dirac ()) ≤
        ENNReal.ofReal (CM * (S.range : ℝ) ^ (4 * B.card)) * (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm (Measure.dirac ()) (S.distanceWeight u n) (8 * (Λ.k : ENNReal)) A +
            weightedCurvatureNorm (Measure.dirac ()) (S.distanceWeight u n) (8 * (Λ.k : ENNReal)) A')) ^
          (2 * B.card) := by
    intro u d n _ hu hd hn A A' hA hA'
    subst hu
    exact (hMeans d n hd hn B Unit (Measure.dirac ()) A A' hA hA').1
  have hMb : ∀ (u d n : ℕ) [NeZero n], u = S.lastSeparated + d → d ≤ S.logIndex + 1 → n = S.levelSide u → ∀ w,
      |(S.goodSet u n).indicator (S.cutoffMean u d n B) w| ≤
        |CM| * (S.range : ℝ) ^ (4 * B.card) * (121 ^ 16 * S.scaleCoupling ^ 4) := by
    intro u d n _ hu hd hn w
    exact S.abs_indicator_cutoffMean_le (hI u d n hu hd hn) hrt hx hB (hcut u (by omega) (by omega) n hn) w
  have hxε : 0 ≤ S.scaleCoupling ^ ((1 : ℝ) / 4000) := Real.rpow_nonneg hx0 _
  have hxh : 0 ≤ S.scaleCoupling ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hx0 _
  have hstep : ∀ d, d < S.logIndex →
      |S.stageMean (S.lastSeparated + d) d (S.levelSide (S.lastSeparated + d)) B -
        S.stageMean (S.lastSeparated + (d + 1)) (d + 1) (S.levelSide (S.lastSeparated + (d + 1))) B| ≤
      |CO| * (S.range : ℝ) ^ (4 * B.card + 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ) *
          (|CG (2 * B.card + 1)| * S.scaleCoupling ^ ((1 : ℝ) / 4000)) +
        |CM| * (S.range : ℝ) ^ (4 * B.card) * (121 ^ 16 * S.scaleCoupling ^ 4) *
          (|CG 5| * S.scaleCoupling ^ (-((5 : ℕ) : ℝ))) := by
    intro d hd
    have hu1 : S.lastSeparated + d + 1 ≤ S.data.windowLevel := by omega
    have hside := S.levelSide_succ hu1
    have hPr := hProb (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1))
    have hg := hGood (S.lastSeparated + d + 1) (by omega) (by omega)
    have hCo : 0 ≤ |CO| * (S.range : ℝ) ^ (4 * B.card + 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ) := by positivity
    have hE : ∫⁻ w, (S.goodSet (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1))).indicator
        (fun w => ENNReal.ofReal
        (|CO| * (S.range : ℝ) ^ (4 * B.card + 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ) *
          (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) *
          S.localCurvature (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1))
            (S.state (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1)) w).1) ^ (2 * B.card + 1))) w
          ∂(S.law (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1))) ≤
        ENNReal.ofReal (|CO| * (S.range : ℝ) ^ (4 * B.card + 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ) *
          (|CG (2 * B.card + 1)| * S.scaleCoupling ^ ((1 : ℝ) / 4000))) :=
      lintegral_indicator_ofReal_const_mul_le hCo ((hg.2 (2 * B.card + 1)).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_abs_self _) hxε)))
    have hGc : ENNReal.ofReal (|CM| * (S.range : ℝ) ^ (4 * B.card) * (121 ^ 16 * S.scaleCoupling ^ 4)) *
        (S.law (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1)))
          (S.goodSet (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1)))ᶜ ≤
        ENNReal.ofReal (|CM| * (S.range : ℝ) ^ (4 * B.card) * (121 ^ 16 * S.scaleCoupling ^ 4) *
          (|CG 5| * S.scaleCoupling ^ (-((5 : ℕ) : ℝ)))) := by
      rw [ENNReal.ofReal_mul (p := |CM| * (S.range : ℝ) ^ (4 * B.card) * (121 ^ 16 * S.scaleCoupling ^ 4))
        (by positivity)]
      refine mul_le_mul_right ((hg.1 5).trans (ENNReal.ofReal_le_ofReal ?_)) _
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hx0 _)
    have hO : ∀ (V : TorusField (S.levelSide (S.lastSeparated + d + 1)))
        (Y : Finset (TorusSite (S.levelSide (S.lastSeparated + d + 1))))
        (ω : Y → (S.tower.stage (S.lastSeparated + d + 1)).labels.Ω),
        S.IsGoodConfig (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1)) V Y →
        0 < coarseStateWeight (S.tower.stage (S.lastSeparated + d)).toStepSetup
          (hotCoreSites (S.tower.stage (S.lastSeparated + d)).toStepSetup V) V ⟨Y, ω⟩ →
        |caseMean (S.tower.stage (S.lastSeparated + d)).toStepSetup
            (hotCoreSites (S.tower.stage (S.lastSeparated + d)).toStepSetup V) V ⟨Y, ω⟩
            (S.cutoffCaseFn (S.lastSeparated + d) d (S.levelSide (S.lastSeparated + d + 1)) B) -
          S.formProductMean (d + 1) (S.levelSide (S.lastSeparated + d + 1)) B
            (S.cutoffColourForm (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1)) V)| ≤
        |CO| * (S.range : ℝ) ^ (4 * B.card + 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ) *
          (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) *
            S.localCurvature (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1)) V) ^
            (2 * B.card + 1) := by
      intro V Y ω hgd hp
      refine (hOne d _ hd rfl V Y ω hgd hp B).trans ?_
      have hy : 0 ≤ (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) *
          S.localCurvature (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1)) V) ^
          (2 * B.card + 1) := by
        have := S.localCurvature_nonneg (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1)) V
        positivity
      refine mul_le_mul_of_nonneg_right ?_ hy
      refine mul_le_mul_of_nonneg_right ?_ hxh
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have h := S.abs_stageMean_sub_succ_le hlog (S.lastSeparated + d) d (S.levelSide (S.lastSeparated + d + 1)) B
      (hMap _ _) (hBorel _ _) (hBorel _ _) (hMG _ (by omega)) (hWt _ (by omega))
      (hMb (S.lastSeparated + d) d _ rfl (by omega) hside.symm)
      (hMb (S.lastSeparated + d + 1) (d + 1) _ (by omega) (by omega) rfl) hO
      (by positivity) (by positivity) hE hGc
    rw [← S.stageMean_congr_side B hside] at h
    exact h
  have hchain := abs_sub_le_of_steps
    (D := fun d => S.stageMean (S.lastSeparated + d) d (S.levelSide (S.lastSeparated + d)) B) hstep S.logIndex le_rfl
  have h0 : S.stageMean (S.lastSeparated + 0) 0 (S.levelSide (S.lastSeparated + 0)) B =
      S.stageMean S.lastSeparated 0 (S.levelSide S.lastSeparated) B := rfl
  simp only [h0] at hchain
  have hPr := hProb (S.lastSeparated + S.logIndex) (S.levelSide (S.lastSeparated + S.logIndex))
  have hg := hGood (S.lastSeparated + S.logIndex) (by omega) (by omega)
  have hp0 : |S.formProductMean S.logIndex (S.levelSide (S.lastSeparated + S.logIndex)) B 0| ≤
      |CM| * (S.range : ℝ) ^ (4 * B.card) := by
    have h1 := S.abs_formProductMean_le
      (hI (S.lastSeparated + S.logIndex) S.logIndex (S.levelSide (S.lastSeparated + S.logIndex)) rfl (by omega) rfl)
      hrt 0 (le_refl (0 : ℝ)) (fun p => by rw [curlNorm_zero]; simp) hx0
    simpa using h1
  have hLq : 0 ≤ (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have htop := S.abs_stageMean_sub_formProductMean_zero_le hlog (S.lastSeparated + S.logIndex) S.logIndex
    (S.levelSide (S.lastSeparated + S.logIndex)) B (hBorel _ _)
    (c2 := |CM| * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4))
    (c := |CG (8 * Λ.k)| * S.scaleCoupling ^ ((1 : ℝ) / 4000))
    (b := |CM| * (S.range : ℝ) ^ (4 * B.card) * (|CG 1| * S.scaleCoupling ^ (-((1 : ℕ) : ℝ))))
    (fun A A' hA hA' => by
      refine (hMeans S.logIndex (S.levelSide (S.lastSeparated + S.logIndex)) (by omega) rfl B _
        (S.law (S.lastSeparated + S.logIndex) (S.levelSide (S.lastSeparated + S.logIndex))) A A' hA hA').2.trans ?_
      refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
      refine mul_le_mul_of_nonneg_right ?_ hLq
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    hrt hx (by positivity) (by positivity) (by positivity) (hcut _ (by omega) (by omega) _ rfl)
    (hMb (S.lastSeparated + S.logIndex) S.logIndex _ rfl (by omega) rfl)
    ((hg.2 (8 * Λ.k)).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) hxε)))
    (by
      have h1 : ENNReal.ofReal |S.formProductMean S.logIndex (S.levelSide (S.lastSeparated + S.logIndex)) B 0| ≤
          ENNReal.ofReal (|CM| * (S.range : ℝ) ^ (4 * B.card)) :=
        ENNReal.ofReal_le_ofReal hp0
      have h2 : (S.law (S.lastSeparated + S.logIndex) (S.levelSide (S.lastSeparated + S.logIndex)))
            (S.goodSet (S.lastSeparated + S.logIndex) (S.levelSide (S.lastSeparated + S.logIndex)))ᶜ ≤
          ENNReal.ofReal (|CG 1| * S.scaleCoupling ^ (-((1 : ℕ) : ℝ))) :=
        (hg.1 1).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hx0 _)))
      rw [ENNReal.ofReal_mul (p := |CM| * (S.range : ℝ) ^ (4 * B.card)) (by positivity)]
      exact mul_le_mul' h1 h2)
  have h3 := abs_sub_le (S.stageMean S.lastSeparated 0 (S.levelSide S.lastSeparated) B)
    (S.stageMean (S.lastSeparated + S.logIndex) S.logIndex (S.levelSide (S.lastSeparated + S.logIndex)) B)
    (S.formProductMean S.logIndex (S.levelSide (S.lastSeparated + S.logIndex)) B 0)
  linarith
end MomentPoint
section Final
private theorem error_sum_le {x r N Lq cO cM cM1 g1 g5 g g' : ℝ} {b : ℕ} (hb : b ≤ 8) (hx : 1 ≤ x) (hr : 1 ≤ r)
    (hN0 : 0 ≤ N) (hN : N ≤ 6000 * x ^ ((3 : ℝ) / 4000)) (hL0 : 0 ≤ Lq) (hL : Lq ≤ x⁻¹) (hcO : 0 ≤ cO) (hcM : 0 ≤ cM)
    (hcM1 : 0 ≤ cM1) (hg1 : 0 ≤ g1) (hg5 : 0 ≤ g5) (hg : 0 ≤ g) (hg' : 0 ≤ g') :
    N * (cO * r ^ (4 * b + 2) * x ^ (-(1 / 2) : ℝ) * (g1 * x ^ ((1 : ℝ) / 4000)) +
        cM * r ^ (4 * b) * (121 ^ 16 * x ^ 4) * (g5 * x ^ (-((5 : ℕ) : ℝ)))) +
      (cM * r ^ (4 * b) * Lq * (1 + 120 * (1 + g * x ^ ((1 : ℝ) / 4000))) ^ (2 * b) +
        cM * r ^ (4 * b) * (g' * x ^ (-((1 : ℕ) : ℝ)))) + cM1 * r ^ (4 * b) * Lq ≤
    (6000 * cO * g1 + 6000 * cM * 121 ^ 16 * g5 + cM * (121 + 120 * g) ^ 16 + cM * g' + cM1) *
      (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) := by apply _root_.YangMills.SharedProofs.p8611 <;> assumption
private theorem rpow_mul_le_target {x r : ℝ} {b : ℕ} (hx : 1 ≤ x) (hr1 : 1 ≤ r) (hr : r ≤ 2 * x ^ ((1 : ℝ) / 100)) :
    r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ) ≤ 8 * (r ^ (4 * b) * x ^ ((1 : ℝ) / 1000)) := by
  have hx0 : 0 < x := by linarith
  have hr0 : 0 ≤ r := by linarith
  have h3 : r ^ 3 ≤ 8 * x ^ ((3 : ℝ) / 100) := by
    calc r ^ 3 ≤ (2 * x ^ ((1 : ℝ) / 100)) ^ 3 := pow_le_pow_left₀ hr0 hr _
      _ = 8 * x ^ ((3 : ℝ) / 100) := by
          rw [mul_pow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 100)), ← Real.rpow_mul hx0.le]
          norm_num
  calc r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ) = r ^ (4 * b) * (r ^ 3 * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) := by
        rw [pow_add]
        ring
    _ ≤ r ^ (4 * b) * (8 * x ^ ((3 : ℝ) / 100) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (by positivity)) (by positivity)
    _ = 8 * (r ^ (4 * b) * (x ^ ((3 : ℝ) / 100) * x ^ (-(1 / 2) + 1 / 1000 : ℝ))) := by ring
    _ = 8 * (r ^ (4 * b) * x ^ ((3 : ℝ) / 100 + (-(1 / 2) + 1 / 1000))) := by rw [← Real.rpow_add hx0]
    _ ≤ 8 * (r ^ (4 * b) * x ^ ((1 : ℝ) / 1000)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by norm_num)
        exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
private theorem ceil_four_log_le {x : ℝ} (hx : 1 ≤ x) :
    ((⌈4 * Real.log x⌉₊ : ℕ) : ℝ) ≤ 6000 * x ^ ((3 : ℝ) / 4000) := by apply _root_.YangMills.SharedProofs.p23711 <;> assumption
end Final
section Parameters
private theorem forAllHull_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁)
    (h₂ : ForAllHullParameters Q₂) : ForAllHullParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem forAllHull_imp {Q₁ Q₂ : MomentParameters → Prop} (h : ForAllHullParameters Q₁)
    (f : ∀ Λ, Λ.k ≤ 8 → Q₁ Λ → Q₂ Λ) : ForAllHullParameters Q₂ := by apply _root_.YangMills.SharedProofs.p30752 <;> assumption
private theorem forAllHull_of_forAll {Q : MomentParameters → Prop} (h : ForAllParameters Q) :
    ForAllHullParameters Q := by apply _root_.YangMills.SharedProofs.p12974 <;> assumption
private theorem forAllHull_of_admissibleParameters {P : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop}
    (h : HoldsAtAdmissibleParameters P) : ForAllHullParameters fun Λ => P Λ.table Λ.floor := by apply _root_.YangMills.SharedProofs.p3284 <;> assumption
private theorem forAllHull_of_parameters {P : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop}
    (h : HoldsOnParameterFamilies P) : ForAllHullParameters fun Λ => P Λ.table Λ.floor := by
  intro a ha
  obtain ⟨L₀, r₀, C₀, hr, h⟩ := h a ha
  refine ⟨L₀, r₀, C₀, hr, ?_⟩
  intro L hodd hL Tb e1 e2 hD hCS hCH hrt hC
  obtain ⟨y₀, h⟩ := h L hodd hL Tb e1 e2 hD hCS hCH hrt hC
  exact ⟨0, fun Kr _ _ _ _ _ => ⟨y₀, fun y hy hR hW g _ _ k _ _ _ R d _ => h y hy hR hW⟩⟩
private theorem forAllHull_of_admissible {P : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop}
    (h : ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → P T y) :
    ForAllHullParameters fun Λ => P Λ.table Λ.floor := by apply _root_.YangMills.SharedProofs.p14065 <;> assumption
end Parameters
namespace MomentPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem stageOnFlow {j : ℕ} (hj : j ≤ S.data.windowLevel) :
    StageOnFlow Λ.table Λ.response Λ.floor S.β j
      (⟨S.tower.stage j, S.resp j⟩ : StageWithResponse Λ.stepParams) := by apply _root_.YangMills.SharedProofs.p21183 <;> assumption
private theorem isTowerOnParameters {s : ℕ} (hs : s + 1 ≤ S.data.windowLevel) :
    IsTowerAtParameters Λ.table Λ.floor S.tower S.β s where
  startsAtWilson := S.startsAtWilson
  coupling_eq := fun j hj => (S.stageOnFlow (hj.trans hs)).coupling_eq
  onFamily := fun j hj => (S.stageOnFlow (by omega)).onFamily.onFamily
private theorem isBlockTorusSide_levelSide {u : ℕ} (hu : u + 2 ≤ S.data.windowLevel) (hL : 1 ≤ Λ.stepParams.side) :
    IsBlockTorusSide Λ.stepParams (S.levelSide (u + 1) * Λ.stepParams.side) ∧
      Λ.stepParams.side ∣ S.levelSide (u + 1) := by apply _root_.YangMills.SharedProofs.p27816 <;> assumption
end MomentPoint
private theorem abs_sub_le_of_three {a b c A D P G : ℝ} (h1 : |A - D| ≤ a) (h2 : |D - P| ≤ b) (h3 : |P - G| ≤ c) :
    |A - G| ≤ a + b + c := by
  have e1 := abs_sub_le A D G
  have e2 := abs_sub_le D P G
  linarith
private theorem final_bounds {A0 D0 P p0 G b c T R e cl z m1 m0 : ℝ} (hlead : |A0 - D0| ≤ cl * T)
    (main : |D0 - P| ≤ b) (hiv : |P - G| ≤ c) (hbc : b + c ≤ z * T) (hp0 : |p0| ≤ m0 * R)
    (hiv0 : |p0 - G| ≤ m1 * R) (hT : T ≤ 8 * (R * e)) (he : 1 ≤ e) (hR : 0 ≤ R) (hm1 : 0 ≤ m1) (hm0 : 0 ≤ m0)
    (hcl : 0 ≤ cl) (hz : 0 ≤ z) :
    |A0 - G| ≤ (cl + z) * T ∧ |A0| ≤ (8 * (cl + z) + m1 + m0) * (R * e) ∧
      |G| ≤ (8 * (cl + z) + m1 + m0) * (R * e) := by
  have h1 : |A0 - G| ≤ (cl + z) * T := by
    have := abs_sub_le_of_three hlead main hiv
    have e1 : (cl + z) * T = cl * T + z * T := by ring
    linarith
  have hRe : R ≤ R * e := by nlinarith
  have hG : |G| ≤ (m1 + m0) * R := by
    have h2 := abs_sub_abs_le_abs_sub G p0
    rw [abs_sub_comm G p0] at h2
    have e1 : (m1 + m0) * R = m1 * R + m0 * R := by ring
    linarith
  have hG2 : (m1 + m0) * R ≤ (m1 + m0) * (R * e) := mul_le_mul_of_nonneg_left hRe (by positivity)
  have hT2 : (cl + z) * T ≤ (cl + z) * (8 * (R * e)) := mul_le_mul_of_nonneg_left hT (by positivity)
  refine ⟨h1, ?_, ?_⟩
  · have h3 : |A0| ≤ |A0 - G| + |G| := by
      have := abs_sub_abs_le_abs_sub A0 G
      linarith
    linarith
  · have : 0 ≤ (cl + z) * (8 * (R * e)) := by positivity
    linarith
theorem gaussianChainMoments (hGS : goodConfigsLikelyStatement) (hLM : leadingResponseMomentsStatement)
    (hMF : formMeansAtWeightStatement) (hWR : formMeansStatement)
    (hOS : formProductMeanStepStatement) (hWS : scaleWindowStatement) (hCG : goodConfigCutoffStatement)
    (hBC : chainMeasurabilityStatement) (hSB : StageStatesMeasurableStatement)
    (hMC : conditionalMeanIsCaseMeanStatement)
    (hRC : FreeEnergies.conditionalMeanReadsCasesStatement) (hFS : StagesAreWellPosed)
    (hRT : TowerAlongFlowStatement) : gaussianChainMomentsStatement := by
  unfold goodConfigsLikelyStatement ForAllHullPoints at hGS
  unfold leadingResponseMomentsStatement ForAllHullPoints at hLM
  unfold formMeansAtWeightStatement ForAllPoints at hMF
  unfold formMeansStatement ForAllPoints at hWR
  unfold formProductMeanStepStatement ForAllPoints at hOS
  unfold scaleWindowStatement ForAllPoints at hWS
  unfold goodConfigCutoffStatement ForAllPoints at hCG
  unfold conditionalMeanIsCaseMeanStatement at hMC
  unfold FreeEnergies.conditionalMeanReadsCasesStatement at hRC
  unfold TowerAlongFlowStatement at hRT
  unfold StagesAreWellPosed at hFS
  unfold gaussianChainMomentsStatement ForAllHullPoints
  refine forAllHull_imp (forAllHull_and hGS (forAllHull_and hLM (forAllHull_and (forAllHull_of_forAll hMF)
    (forAllHull_and (forAllHull_of_forAll hWR)
    (forAllHull_and (forAllHull_of_forAll hOS) (forAllHull_and (forAllHull_of_forAll hWS)
    (forAllHull_and (forAllHull_of_forAll hCG)
    (forAllHull_and (forAllHull_of_admissibleParameters hMC) (forAllHull_and (forAllHull_of_admissibleParameters hRC)
      (forAllHull_and (forAllHull_of_admissible (P := fun T y => ∀ (K : ResponseParameters) (β : ℝ)
        (hL : ∀ c : ChainStage (T.stepParameters y), ClusterExpansionOfAStep.CoarseLabelFacts c.toStepSetup)
        (z₀ : StageWithResponse (T.stepParameters y)),
        IsInitialStage T y β z₀ → ∀ s : ℕ, StagesOnFlowUpTo T K y β hL z₀ s → ∀ t ≤ s,
          (flowStages T y β hL z₀ t).1.toStepSetup.IsWellPosed) hFS)
        (forAllHull_of_parameters hRT))))))))))) ?_
  rintro Λ hk ⟨⟨CG, _, XG, _, _, hG⟩, ⟨CL, _, XL, _, _, hL⟩, ⟨CM, _, XM, _, _, hM⟩, ⟨CW, _, XW, _, _, hW⟩,
    ⟨CO, _, XO, _, _, hO⟩, ⟨CN, _, XN, _, _, hN⟩, ⟨CC, _, XC, _, _, hC⟩, hMC', hRC', hFS', hfit, hlam, -⟩
  have hrt : 0 ≤ Λ.stepParams.rt := hfit.rt_pos.le
  have hL1 : 1 ≤ Λ.stepParams.side := le_trans (by norm_num) hfit.L_ge
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = ∑ j ∈ Finset.range 18, |CG j| := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 121 + 120 * |CG (8 * Λ.k)| := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = 6000 * |CO 0| * K1 + 6000 * |CM 0| * 121 ^ 16 * |CG 5| + |CM 0| * D ^ 16 +
      |CM 0| * |CG 1| + |CM 1| :=
    ⟨_, rfl⟩
  have hK10 : 0 ≤ K1 := hK1 ▸ Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  refine ⟨fun j => Nat.casesOn j (|CL 0| + Z) (fun _ => 8 * (|CL 0| + Z) + |CM 1| + |CM 0|), 1,
    max Λ.floor (max 1 (max XG (max XL (max XM (max XO (max XN XC)))))), one_pos, le_max_left _ _,
    fun S hS d hd μ hμ B => ?_⟩
  have hx : 1 ≤ S.scaleCoupling := le_trans (by simp) hS
  have hxG : XG ≤ S.scaleCoupling := le_trans (by simp) hS
  have hxL : XL ≤ S.scaleCoupling := le_trans (by simp) hS
  have hxM : XM ≤ S.scaleCoupling := le_trans (by simp) hS
  have hxO : XO ≤ S.scaleCoupling := le_trans (by simp) hS
  have hxN : XN ≤ S.scaleCoupling := le_trans (by simp) hS
  have hxC : XC ≤ S.scaleCoupling := le_trans (by simp) hS
  have hx0 : 0 ≤ S.scaleCoupling := by linarith
  have hB : B.card ≤ 8 := by
    have := Finset.card_le_univ B
    simp only [Fintype.card_fin] at this
    omega
  have hlog := hBC.2.1
  have hBorel : ∀ (u n : ℕ) [NeZero n], Measurable (stageState S.tower u n) :=
    fun u n _ => hSB Λ.stepParams hfit S.tower u n
  have hBC3 := hBC.2.2 Λ.stepParams hfit hlam S.tower S.isCutoff S.marksMeasurable S.β
  have hforms : ∀ u, u ≤ S.data.windowLevel → (S.tower.stage u).toStepSetup.IsWellPosed := by
    intro u hu
    have h := hFS' Λ.response S.β S.labelFacts S.initial S.isInitial S.data.windowLevel S.onFlow u hu
    rw [← S.stage_eq u hu] at h
    exact h
  obtain ⟨hLq, -, -, -, -, hK, -⟩ := hN S hxN
  have hMeans : ∀ (d n : ℕ) [NeZero n], d ≤ S.logIndex + 1 → n = S.levelSide (S.lastSeparated + d) →
      ∀ (B : Finset (Fin Λ.k)) (Ω : Type) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (A A' : Ω → ColourForm n), Measurable A → Measurable A' →
      ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w)| ∂μ ≤
        ENNReal.ofReal (CM 0 * (S.range : ℝ) ^ (4 * B.card)) *
          (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A +
            weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A')) ^
          (2 * B.card) ∧
      ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w) - S.formProductMean d n B 0| ∂μ ≤
        ENNReal.ofReal (CM 0 * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(d : ℝ) / 4)) *
          (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A +
            weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A')) ^
          (2 * B.card) := by
    intro d n _ hd hn B Ω _ μ _ A A' hA hA'
    have h := (hM S hxM).1 d n hd hn B Ω μ A A' hA hA'
    exact ⟨h.1, h.2.1⟩
  have main := S.abs_stageMean_sub_top_le hlog hrt hk hx B hBorel (fun u n _ => (hBC3 u n).1)
    (fun u n _ => (hBC3 u n).2) hK
    (fun u hu F hm hb => hMC' S.tower S.β u (S.levelSide (u + 1)) (S.isTowerOnParameters (by omega)) S.isCutoff
      S.marksMeasurable (hforms u (by omega))
      (S.isBlockTorusSide_levelSide hu hL1).1 (S.isBlockTorusSide_levelSide hu hL1).2 F hm hb)
    (fun u hu => (hRC' S.tower S.β u (S.levelSide (u + 1)) (S.isTowerOnParameters (by omega)) S.isCutoff
      S.marksMeasurable (hforms u (by omega))
      (S.isBlockTorusSide_levelSide hu hL1).1 (S.isBlockTorusSide_levelSide hu hL1).2).1)
    (fun u h1 h2 n _ hn W Y hg => (hC S hxC u h1 h2 n hn W Y hg).2.1) hMeans (hO S hxO) (hG S hxG).1
  have hlead := (hL S hxL B).2
  have hiv := (hM S hxM).2 S.logIndex d (S.levelSide (S.lastSeparated + S.logIndex)) hd (by omega) rfl μ hμ B
  have hiv0 := (hM S hxM).2 0 d (S.levelSide (S.lastSeparated + 0)) hd (by omega) rfl μ hμ B
  have hprod := (hW S).2.2.2.1
  have e0 : S.stageMean S.lastSeparated 0 (S.levelSide S.lastSeparated) B =
      ∫ w, Set.indicator {w | S.IsGoodConfig S.lastSeparated (S.levelSide S.lastSeparated)
          (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1
          (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).2.1}
        (fun w => S.formProduct S.lastSeparated (S.levelSide S.lastSeparated) B
          (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated)
            (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1)) w
        ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) := by
    have e : S.cutoffMean S.lastSeparated 0 (S.levelSide S.lastSeparated) B = fun w =>
        S.formProduct S.lastSeparated (S.levelSide S.lastSeparated) B
          (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated)
            (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1) :=
      funext fun w => hprod _ B _
    unfold MomentPoint.stageMean
    rw [e]
    rfl
  rw [← e0] at hlead
  have hr0 : 0 < S.scaleCoupling ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos (by linarith) _
  have hr1 : (1 : ℝ) ≤ S.range := by
    have : 0 < S.range := Nat.ceil_pos.2 hr0
    exact_mod_cast this
  have hr2 : (S.range : ℝ) ≤ 2 * S.scaleCoupling ^ ((1 : ℝ) / 100) := by
    have h1 := Nat.ceil_lt_add_one hr0.le
    have h2 : 1 ≤ S.scaleCoupling ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx (by norm_num)
    have h3 : (S.range : ℝ) = ((⌈S.scaleCoupling ^ ((1 : ℝ) / 100)⌉₊ : ℕ) : ℝ) := rfl
    linarith
  have hNle : (S.logIndex : ℝ) ≤ 6000 * S.scaleCoupling ^ ((3 : ℝ) / 4000) := ceil_four_log_le hx
  have hLq0 : 0 ≤ (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hrr : (0 : ℝ) ≤ (S.range : ℝ) ^ (4 * B.card) := by positivity
  have hT0 : 0 ≤ (S.range : ℝ) ^ (4 * B.card + 3) * S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ) := by positivity
  have num := error_sum_le (x := S.scaleCoupling) (r := S.range) (N := S.logIndex)
    (Lq := (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4)) (cO := |CO 0|)
    (cM := |CM 0|) (cM1 := |CM 1|) (g1 := |CG (2 * B.card + 1)|) (g5 := |CG 5|) (g := |CG (8 * Λ.k)|) (g' := |CG 1|)
    hB hx hr1 (Nat.cast_nonneg _) hNle hLq0 hLq (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
  have hg1 : |CG (2 * B.card + 1)| ≤ K1 := by
    rw [hK1]
    exact Finset.single_le_sum (f := fun j => |CG j|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega))
  have hZle : 6000 * |CO 0| * |CG (2 * B.card + 1)| + 6000 * |CM 0| * 121 ^ 16 * |CG 5| +
      |CM 0| * (121 + 120 * |CG (8 * Λ.k)|) ^ 16 + |CM 0| * |CG 1| + |CM 1| ≤ Z := by
    rw [hZ, hD]
    gcongr
  have hiv' : |S.formProductMean S.logIndex (S.levelSide (S.lastSeparated + S.logIndex)) B 0 -
        ∫ X, ∏ i ∈ B, S.halfForm d (S.data.period Λ.stepParams.side) i X ∂μ| ≤
      |CM 1| * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) :=
    hiv.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hrr) hLq0)
  have hlead' : |S.scaleCoupling ^ B.card * ∫ w, ∏ i ∈ B, S.supportTotal S.lastSeparated
        (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)
        ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) -
      S.stageMean S.lastSeparated 0 (S.levelSide S.lastSeparated) B| ≤
      |CL 0| * ((S.range : ℝ) ^ (4 * B.card + 3) * S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ)) := by
    refine hlead.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hT0
  have hbc := num.trans (mul_le_mul_of_nonneg_right hZle hT0)
  have hp0 : |S.formProductMean 0 (S.levelSide (S.lastSeparated + 0)) B 0| ≤ |CM 0| * (S.range : ℝ) ^ (4 * B.card) := by
    have h1 := S.abs_formProductMean_le (d := 0) (u := S.lastSeparated + 0) (n := S.levelSide (S.lastSeparated + 0))
      (B := B) (C0 := CM 0)
      (fun A A' hA hA' => (hMeans 0 _ (by omega) rfl B Unit (Measure.dirac ()) A A' hA hA').1) hrt 0
      (le_refl (0 : ℝ)) (fun p => by rw [MomentPoint.curlNorm_zero]; simp) hx0
    simpa using h1
  have hiv0' : |S.formProductMean 0 (S.levelSide (S.lastSeparated + 0)) B 0 -
        ∫ X, ∏ i ∈ B, S.halfForm d (S.data.period Λ.stepParams.side) i X ∂μ| ≤
      |CM 1| * (S.range : ℝ) ^ (4 * B.card) := by
    refine hiv0.trans ?_
    simp only [Nat.cast_zero, neg_zero, zero_div, Real.rpow_zero, mul_one]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hrr
  have hout := final_bounds hlead' main hiv' hbc hp0 hiv0' (rpow_mul_le_target (b := B.card) hx hr1 hr2)
    (Real.one_le_rpow hx (by norm_num)) hrr (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hZ0
  refine ⟨hout.1.trans_eq ?_, hout.2.1.trans_eq ?_, hout.2.2.trans_eq ?_⟩
  · show (|CL 0| + Z) * ((S.range : ℝ) ^ (4 * B.card + 3) * S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ)) =
      (|CL 0| + Z) * (S.range : ℝ) ^ (4 * B.card + 3) * S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ)
    ring
  · show (8 * (|CL 0| + Z) + |CM 1| + |CM 0|) * ((S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000)) =
      (8 * (|CL 0| + Z) + |CM 1| + |CM 0|) * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000)
    ring
  · show (8 * (|CL 0| + Z) + |CM 1| + |CM 0|) * ((S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000)) =
      (8 * (|CL 0| + Z) + |CM 1| + |CM 0|) * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000)
    ring
end YangMills.Construction.MomentLaw
end
