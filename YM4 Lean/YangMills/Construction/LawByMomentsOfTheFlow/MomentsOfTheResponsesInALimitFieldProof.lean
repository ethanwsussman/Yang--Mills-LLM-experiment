import YangMills.Construction.LawByMomentsOfTheFlow.CutOfAFieldIsBorel
import YangMills.Construction.LawByMomentsOfTheFlow.FormsAtTheCutAreOfTheFarClass
import YangMills.Construction.LawByMomentsOfTheFlow.GoodStatesInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.MeansOfFormsAtAWeight
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsOfTheResponsesInALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.OneStepOfTheMeansOfForms
import YangMills.Construction.LawByMomentsOfTheFlow.ResponsesOfAGoodStateNearTheirForms
import YangMills.Construction.LawByMomentsOfTheFlow.TheCutOfAGoodState
import YangMills.Construction.LawByMomentsOfTheFlow.WhatTheMeansOfFormsRead
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Quaternion Topology
namespace YangMills.Construction.MomentLaw
open MomentMethod TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses ResponseInTheExpansion BlockAverages LumpContours
section Borel
variable {Ω₀ : Type} [MeasurableSpace Ω₀]
private theorem measurable_pathHolonomy {F : BlockFrame} {j : ℕ} (X : Ω₀ → F.GaugeField j)
    (hX : ∀ x i, Measurable fun a => X a x i) (x : F.Site j) (l : List PathStep) :
    Measurable fun a => pathHolonomy (X a) x l := by apply _root_.YangMills.SharedProofs.p6492 <;> assumption
private theorem measurable_readAtLevel (F : BlockFrame) (j : ℕ) {n : ℕ} {W : Ω₀ → TorusField n} (hW : Measurable W)
    (x : F.Site j) (i : Fin 4) : Measurable fun a => readAtLevel F j (W a) x i :=
  (measurable_pi_apply i).comp ((measurable_pi_apply _).comp hW)
private theorem measurable_axialGaugeAt (ℓ : TorusLumps.StepParameters) {n : ℕ} {V : Ω₀ → TorusField n} (hV : Measurable V)
    (o z : TorusSite n) : Measurable fun a => axialGaugeAt ℓ (V a) o z := by
  unfold axialGaugeAt ColdStepAtMirrorFrames.axialGaugeHolonomy
  exact measurable_pathHolonomy _ (fun x i => measurable_readAtLevel _ _ hV x i) _ _
private theorem measurable_curvature {n : ℕ} {V : Ω₀ → TorusField n} (hV : Measurable V) (x : TorusSite n) (μ ν : Fin 4) :
    Measurable fun a => curvature (V a) x μ ν := by apply _root_.YangMills.SharedProofs.p35643 <;> assumption
private theorem measurable_gaugeTransform {n : ℕ} {g : Ω₀ → TorusSite n → UnitQuaternion} (hg : Measurable g)
    {V : Ω₀ → TorusField n} (hV : Measurable V) (b : TorusBond n) : Measurable fun ω => ResponseInTheExpansion.gaugeTransform (g ω) (V ω) b := by apply _root_.YangMills.SharedProofs.p20103 <;> assumption
private theorem measurable_imaginaryComponent_minimalLog
    (hlog : MeasurableQuaternion (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])))
    (c : Fin 3) {G : Ω₀ → UnitQuaternion} (hG : Measurable G) :
    Measurable fun ω => imaginaryComponent c (minimalLog (G ω)) := by apply _root_.YangMills.SharedProofs.p57079 <;> assumption
private theorem imaginaryComponent_smul (c : ℝ) (e : Fin 3) (w : imaginaryQuaternions) :
    imaginaryComponent e (c • w) = c * imaginaryComponent e w := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem measurable_toColourForm_cutoffCoords
    (hlog : MeasurableQuaternion (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])))
    (ℓ : TorusLumps.StepParameters) {n : ℕ} [NeZero n] (o : TorusSite n) (m : ℕ) :
    Measurable fun W : TorusField n => (toColourForm (cutoffCoords ℓ W o m) : ColourForm n) := by
  refine measurable_pi_lambda _ fun e => measurable_pi_lambda _ fun b => ?_
  have hg : Measurable fun W : TorusField n => axialGaugeAt ℓ W o :=
    measurable_pi_lambda _ fun z => measurable_axialGaugeAt ℓ measurable_id o z
  have hl := measurable_imaginaryComponent_minimalLog hlog e (measurable_gaugeTransform hg measurable_id b)
  have e' : (fun W : TorusField n => (toColourForm (cutoffCoords ℓ W o m) : ColourForm n) e b) =
      fun W => cutoffProfile o m b.1 * imaginaryComponent e (minimalLog (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W b)) := by
    funext W
    exact imaginaryComponent_smul _ _ _
  rw [e']
  exact measurable_const.mul hl
abbrev _root_.YangMills.SharedProofs.p107287 := @measurable_toColourForm_cutoffCoords
private theorem measurable_boxCurvature {n : ℕ} [NeZero n] (o : TorusSite n) (r : ℝ) :
    Measurable fun W : TorusField n => boxCurvature o r W := by
  unfold boxCurvature
  exact Measurable.iSup fun p => measurable_curvature measurable_id _ _ _
abbrev _root_.YangMills.DeltaSharedProofs.p12736 := @measurable_boxCurvature
end Borel
section Means
variable (a ρA : ℝ) (L : ℕ) [NeZero L]
private theorem measurable_fluctuation_coord (u n : ℕ) [NeZero n] (i : Fin 3 × ChartBondIndex L u n) :
    Measurable fun η : StepFluctuation L u n => η i :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable
private theorem measurable_pushColours_add (c : ℝ) (u n : ℕ) [NeZero n] :
    Measurable fun p : ColourForm n × StepFluctuation L u n => (fun e b =>
      pushColours a ρA L u p.1 e b + c * extendFluctuation p.2 e b : ColourForm (n * L)) := by
  refine measurable_pi_lambda _ fun e => measurable_pi_lambda _ fun b => ?_
  refine Measurable.add ?_ (measurable_const.mul ?_)
  · unfold pushColours responseMap
    refine Finset.measurable_sum _ fun c' _ => measurable_const.mul ?_
    exact (measurable_pi_apply c').comp ((measurable_pi_apply e).comp measurable_fst)
  · unfold extendFluctuation extendChart
    refine Finset.measurable_sum _ fun b' _ => ?_
    by_cases h : (StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) = b'.1
    · simp only [if_pos h]
      exact (measurable_fluctuation_coord L u n _).comp measurable_snd
    · simp only [if_neg h]
      exact measurable_const
private theorem measurable_descendWithNoise (t : ℕ) (c : ℝ) : ∀ (d n : ℕ) [NeZero n],
    Measurable fun p : ColourForm n × FluctuationSample L t d n => descendWithNoise a ρA t c d n p.1 p.2
  | 0, n, _ => measurable_fst
  | d + 1, n, _ => by
    letI := instMeasurableSpaceFluctuationSample L t d (n * L)
    have h := measurable_descendWithNoise t c d (n * L)
    have h1 : Measurable fun p : ColourForm n × FluctuationSample L t (d + 1) n =>
        (fun e b => pushColours a ρA L (t + d) p.1 e b + c * extendFluctuation p.2.1 e b : ColourForm (n * L)) :=
      (measurable_pushColours_add a ρA L c (t + d) n).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    exact h.comp (h1.prodMk (measurable_snd.comp measurable_snd))
private theorem isProbabilityMeasure_fluctuationSampleLaw (t : ℕ) :
    ∀ (d n : ℕ), IsProbabilityMeasure (fluctuationSampleLaw a L t d n)
  | 0, _ => Measure.dirac.isProbabilityMeasure
  | d + 1, n => by
    let _ := instMeasurableSpaceFluctuationSample L t d (n * L)
    have h2 := isProbabilityMeasure_fluctuationSampleLaw t d (n * L)
    have h1 : IsProbabilityMeasure (fluctuationGaussian a L 1 (t + d) n) := by
      unfold fluctuationGaussian
      infer_instance
    exact Measure.prod.instIsProbabilityMeasure _ _
end Means
section Forms
private theorem measurable_colourEval_diag {n : ℕ} [NeZero n] (q : BondBilinear n) :
    Measurable fun X : ColourForm n => colourEval q X X := by
  unfold colourEval bilinearEval
  refine Finset.measurable_sum _ fun e _ => Finset.measurable_sum _ fun b _ => Finset.measurable_sum _ fun b' _ => ?_
  have h : ∀ c : TorusBond n, Measurable fun X : ColourForm n => X e c :=
    fun c => (measurable_pi_apply c).comp (measurable_pi_apply e)
  exact ((h b).mul_const _).mul (h b')
end Forms
namespace MomentPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem measurable_formProduct (t n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)) :
    Measurable (S.formProduct t n B) := by
  unfold formProduct
  exact Finset.measurable_prod _ fun i _ => measurable_const.mul (measurable_colourEval_diag _)
abbrev _root_.YangMills.SharedProofs.p97087 := @measurable_formProduct
private theorem measurable_formProductMean (d n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)) :
    Measurable (S.formProductMean d n B) := by
  have h := isProbabilityMeasure_fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n
  have h1 := (S.measurable_formProduct S.lastSeparated (fineSide Λ.stepParams.side d n) B).comp
    (measurable_descendWithNoise Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side S.lastSeparated
      (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d n)
  exact (h1.stronglyMeasurable.integral_prod_right').measurable
abbrev _root_.YangMills.SharedProofs.p14233 := @measurable_formProductMean
private def goodSet (u n : ℕ) [NeZero n] : Set (MarkedSample Λ.stepParams u n) :=
  {w | S.IsGoodConfig u n (S.state u n w).1 (S.state u n w).2.1}
private theorem measurableSet_sigma_fst_eq {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
private theorem measurable_localCurvature (u n : ℕ) [NeZero n] : Measurable (S.localCurvature u n) :=
  measurable_boxCurvature _ _
private theorem measurableSet_goodSet (u n : ℕ) [NeZero n] (hq : Measurable (stageState S.tower u n)) :
    MeasurableSet (S.goodSet u n) := by
  classical
  have h1 : MeasurableSet {z : StageState S.tower u n | S.IsGoodConfig u n z.1 z.2.1} := by
    have e : {z : StageState S.tower u n | S.IsGoodConfig u n z.1 z.2.1} =
        {z | S.localCurvature u n z.1 ≤ S.scaleCoupling ^ (-(1 / 4) : ℝ)} ∩
          ⋃ a ∈ (Finset.univ.filter fun a : Finset (TorusSite n) =>
            Disjoint a (supBall (S.originSite u n) (8 * S.rangeSq))),
            {z : StageState S.tower u n | z.2.1 = a} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        exists_prop, exists_eq_right']
      exact ⟨fun h => ⟨h.curvature_le, h.disjoint_lumps⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [e]
    refine (measurableSet_le ((S.measurable_localCurvature u n).comp measurable_fst) measurable_const).inter ?_
    refine Finset.measurableSet_biUnion _ fun a _ => ?_
    exact measurable_snd (measurableSet_sigma_fst_eq a)
  exact hq h1
abbrev _root_.YangMills.DeltaSharedProofs.p501697 := @measurableSet_goodSet
private def cutoffMean (u d n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)) (w : MarkedSample Λ.stepParams u n) : ℝ :=
  S.formProductMean d n B (S.cutoffColourForm u n (S.state u n w).1)
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
    S.distanceWeight u n p ≤ 1 := by
  unfold distanceWeight
  rw [Real.exp_le_one_iff, neg_nonpos]
  have : 0 ≤ Λ.stepParams.weightRate := by unfold TorusLumps.StepParameters.weightRate; positivity
  positivity
abbrev _root_.YangMills.SharedProofs.p40065 := @distanceWeight_le_one
end MomentPoint
section Norms
private theorem weightedCurvatureNorm_le_eLpNorm {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ} [NeZero n]
    {ω : TorusPlaquette n → ℝ} (hω : ∀ p, ω p ≤ 1) (q : ENNReal) (X : Ω → ColourForm n) (g : Ω → ℝ)
    (hg : ∀ w (p : OrientedPlaquette n), curlNorm (X w) p.1 ≤ g w) : weightedCurvatureNorm μ ω q X ≤ eLpNorm g q μ := by
  unfold weightedCurvatureNorm
  refine iSup_le fun p => ?_
  calc ENNReal.ofReal (ω p.1) * eLpNorm (fun e => curlNorm (X e) p.1) q μ
      ≤ 1 * eLpNorm (fun e => curlNorm (X e) p.1) q μ := by
        gcongr
        exact ENNReal.ofReal_le_one.2 (hω _)
    _ = eLpNorm (fun e => curlNorm (X e) p.1) q μ := one_mul _
    _ ≤ eLpNorm g q μ := eLpNorm_mono_real fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by unfold curlNorm; exact Real.sqrt_nonneg _)]
        exact hg w p
abbrev _root_.YangMills.SharedProofs.p17835 := @weightedCurvatureNorm_le_eLpNorm
end Norms
section Tower
variable {ℓ : TorusLumps.StepParameters}
private theorem stageState_fst (T : StageTower ℓ) (s n : ℕ) [NeZero n] (w : MarkedSample ℓ s n) :
    (stageState T s n w).1 = topField ℓ s n w := by apply _root_.YangMills.SharedProofs.p2480 <;> assumption
private def caseLiftOf (T : StageTower ℓ) (s n : ℕ) [NeZero n]
    (F : TorusField n → CaseFunction (T.stage s).toStepSetup n) (u : MarkedSample ℓ (s + 1) n) : ℝ :=
  F u.2.2.1 (topField ℓ s (n * ℓ.side) u.1) (stageState T s (n * ℓ.side) u.1).2.1
    (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1
private theorem coarseStateWeight_pos_ae (T : StageTower ℓ) (β : ℝ) (s n : ℕ) [NeZero n]
    [IsProbabilityMeasure (markedSampleLaw T β (s + 1) n)]
    (hm : stageSigma T (s + 1) n ≤ markedSampleMeasurableSpace ℓ (s + 1) n)
    (hw : ∀ (C : Finset (TorusSite n)) (V : TorusField n) W Yt ωt bad b,
      0 ≤ stepWeight (T.stage s).toStepSetup C V W Yt ωt bad b)
    (h1 : (markedSampleLaw T β (s + 1) n)[caseLiftOf T s n (fun _ _ _ _ _ _ => 1) | stageSigma T (s + 1) n]
      =ᵐ[markedSampleLaw T β (s + 1) n]
      fun u => caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
        (stageState T (s + 1) n u).2 (fun _ _ _ _ _ => 1)) :
    ∀ᵐ u ∂(markedSampleLaw T β (s + 1) n),
      0 < coarseStateWeight (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
        (stageState T (s + 1) n u).2 := by
  have e1 : caseLiftOf T s n (fun _ _ _ _ _ _ => 1) = fun _ => (1 : ℝ) := rfl
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
section Numbers
private theorem one_add_mul_le_rpow_quarter {x v : ℝ} (hx : 1 ≤ x) (hv0 : 0 ≤ v) (hv : v ≤ x ^ (-(1 / 4) : ℝ)) :
    1 + 120 * x ^ ((1 : ℝ) / 2) * v ≤ 121 * x ^ ((1 : ℝ) / 4) := by
  have hx0 : 0 < x := by linarith
  have h1 : x ^ ((1 : ℝ) / 2) * x ^ (-(1 / 4) : ℝ) = x ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have h2 : (1 : ℝ) ≤ x ^ ((1 : ℝ) / 4) := Real.one_le_rpow hx (by norm_num)
  have h3 : x ^ ((1 : ℝ) / 2) * v ≤ x ^ ((1 : ℝ) / 4) := by
    rw [← h1]
    exact mul_le_mul_of_nonneg_left hv (by positivity)
  nlinarith
abbrev _root_.YangMills.SharedProofs.p117073 := @one_add_mul_le_rpow_quarter
private theorem pow_le_rpow_four {x : ℝ} (hx : 1 ≤ x) {j : ℕ} (hj : j ≤ 16) :
    (121 * x ^ ((1 : ℝ) / 4)) ^ j ≤ 121 ^ 16 * x ^ 4 := by
  have hx0 : 0 < x := by linarith
  have h2 : (1 : ℝ) ≤ x ^ ((1 : ℝ) / 4) := Real.one_le_rpow hx (by norm_num)
  have h1 : (1 : ℝ) ≤ 121 * x ^ ((1 : ℝ) / 4) := by linarith
  calc (121 * x ^ ((1 : ℝ) / 4)) ^ j ≤ (121 * x ^ ((1 : ℝ) / 4)) ^ 16 := pow_le_pow_right₀ h1 hj
    _ = 121 ^ 16 * x ^ 4 := by
      rw [mul_pow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 4)), ← Real.rpow_mul hx0.le]
      norm_num
abbrev _root_.YangMills.SharedProofs.p9016 := @pow_le_rpow_four
end Numbers
namespace MomentPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem localCurvature_nonneg (u n : ℕ) [NeZero n] (W : TorusField n) : 0 ≤ S.localCurvature u n W :=
  Real.iSup_nonneg fun _ => norm_nonneg _
private theorem curlNorm_zero {n : ℕ} [NeZero n] (p : TorusPlaquette n) : curlNorm (0 : ColourForm n) p = 0 := by
  unfold curlNorm curl
  simp
end MomentPoint
section ResponsesNearForms
private theorem forAllHullParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁)
    (h₂ : ForAllHullParameters Q₂) : ForAllHullParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem forAllHullParameters_mono {Q₁ Q₂ : MomentParameters → Prop} (h : ForAllHullParameters Q₁)
    (f : ∀ Λ, Λ.k ≤ 8 → Q₁ Λ → Q₂ Λ) : ForAllHullParameters Q₂ := by apply _root_.YangMills.SharedProofs.p30752 <;> assumption
private theorem forAllHullParameters_of_forAllParameters {Q : MomentParameters → Prop} (h : ForAllParameters Q) :
    ForAllHullParameters Q := by apply _root_.YangMills.SharedProofs.p12974 <;> assumption
private theorem forAllHullParameters_of_admissibleParameters {P : ParameterAssignment → ℝ → Prop}
    (h : HoldsAtAdmissibleParameters P) : ForAllHullParameters fun Λ => P Λ.table Λ.floor := by apply _root_.YangMills.SharedProofs.p3284 <;> assumption
private theorem forAllHullParameters_of_parameters {P : ParameterAssignment → ℝ → Prop}
    (h : HoldsOnParameterFamilies P) : ForAllHullParameters fun Λ => P Λ.table Λ.floor := by
  intro a ha
  obtain ⟨L₀, r₀, C₀, hr, h⟩ := h a ha
  refine ⟨L₀, r₀, C₀, hr, ?_⟩
  intro L hodd hL Tb e1 e2 hD hCS hCH hrt hC
  obtain ⟨y₀, h⟩ := h L hodd hL Tb e1 e2 hD hCS hCH hrt hC
  exact ⟨0, fun Kr _ _ _ _ _ => ⟨y₀, fun y hy hR hW g _ _ k _ _ _ R d _ => h y hy hR hW⟩⟩
private theorem forAllHullParameters_of_admissible {P : ParameterAssignment → ℝ → Prop}
    (h : ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → P T y) :
    ForAllHullParameters fun Λ => P Λ.table Λ.floor := by apply _root_.YangMills.SharedProofs.p14065 <;> assumption
end ResponsesNearForms
namespace MomentPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem stageOnFlow_at {j : ℕ} (hj : j ≤ S.data.windowLevel) :
    StageOnFlow Λ.table Λ.response Λ.floor S.β j
      (⟨S.tower.stage j, S.resp j⟩ : StageWithResponse Λ.stepParams) := by apply _root_.YangMills.SharedProofs.p21183 <;> assumption
private theorem isTowerOnParameters_of_le {s : ℕ} (hs : s + 1 ≤ S.data.windowLevel) :
    IsTowerAtParameters Λ.table Λ.floor S.tower S.β s where
  startsAtWilson := S.startsAtWilson
  coupling_eq := fun j hj => (S.stageOnFlow_at (hj.trans hs)).coupling_eq
  onFamily := fun j hj => (S.stageOnFlow_at (by omega)).onFamily.onFamily
private theorem isBlockTorusSide_levelSide {u : ℕ} (hu : u + 2 ≤ S.data.windowLevel) (hL : 1 ≤ Λ.stepParams.side) :
    IsBlockTorusSide Λ.stepParams (S.levelSide (u + 1) * Λ.stepParams.side) ∧
      Λ.stepParams.side ∣ S.levelSide (u + 1) := by
  have e : S.data.windowLevel - (u + 1) = S.data.windowLevel - (u + 2) + 1 := by omega
  have hd : Λ.stepParams.side ∣ S.levelSide (u + 1) := by
    show Λ.stepParams.side ∣ S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (u + 1))
    rw [e, pow_succ]
    exact Dvd.dvd.mul_left (Dvd.intro_left _ rfl) _
  refine ⟨⟨Dvd.intro_left _ rfl, ?_⟩, hd⟩
  have h1 : S.data.period Λ.stepParams.side ≤ S.levelSide (u + 1) := Nat.le_mul_of_pos_right _ (Nat.pow_pos hL)
  have h2 := S.side_le
  have h3 : Λ.stepParams.n₀ ≤ Λ.stepParams.side * Λ.stepParams.n₀ := Nat.le_mul_of_pos_left _ hL
  rw [mul_comm]
  exact Nat.mul_le_mul_right _ (h3.trans (h2.trans h1))
abbrev _root_.YangMills.SharedProofs.p27816 := @isBlockTorusSide_levelSide
end MomentPoint
section Numbers
private theorem scaled_factor_bounds {x s r v N f Q C E : ℝ} (hs : 1 ≤ s) (hx : x = s ^ 2) (hr : 1 ≤ r) (hv : 0 ≤ v)
    (hN : 1 ≤ N) (hC : 0 ≤ C) (hE0 : 0 ≤ E) (hE : s ^ 3 * E ≤ 1)
    (h1 : |f - 1 / 2 * Q| ≤ C * (r ^ 7 * v ^ 3 + r ^ 4 * s⁻¹ * v ^ 2 + r ^ 4 * E * N))
    (h2 : |Q| ≤ C * r ^ 4 * v ^ 2) :
    |x * f - x / 2 * Q| ≤ r ^ 3 * s⁻¹ * ((3 * C + 1) * r ^ 4 * (1 + s * v) ^ 3 * N) ∧
      |x / 2 * Q| ≤ (3 * C + 1) * r ^ 4 * (1 + s * v) ^ 3 * N := by
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  set a := s * v with ha
  have ha0 : 0 ≤ a := by positivity
  have hw : 1 ≤ 1 + a := by linarith
  have haw : a ≤ 1 + a := by linarith
  have hvs : v = a * s⁻¹ := by rw [ha]; field_simp
  have r47 : r ^ 4 ≤ r ^ 7 := pow_le_pow_right₀ hr (by norm_num)
  have hw3 : 1 ≤ (1 + a) ^ 3 := one_le_pow₀ hw
  have ha3 : a ^ 3 ≤ (1 + a) ^ 3 := pow_le_pow_left₀ ha0 haw 3
  have ha2 : a ^ 2 ≤ (1 + a) ^ 3 := by
    calc a ^ 2 ≤ (1 + a) ^ 2 := pow_le_pow_left₀ ha0 haw 2
      _ ≤ (1 + a) ^ 3 := pow_le_pow_right₀ hw (by norm_num)
  have t1 : x * (r ^ 7 * v ^ 3) ≤ s⁻¹ * (r ^ 7 * (1 + a) ^ 3 * N) := by
    have e : x * (r ^ 7 * v ^ 3) = s⁻¹ * (r ^ 7 * a ^ 3) := by rw [hx, hvs]; field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc r ^ 7 * a ^ 3 ≤ r ^ 7 * (1 + a) ^ 3 := by gcongr
      _ ≤ r ^ 7 * (1 + a) ^ 3 * N := le_mul_of_one_le_right (by positivity) hN
  have t2 : x * (r ^ 4 * s⁻¹ * v ^ 2) ≤ s⁻¹ * (r ^ 7 * (1 + a) ^ 3 * N) := by
    have e : x * (r ^ 4 * s⁻¹ * v ^ 2) = s⁻¹ * (r ^ 4 * a ^ 2) := by rw [hx, hvs]; field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc r ^ 4 * a ^ 2 ≤ r ^ 7 * (1 + a) ^ 3 := by gcongr
      _ ≤ r ^ 7 * (1 + a) ^ 3 * N := le_mul_of_one_le_right (by positivity) hN
  have t3 : x * (r ^ 4 * E * N) ≤ s⁻¹ * (r ^ 7 * (1 + a) ^ 3 * N) := by
    have e : x * (r ^ 4 * E * N) = s⁻¹ * ((s ^ 3 * E) * (r ^ 4 * N)) := by rw [hx]; field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (s ^ 3 * E) * (r ^ 4 * N) ≤ 1 * (r ^ 4 * N) := by gcongr
      _ = r ^ 4 * 1 * N := by ring
      _ ≤ r ^ 7 * (1 + a) ^ 3 * N := by gcongr
  set R := r ^ 7 * (1 + a) ^ 3 * N with hR
  have hR0 : 0 ≤ s⁻¹ * R := by positivity
  constructor
  · have e : x * f - x / 2 * Q = x * (f - 1 / 2 * Q) := by ring
    rw [e, abs_mul, abs_of_nonneg hx0]
    calc x * |f - 1 / 2 * Q| ≤ x * (C * (r ^ 7 * v ^ 3 + r ^ 4 * s⁻¹ * v ^ 2 + r ^ 4 * E * N)) := by gcongr
      _ = C * (x * (r ^ 7 * v ^ 3) + x * (r ^ 4 * s⁻¹ * v ^ 2) + x * (r ^ 4 * E * N)) := by ring
      _ ≤ C * (s⁻¹ * R + s⁻¹ * R + s⁻¹ * R) := by gcongr
      _ = 3 * C * (s⁻¹ * R) := by ring
      _ ≤ (3 * C + 1) * (s⁻¹ * R) := by nlinarith
      _ = r ^ 3 * s⁻¹ * ((3 * C + 1) * r ^ 4 * (1 + a) ^ 3 * N) := by rw [hR]; ring
  · have e : x * v ^ 2 = a ^ 2 := by rw [hx, ha]; ring
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ x / 2)]
    calc x / 2 * |Q| ≤ x / 2 * (C * r ^ 4 * v ^ 2) := by gcongr
      _ = 1 / 2 * (C * r ^ 4 * (x * v ^ 2)) := by ring
      _ = 1 / 2 * (C * r ^ 4 * a ^ 2) := by rw [e]
      _ ≤ 1 * (C * r ^ 4 * ((1 + a) ^ 3 * N)) := by
        have : a ^ 2 ≤ (1 + a) ^ 3 * N := ha2.trans (le_mul_of_one_le_right (by positivity) hN)
        gcongr
        norm_num
      _ ≤ (3 * C + 1) * r ^ 4 * (1 + a) ^ 3 * N := by
        have : 0 ≤ r ^ 4 * (1 + a) ^ 3 * N := by positivity
        nlinarith
abbrev _root_.YangMills.SharedProofs.p27143 := @scaled_factor_bounds
private theorem abs_prod_sub_prod_le {ι : Type} [DecidableEq ι] (B : Finset ι) (A Z T : ι → ℝ) {ε : ℝ} (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) (hT : ∀ i ∈ B, 0 ≤ T i) (hA : ∀ i ∈ B, |A i - Z i| ≤ ε * T i) (hZ : ∀ i ∈ B, |Z i| ≤ T i) :
    |∏ i ∈ B, A i - ∏ i ∈ B, Z i| ≤ ε * (2 ^ B.card * ∏ i ∈ B, T i) ∧
      ∏ i ∈ B, |A i| ≤ 2 ^ B.card * ∏ i ∈ B, T i := by
  induction B using Finset.induction_on with
  | empty => simpa using h0
  | insert j B hj ih =>
    have ih' := ih (fun i hi => hT i (Finset.mem_insert_of_mem hi)) (fun i hi => hA i (Finset.mem_insert_of_mem hi))
      (fun i hi => hZ i (Finset.mem_insert_of_mem hi))
    have hTj := hT j (Finset.mem_insert_self _ _)
    have hAj := hA j (Finset.mem_insert_self _ _)
    have hZj := hZ j (Finset.mem_insert_self _ _)
    have hAj' : |A j| ≤ 2 * T j := by
      have : |A j| ≤ |A j - Z j| + |Z j| := by
        have := abs_add_le (A j - Z j) (Z j)
        simpa using this
      nlinarith
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.prod_insert hj, Finset.prod_insert hj,
      Finset.card_insert_of_notMem hj]
    constructor
    · have e : A j * ∏ i ∈ B, A i - Z j * ∏ i ∈ B, Z i =
          (A j - Z j) * ∏ i ∈ B, A i + Z j * (∏ i ∈ B, A i - ∏ i ∈ B, Z i) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, Finset.abs_prod]
      have hP : 0 ≤ ∏ i ∈ B, |A i| := Finset.prod_nonneg fun _ _ => abs_nonneg _
      have u1 : |A j - Z j| * ∏ i ∈ B, |A i| ≤ (ε * T j) * (2 ^ B.card * ∏ i ∈ B, T i) :=
        mul_le_mul hAj ih'.2 hP (by positivity)
      have u2 : |Z j| * |∏ i ∈ B, A i - ∏ i ∈ B, Z i| ≤ T j * (ε * (2 ^ B.card * ∏ i ∈ B, T i)) :=
        mul_le_mul hZj ih'.1 (abs_nonneg _) hTj
      calc _ ≤ (ε * T j) * (2 ^ B.card * ∏ i ∈ B, T i) + T j * (ε * (2 ^ B.card * ∏ i ∈ B, T i)) := add_le_add u1 u2
        _ = ε * (2 ^ (B.card + 1) * (T j * ∏ i ∈ B, T i)) := by ring
    · calc |A j| * ∏ i ∈ B, |A i| ≤ (2 * T j) * (2 ^ B.card * ∏ i ∈ B, T i) :=
            mul_le_mul hAj' ih'.2 (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
        _ = 2 ^ (B.card + 1) * (T j * ∏ i ∈ B, T i) := by ring
abbrev _root_.YangMills.SharedProofs.p833 := @abs_prod_sub_prod_le
end Numbers
section Floors
private theorem exists_large_coupling_floor {c : ℝ} (hc : 0 < c) : ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x →
    (clusterRange x : ℝ) ^ 3 * (x ^ ((1 : ℝ) / 2))⁻¹ ≤ 1 ∧
      (x ^ ((1 : ℝ) / 2)) ^ 3 * Real.exp (-(c * (clusterRange x : ℝ) ^ 2)) ≤ 1 := by
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, 8 ≤ x ^ ((47 : ℝ) / 100) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 47 / 100)).eventually_ge_atTop 8
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, |Real.log x| ≤ (2 * c / 3) * |x ^ ((1 : ℝ) / 50)| := by
    have := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 50)).bound (by positivity : 0 < 2 * c / 3)
    simpa using this
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 (e1.and e2)
  refine ⟨max X 1, le_max_right _ _, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  obtain ⟨h8, hl⟩ := hX x ((le_max_left _ _).trans hx)
  have hy1 : 1 ≤ x ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx1 (by norm_num)
  have hrl : x ^ ((1 : ℝ) / 100) ≤ (clusterRange x : ℝ) := Nat.le_ceil _
  have hru : (clusterRange x : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 100) := by
    have := (Nat.ceil_lt_add_one (by positivity : 0 ≤ x ^ ((1 : ℝ) / 100))).le
    unfold clusterRange
    linarith
  have hs0 : 0 < x ^ ((1 : ℝ) / 2) := by positivity
  constructor
  · rw [← div_eq_mul_inv, div_le_one hs0]
    calc (clusterRange x : ℝ) ^ 3 ≤ (2 * x ^ ((1 : ℝ) / 100)) ^ 3 := by gcongr
      _ = 8 * x ^ ((3 : ℝ) / 100) := by
        have e0 : (x ^ ((1 : ℝ) / 100)) ^ 3 = x ^ ((3 : ℝ) / 100) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
          norm_num
        rw [mul_pow, e0]
        norm_num
      _ ≤ x ^ ((47 : ℝ) / 100) * x ^ ((3 : ℝ) / 100) := by gcongr
      _ = x ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hx0]
        norm_num
  · have e3 : (x ^ ((1 : ℝ) / 2)) ^ 3 = Real.exp (3 / 2 * Real.log x) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, Real.rpow_def_of_pos hx0]
      norm_num
      ring_nf
    have e4 : x ^ ((1 : ℝ) / 50) ≤ (clusterRange x : ℝ) ^ 2 := by
      calc x ^ ((1 : ℝ) / 50) = (x ^ ((1 : ℝ) / 100)) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
            norm_num
        _ ≤ (clusterRange x : ℝ) ^ 2 := by gcongr
    rw [e3, ← Real.exp_add]
    apply Real.exp_le_one_iff.2
    have h1 : Real.log x ≤ 2 * c / 3 * x ^ ((1 : ℝ) / 50) := by
      have : 0 ≤ x ^ ((1 : ℝ) / 50) := by positivity
      rw [abs_of_nonneg this] at hl
      exact (le_abs_self _).trans hl
    have h2 : c * x ^ ((1 : ℝ) / 50) ≤ c * (clusterRange x : ℝ) ^ 2 := by gcongr
    nlinarith
abbrev _root_.YangMills.SharedProofs.p37192 := @exists_large_coupling_floor
end Floors
section Point
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem resp_isAdmissible {u : ℕ} (hu : u ≤ S.data.windowLevel) : (S.resp u).IsAdmissible := by apply _root_.YangMills.SharedProofs.p17647 <;> assumption
variable (u n : ℕ) [NeZero n]
private theorem measurable_meanScore (hs : Measurable (S.resp u).score) (i : Fin Λ.k) :
    Measurable fun q : StageState S.tower u n => S.meanScore u n i q := by apply _root_.YangMills.SharedProofs.p9251 <;> assumption
private theorem one_le_meanScore (hs : ∀ w, 0 ≤ (S.resp u).score w) (i : Fin Λ.k) (q : StageState S.tower u n) :
    1 ≤ S.meanScore u n i q := by apply _root_.YangMills.SharedProofs.p166 <;> assumption
end Point
section NumbersOfTheBound
private theorem lead_bound_numeric {x s Yv rr K A₂ c₁ c₂ Cf z p : ℝ} {b : ℕ} (hs : 1 ≤ s) (hxs : x = s ^ 2)
    (hY1 : 1 ≤ Yv) (hr : 1 ≤ rr) (hA₂ : 0 ≤ A₂) (hK : 0 ≤ K) (hz : z ≤ Yv) (hz0 : 0 ≤ z)
    (hterm : (2 * K) ^ b * (|c₁| + A₂) + |c₂| ≤ Cf) (hp : p = (x ^ (b + 1))⁻¹) :
    rr ^ 3 * s⁻¹ * (2 * K * rr ^ 4) ^ b * (|c₁| * z + A₂) + x ^ b * (|c₂| * p) ≤
      Cf * rr ^ (4 * b + 3) * (s⁻¹ * Yv) := by
  have hx0 : 0 < x := by rw [hxs]; positivity
  have hsi0 : 0 ≤ s⁻¹ := by positivity
  have hsi : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  have hrp : 1 ≤ rr ^ (4 * b + 3) := one_le_pow₀ hr
  have t1 : rr ^ 3 * s⁻¹ * (2 * K * rr ^ 4) ^ b * (|c₁| * z + A₂) ≤
      rr ^ (4 * b + 3) * (s⁻¹ * Yv) * ((2 * K) ^ b * (|c₁| + A₂)) := by
    have h1 : |c₁| * z + A₂ ≤ Yv * (|c₁| + A₂) := by
      have u1 : |c₁| * z ≤ |c₁| * Yv := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      have u2 : A₂ ≤ A₂ * Yv := le_mul_of_one_le_right hA₂ hY1
      nlinarith
    calc rr ^ 3 * s⁻¹ * (2 * K * rr ^ 4) ^ b * (|c₁| * z + A₂)
        ≤ rr ^ 3 * s⁻¹ * (2 * K * rr ^ 4) ^ b * (Yv * (|c₁| + A₂)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = rr ^ (4 * b + 3) * (s⁻¹ * Yv) * ((2 * K) ^ b * (|c₁| + A₂)) := by
          rw [mul_pow (2 * K) (rr ^ 4) b]
          ring
  have t2 : x ^ b * (|c₂| * p) ≤ rr ^ (4 * b + 3) * (s⁻¹ * Yv) * |c₂| := by
    have e : x ^ b * (|c₂| * p) = s⁻¹ * s⁻¹ * |c₂| := by
      rw [hp, pow_succ, mul_inv, hxs]
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have w1 : s⁻¹ * s⁻¹ ≤ s⁻¹ := mul_le_of_le_one_left hsi0 hsi
    have w2 : s⁻¹ ≤ s⁻¹ * Yv := le_mul_of_one_le_right hsi0 hY1
    have w3 : s⁻¹ * Yv ≤ rr ^ (4 * b + 3) * (s⁻¹ * Yv) := le_mul_of_one_le_left (by positivity) hrp
    linarith
  calc _ ≤ rr ^ (4 * b + 3) * (s⁻¹ * Yv) * ((2 * K) ^ b * (|c₁| + A₂)) + rr ^ (4 * b + 3) * (s⁻¹ * Yv) * |c₂| :=
        add_le_add t1 t2
    _ = rr ^ (4 * b + 3) * (s⁻¹ * Yv) * ((2 * K) ^ b * (|c₁| + A₂) + |c₂|) := by ring
    _ ≤ rr ^ (4 * b + 3) * (s⁻¹ * Yv) * Cf := mul_le_mul_of_nonneg_left hterm (by positivity)
    _ = Cf * rr ^ (4 * b + 3) * (s⁻¹ * Yv) := by ring
abbrev _root_.YangMills.SharedProofs.p55882 := @lead_bound_numeric
private theorem chain_bound_numeric {x r N Lq cO cM cM1 g1 g5 g g' : ℝ} {b : ℕ} (hb : b ≤ 8) (hx : 1 ≤ x) (hr : 1 ≤ r)
    (hN0 : 0 ≤ N) (hN : N ≤ 6000 * x ^ ((3 : ℝ) / 4000)) (hL0 : 0 ≤ Lq) (hL : Lq ≤ x⁻¹) (hcO : 0 ≤ cO) (hcM : 0 ≤ cM)
    (hcM1 : 0 ≤ cM1) (hg1 : 0 ≤ g1) (hg5 : 0 ≤ g5) (hg : 0 ≤ g) (hg' : 0 ≤ g') :
    N * (cO * r ^ (4 * b + 2) * x ^ (-(1 / 2) : ℝ) * (g1 * x ^ ((1 : ℝ) / 4000)) +
        cM * r ^ (4 * b) * (121 ^ 16 * x ^ 4) * (g5 * x ^ (-((5 : ℕ) : ℝ)))) +
      (cM * r ^ (4 * b) * Lq * (1 + 120 * (1 + g * x ^ ((1 : ℝ) / 4000))) ^ (2 * b) +
        cM * r ^ (4 * b) * (g' * x ^ (-((1 : ℕ) : ℝ)))) + cM1 * r ^ (4 * b) * Lq ≤
    (6000 * cO * g1 + 6000 * cM * 121 ^ 16 * g5 + cM * (121 + 120 * g) ^ 16 + cM * g' + cM1) *
      (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hR : ∀ {j : ℕ} {p : ℝ}, j ≤ 4 * b + 3 → p ≤ (-(1 / 2) + 1 / 1000 : ℝ) →
      r ^ j * x ^ p ≤ r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ) := fun hj hp =>
    mul_le_mul (pow_le_pow_right₀ hr hj) (Real.rpow_le_rpow_of_exponent_le hx hp) (by positivity) (by positivity)
  have hxi : x⁻¹ = x ^ (-1 : ℝ) := (Real.rpow_neg_one x).symm
  have t1 : N * (cO * r ^ (4 * b + 2) * x ^ (-(1 / 2) : ℝ) * (g1 * x ^ ((1 : ℝ) / 4000))) ≤
      6000 * cO * g1 * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) := by
    calc N * (cO * r ^ (4 * b + 2) * x ^ (-(1 / 2) : ℝ) * (g1 * x ^ ((1 : ℝ) / 4000)))
        ≤ 6000 * x ^ ((3 : ℝ) / 4000) * (cO * r ^ (4 * b + 2) * x ^ (-(1 / 2) : ℝ) * (g1 * x ^ ((1 : ℝ) / 4000))) :=
          mul_le_mul_of_nonneg_right hN (by positivity)
      _ = 6000 * cO * g1 * (r ^ (4 * b + 2) * (x ^ ((3 : ℝ) / 4000) * x ^ (-(1 / 2) : ℝ) * x ^ ((1 : ℝ) / 4000))) := by
          ring
      _ = 6000 * cO * g1 * (r ^ (4 * b + 2) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
          norm_num
      _ ≤ 6000 * cO * g1 * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hR (by omega) le_rfl) (by positivity)
  have t2 : N * (cM * r ^ (4 * b) * (121 ^ 16 * x ^ 4) * (g5 * x ^ (-((5 : ℕ) : ℝ)))) ≤
      6000 * cM * 121 ^ 16 * g5 * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) := by
    calc N * (cM * r ^ (4 * b) * (121 ^ 16 * x ^ 4) * (g5 * x ^ (-((5 : ℕ) : ℝ))))
        ≤ 6000 * x ^ ((3 : ℝ) / 4000) * (cM * r ^ (4 * b) * (121 ^ 16 * x ^ 4) * (g5 * x ^ (-((5 : ℕ) : ℝ)))) :=
          mul_le_mul_of_nonneg_right hN (by positivity)
      _ = 6000 * cM * 121 ^ 16 * g5 *
            (r ^ (4 * b) * (x ^ ((3 : ℝ) / 4000) * ((x ^ ((4 : ℕ) : ℝ)) * x ^ (-((5 : ℕ) : ℝ))))) := by
          rw [Real.rpow_natCast]
          ring
      _ = 6000 * cM * 121 ^ 16 * g5 *
            (r ^ (4 * b) * x ^ ((3 : ℝ) / 4000 + (((4 : ℕ) : ℝ) + -((5 : ℕ) : ℝ)))) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      _ ≤ 6000 * cM * 121 ^ 16 * g5 * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hR (by omega) (by norm_num)) (by positivity)
  have hxe : 1 ≤ x ^ ((1 : ℝ) / 4000) := Real.one_le_rpow hx (by norm_num)
  have hY0 : 0 ≤ 1 + 120 * (1 + g * x ^ ((1 : ℝ) / 4000)) := by positivity
  have hY : (1 + 120 * (1 + g * x ^ ((1 : ℝ) / 4000))) ^ (2 * b) ≤
      (121 + 120 * g) ^ 16 * x ^ ((16 : ℝ) / 4000) := by
    have h1 : 1 + 120 * (1 + g * x ^ ((1 : ℝ) / 4000)) ≤ (121 + 120 * g) * x ^ ((1 : ℝ) / 4000) := by nlinarith
    have h2 : 1 ≤ (121 + 120 * g) * x ^ ((1 : ℝ) / 4000) := by nlinarith
    calc (1 + 120 * (1 + g * x ^ ((1 : ℝ) / 4000))) ^ (2 * b) ≤
          ((121 + 120 * g) * x ^ ((1 : ℝ) / 4000)) ^ (2 * b) :=
          pow_le_pow_left₀ hY0 h1 _
      _ ≤ ((121 + 120 * g) * x ^ ((1 : ℝ) / 4000)) ^ 16 := pow_le_pow_right₀ h2 (by omega)
      _ = (121 + 120 * g) ^ 16 * x ^ ((16 : ℝ) / 4000) := by
          rw [mul_pow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 4000)), ← Real.rpow_mul hx0.le]
          norm_num
  have t3 : cM * r ^ (4 * b) * Lq * (1 + 120 * (1 + g * x ^ ((1 : ℝ) / 4000))) ^ (2 * b) ≤
      cM * (121 + 120 * g) ^ 16 * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) := by
    calc cM * r ^ (4 * b) * Lq * (1 + 120 * (1 + g * x ^ ((1 : ℝ) / 4000))) ^ (2 * b)
        ≤ cM * r ^ (4 * b) * x⁻¹ * ((121 + 120 * g) ^ 16 * x ^ ((16 : ℝ) / 4000)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hL (by positivity)) hY (by positivity) (by positivity)
      _ = cM * (121 + 120 * g) ^ 16 * (r ^ (4 * b) * (x ^ (-1 : ℝ) * x ^ ((16 : ℝ) / 4000))) := by
          rw [hxi]
          ring
      _ = cM * (121 + 120 * g) ^ 16 * (r ^ (4 * b) * x ^ ((-1 : ℝ) + 16 / 4000)) := by rw [← Real.rpow_add hx0]
      _ ≤ cM * (121 + 120 * g) ^ 16 * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hR (by omega) (by norm_num)) (by positivity)
  have t4 : cM * r ^ (4 * b) * (g' * x ^ (-((1 : ℕ) : ℝ))) ≤
      cM * g' * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) := by
    calc cM * r ^ (4 * b) * (g' * x ^ (-((1 : ℕ) : ℝ))) = cM * g' * (r ^ (4 * b) * x ^ (-((1 : ℕ) : ℝ))) := by ring
      _ ≤ cM * g' * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hR (by omega) (by norm_num)) (by positivity)
  have t5 : cM1 * r ^ (4 * b) * Lq ≤ cM1 * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) := by
    calc cM1 * r ^ (4 * b) * Lq ≤ cM1 * r ^ (4 * b) * x ^ (-1 : ℝ) :=
          mul_le_mul_of_nonneg_left (hxi ▸ hL) (by positivity)
      _ = cM1 * (r ^ (4 * b) * x ^ (-1 : ℝ)) := by ring
      _ ≤ cM1 * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hR (by omega) (by norm_num)) hcM1
  calc _ = N * (cO * r ^ (4 * b + 2) * x ^ (-(1 / 2) : ℝ) * (g1 * x ^ ((1 : ℝ) / 4000))) +
        N * (cM * r ^ (4 * b) * (121 ^ 16 * x ^ 4) * (g5 * x ^ (-((5 : ℕ) : ℝ)))) +
        cM * r ^ (4 * b) * Lq * (1 + 120 * (1 + g * x ^ ((1 : ℝ) / 4000))) ^ (2 * b) +
        cM * r ^ (4 * b) * (g' * x ^ (-((1 : ℕ) : ℝ))) + cM1 * r ^ (4 * b) * Lq := by ring
    _ ≤ 6000 * cO * g1 * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) +
        6000 * cM * 121 ^ 16 * g5 * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) +
        cM * (121 + 120 * g) ^ 16 * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) +
        cM * g' * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) +
        cM1 * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) :=
        add_le_add (add_le_add (add_le_add (add_le_add t1 t2) t3) t4) t5
    _ = _ := by ring
abbrev _root_.YangMills.SharedProofs.p8611 := @chain_bound_numeric
private theorem natCeil_four_log_le {x : ℝ} (hx : 1 ≤ x) :
    ((⌈4 * Real.log x⌉₊ : ℕ) : ℝ) ≤ 6000 * x ^ ((3 : ℝ) / 4000) := by
  have hx0 : 0 ≤ x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 := Nat.ceil_lt_add_one (show 0 ≤ 4 * Real.log x by positivity)
  have h2 := Real.log_le_rpow_div hx0 (show (0 : ℝ) < 3 / 4000 by norm_num)
  have h3 : (1 : ℝ) ≤ x ^ ((3 : ℝ) / 4000) := Real.one_le_rpow hx (by norm_num)
  linarith
abbrev _root_.YangMills.SharedProofs.p23711 := @natCeil_four_log_le
end NumbersOfTheBound
section CondExp
variable {Ω : Type} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
private theorem abs_condExp_le {f g : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P) (h : ∀ᵐ w ∂P, |f w| ≤ g w) :
    ∀ᵐ w ∂P, |(P[f|m]) w| ≤ (P[g|m]) w := by
  have h1 : P[f|m] ≤ᵐ[P] P[g|m] := condExp_mono hf hg (h.mono fun w hw => (le_abs_self _).trans hw)
  have h2 : P[-f|m] ≤ᵐ[P] P[g|m] := condExp_mono hf.neg hg (h.mono fun w hw => (neg_le_abs _).trans hw)
  have h3 : P[-f|m] =ᵐ[P] -P[f|m] := condExp_neg f m
  filter_upwards [h1, h2, h3] with w a b c
  rw [c] at b
  have b' : -(P[f|m]) w ≤ (P[g|m]) w := b
  exact abs_le.2 ⟨by linarith, a⟩
private theorem condExp_add_fun {f g : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P) :
    P[fun w => f w + g w|m] =ᵐ[P] fun w => (P[f|m]) w + (P[g|m]) w := condExp_add hf hg m
private theorem condExp_sub_fun {f g : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P) :
    P[fun w => f w - g w|m] =ᵐ[P] fun w => (P[f|m]) w - (P[g|m]) w := condExp_sub hf hg m
private theorem condExp_const_mul_fun (c : ℝ) (f : Ω → ℝ) : P[fun w => c * f w|m] =ᵐ[P] fun w => c * (P[f|m]) w :=
  condExp_smul c f m
private theorem abs_sub_le_of_steps {D : ℕ → ℝ} {N : ℕ} {e : ℝ} (h : ∀ d, d < N → |D d - D (d + 1)| ≤ e) (he : 0 ≤ e) :
    |D 0 - D N| ≤ N * e := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h1 := ih fun d hd => h d (by omega)
    have h2 := h N (by omega)
    have h3 := abs_sub_le (D 0) (D N) (D (N + 1))
    push_cast
    linarith
private theorem condExp_window_chain (hm : m ≤ mΩ) [IsProbabilityMeasure P] {N : ℕ} {R T₂ Ya Yb Yt Gt : Ω → ℝ}
    {H E Yc G : ℕ → Ω → ℝ} {xb e a₁ Co M c₂ c₃ c₄ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : ℝ}
    (hR : Integrable R P) (hT₂ : Integrable T₂ P) (hYa : Integrable Ya P) (hYb : Integrable Yb P) (hYt : Integrable Yt P)
    (hGt : Integrable Gt P) (hH : ∀ d, d ≤ N → Integrable (H d) P) (hE : ∀ d, d < N → Integrable (E d) P)
    (hYc : ∀ d, d < N → Integrable (Yc d) P) (hG : ∀ d, d < N → Integrable (G d) P)
    (ha₁ : 0 ≤ a₁) (hxb : 0 ≤ xb) (hCo : 0 ≤ Co) (hM : 0 ≤ M) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (lead : ∀ᵐ w ∂P, |xb * R w - H 0 w| ≤ a₁ * (Ya w + Yb w) + xb * T₂ w)
    (step : ∀ d, d < N → ∀ᵐ w ∂P, |E d w - H (d + 1) w| ≤ Co * Yc d w + M * G d w)
    (top : ∀ᵐ w ∂P, |H N w - e| ≤ c₂ * Yt w + c₃ * Gt w + c₄)
    (star : ∀ d, d < N → P[H d|m] =ᵐ[P] P[E d|m])
    (b₁ : ∀ᵐ w ∂P, (P[Ya|m]) w ≤ A₁) (b₂ : ∀ᵐ w ∂P, (P[Yb|m]) w ≤ A₂) (b₃ : ∀ᵐ w ∂P, (P[T₂|m]) w ≤ A₃)
    (b₄ : ∀ d, d < N → ∀ᵐ w ∂P, (P[Yc d|m]) w ≤ A₄) (b₅ : ∀ d, d < N → ∀ᵐ w ∂P, (P[G d|m]) w ≤ A₅)
    (b₆ : ∀ᵐ w ∂P, (P[Yt|m]) w ≤ A₆) (b₇ : ∀ᵐ w ∂P, (P[Gt|m]) w ≤ A₇) (hA : 0 ≤ Co * A₄ + M * A₅) :
    ∀ᵐ w ∂P, |xb * (P[R|m]) w - e| ≤
      a₁ * (A₁ + A₂) + xb * A₃ + N * (Co * A₄ + M * A₅) + (c₂ * A₆ + c₃ * A₇ + c₄) := by
  have L1 : ∀ᵐ w ∂P, |xb * (P[R|m]) w - (P[H 0|m]) w| ≤ a₁ * (A₁ + A₂) + xb * A₃ := by
    have i1 : Integrable (fun w => xb * R w - H 0 w) P := (hR.const_mul _).sub (hH 0 (Nat.zero_le _))
    have i2 : Integrable (fun w => a₁ * (Ya w + Yb w)) P := (hYa.add hYb).const_mul _
    have i3 : Integrable (fun w => xb * T₂ w) P := hT₂.const_mul _
    have i23 : Integrable (fun w => a₁ * (Ya w + Yb w) + xb * T₂ w) P := i2.add i3
    have k := abs_condExp_le (m := m) i1 i23 lead
    have e1 : P[fun w => xb * R w - H 0 w|m] =ᵐ[P] fun w => xb * (P[R|m]) w - (P[H 0|m]) w :=
      (condExp_sub_fun (hR.const_mul _) (hH 0 (Nat.zero_le _))).trans (by
        filter_upwards [condExp_const_mul_fun (m := m) (P := P) xb R] with w hw
        rw [hw])
    have e2 : P[fun w => a₁ * (Ya w + Yb w) + xb * T₂ w|m] =ᵐ[P]
        fun w => a₁ * ((P[Ya|m]) w + (P[Yb|m]) w) + xb * (P[T₂|m]) w := by
      filter_upwards [condExp_add_fun (m := m) i2 i3, condExp_const_mul_fun (m := m) (P := P) a₁ (fun w => Ya w + Yb w),
        condExp_add_fun (m := m) hYa hYb, condExp_const_mul_fun (m := m) (P := P) xb T₂] with w p1 p2 p3 p4
      rw [p1, p2, p3, p4]
    filter_upwards [k, e1, e2, b₁, b₂, b₃] with w k1 k2 k3 q1 q2 q3
    rw [k2, k3] at k1
    refine k1.trans ?_
    gcongr
  have L2 : ∀ d, d < N → ∀ᵐ w ∂P, |(P[H d|m]) w - (P[H (d + 1)|m]) w| ≤ Co * A₄ + M * A₅ := by
    intro d hd
    have i1 : Integrable (fun w => E d w - H (d + 1) w) P := (hE d hd).sub (hH (d + 1) hd)
    have i2 : Integrable (fun w => Co * Yc d w) P := (hYc d hd).const_mul _
    have i3 : Integrable (fun w => M * G d w) P := (hG d hd).const_mul _
    have i23 : Integrable (fun w => Co * Yc d w + M * G d w) P := i2.add i3
    have k := abs_condExp_le (m := m) i1 i23 (step d hd)
    filter_upwards [k, condExp_sub_fun (m := m) (hE d hd) (hH (d + 1) hd), condExp_add_fun (m := m) i2 i3,
      condExp_const_mul_fun (m := m) (P := P) Co (Yc d), condExp_const_mul_fun (m := m) (P := P) M (G d), star d hd,
      b₄ d hd, b₅ d hd] with w k1 k2 k3 k4 k5 k6 q1 q2
    rw [k2, k3, k4, k5, ← k6] at k1
    refine k1.trans ?_
    gcongr
  have L3 : ∀ᵐ w ∂P, |(P[H N|m]) w - e| ≤ c₂ * A₆ + c₃ * A₇ + c₄ := by
    have iH := hH N le_rfl
    have iC : Integrable (fun _ : Ω => e) P := integrable_const _
    have iD : Integrable (fun _ : Ω => c₄) P := integrable_const _
    have i1 : Integrable (fun w => H N w - e) P := iH.sub iC
    have i2 : Integrable (fun w => c₂ * Yt w) P := hYt.const_mul _
    have i3 : Integrable (fun w => c₃ * Gt w) P := hGt.const_mul _
    have i23 : Integrable (fun w => c₂ * Yt w + c₃ * Gt w) P := i2.add i3
    have i4 : Integrable (fun w => c₂ * Yt w + c₃ * Gt w + c₄) P := i23.add iD
    have k := abs_condExp_le (m := m) i1 i4 top
    have ce : P[fun _ : Ω => e|m] = fun _ => e := condExp_const hm e
    have cd : P[fun _ : Ω => c₄|m] = fun _ => c₄ := condExp_const hm c₄
    filter_upwards [k, condExp_sub_fun (m := m) iH iC, condExp_add_fun (m := m) i23 iD, condExp_add_fun (m := m) i2 i3,
      condExp_const_mul_fun (m := m) (P := P) c₂ Yt, condExp_const_mul_fun (m := m) (P := P) c₃ Gt, b₆, b₇]
      with w k1 k2 k3 k4 k5 k6 q1 q2
    rw [k2, k3, k4, k5, k6, ce, cd] at k1
    refine k1.trans ?_
    gcongr
  have L2' : ∀ᵐ w ∂P, ∀ d, d < N → |(P[H d|m]) w - (P[H (d + 1)|m]) w| ≤ Co * A₄ + M * A₅ := by
    rw [ae_all_iff]
    intro d
    by_cases hd : d < N
    · filter_upwards [L2 d hd] with w hw _ using hw
    · exact ae_of_all _ fun _ h => absurd h hd
  filter_upwards [L1, L2', L3] with w l1 l2 l3
  have l4 := abs_sub_le_of_steps (D := fun d => (P[H d|m]) w) l2 hA
  have t1 : |xb * (P[R|m]) w - e| ≤ |xb * (P[R|m]) w - (P[H 0|m]) w| + |(P[H 0|m]) w - (P[H N|m]) w| +
      |(P[H N|m]) w - e| := by
    have u1 := abs_sub_le (xb * (P[R|m]) w) ((P[H 0|m]) w) e
    have u2 := abs_sub_le ((P[H 0|m]) w) ((P[H N|m]) w) e
    linarith
  linarith
end CondExp
section Limits
variable {T : TranslatedLaws} {J : Type} {X : J → T.Family} {P : Measure (TranslateValues J)}
private theorem ae_eq_zero_of_limit (hX : IsJointLimitLaw T X P) {l : ℕ} (a : Fin l → J) (G : (Fin l → ℝ) → ℝ)
    (hG : Continuous G) (hG0 : ∀ w, 0 ≤ G w) (h : ∀ᶠ i in atTop, ∀ᵐ ω ∂(T.μ i), G (fun c => X (a c) i ω) = 0) :
    ∀ᵐ v ∂P, G (fun c => v (a c, 0)) = 0 := by apply _root_.YangMills.SharedProofs.p3582 <;> assumption
private theorem ae_le_of_limit (hX : IsJointLimitLaw T X P) {l : ℕ} (a : Fin l → J) (A C : (Fin l → ℝ) → ℝ)
    (hA : Continuous A) (hC : Continuous C)
    (h : ∀ᶠ i in atTop, ∀ᵐ ω ∂(T.μ i), A (fun c => X (a c) i ω) ≤ C (fun c => X (a c) i ω)) :
    ∀ᵐ v ∂P, A (fun c => v (a c, 0)) ≤ C (fun c => v (a c, 0)) := by apply _root_.YangMills.SharedProofs.p29837 <;> assumption
end Limits
section Samples
variable {ℓ : TorusLumps.StepParameters}
private theorem heq_fst_of_heq {K₁ K₂ n : ℕ} (h : K₁ = K₂) (w₁ : MarkedSample ℓ (K₁ + 1) n)
    (w₂ : MarkedSample ℓ (K₂ + 1) n) (e : HEq w₁ w₂) : HEq w₁.1 w₂.1 := by
  subst h
  rw [eq_of_heq e]
private theorem sampleBelow_fst_heq (u : ℕ) : ∀ (d n : ℕ) (w₁ : MarkedSample ℓ (u + 1 + d) n)
    (w₂ : MarkedSample ℓ (u + (d + 1)) n), HEq w₁ w₂ →
    fineSide ℓ.side d n * ℓ.side = fineSide ℓ.side (d + 1) n ∧
      HEq (sampleBelow ℓ (u + 1) d n w₁).1 (sampleBelow ℓ u (d + 1) n w₂) := by
  intro d
  induction d with
  | zero =>
    intro n w₁ w₂ e
    refine ⟨rfl, ?_⟩
    have e' : w₁ = w₂ := eq_of_heq e
    subst e'
    exact HEq.rfl
  | succ d ih =>
    intro n w₁ w₂ e
    exact ih (n * ℓ.side) w₁.1 w₂.1 (heq_fst_of_heq (by show u + 1 + d = u + (d + 1); omega) w₁ w₂ e)
abbrev _root_.YangMills.SharedProofs.p2695 := @sampleBelow_fst_heq
private theorem cast_heq_sample {K K' n : ℕ} (h : K = K') (w : MarkedSample ℓ K n) :
    HEq (h ▸ w : MarkedSample ℓ K' n) w := by
  subst h
  exact HEq.rfl
private theorem sampleBelow_cast_heq (u K n : ℕ) (w : MarkedSample ℓ K n) {d₁ d₂ : ℕ} (h₁ : K = u + 1 + d₁)
    (h₂ : K = u + d₂) (hd : d₂ = d₁ + 1) :
    fineSide ℓ.side d₁ n * ℓ.side = fineSide ℓ.side d₂ n ∧
      HEq (sampleBelow ℓ (u + 1) d₁ n (h₁ ▸ w)).1 (sampleBelow ℓ u d₂ n (h₂ ▸ w)) := by
  subst hd
  exact sampleBelow_fst_heq u d₁ n _ _ ((cast_heq_sample h₁ w).trans (cast_heq_sample h₂ w).symm)
private theorem map_cast_markedSampleLaw (T : StageTower ℓ) (β : ℝ) {K K' : ℕ} (h : K = K') (n : ℕ) [NeZero n] :
    Measurable (fun w : MarkedSample ℓ K n => (h ▸ w : MarkedSample ℓ K' n)) ∧
      (markedSampleLaw T β K n).map (fun w : MarkedSample ℓ K n => (h ▸ w : MarkedSample ℓ K' n)) =
        markedSampleLaw T β K' n := by
  subst h
  exact ⟨measurable_id, Measure.map_id⟩
end Samples
section Window
variable {Λ : MomentParameters}
open Classical in
private def formMeanObs (t d : ℕ) (B : Finset (Fin Λ.k)) : SampleObservable Λ :=
  levelObservable (t + d) fun S q => if S.IsGoodConfig (t + d) (S.sideAtLevel (t + d)) q.1 q.2.1 then
    S.formProductMean d (S.sideAtLevel (t + d)) B (S.cutoffColourForm (t + d) (S.sideAtLevel (t + d)) q.1) else 0
private def liftObs (t d : ℕ) (B : Finset (Fin Λ.k)) : SampleObservable Λ := fun S w =>
  if h : t + d + 1 ≤ S.data.windowLevel then
    FreeEnergies.caseLift S.tower (t + d) (S.sideAtLevel (t + d + 1))
      (fun _ => S.goodCaseForms (t + d) d (S.sideAtLevel (t + d + 1)) B) (S.sampleAtLevel (t + d + 1) h w)
  else 0
private def caseMeanObs (t d : ℕ) (B : Finset (Fin Λ.k)) : SampleObservable Λ := fun S w =>
  if h : t + d + 1 ≤ S.data.windowLevel then
    FreeEnergies.caseMeanAtSample S.tower (t + d) (S.sideAtLevel (t + d + 1))
      (fun _ => S.goodCaseForms (t + d) d (S.sideAtLevel (t + d + 1)) B) (S.sampleAtLevel (t + d + 1) h w)
  else 0
private def oneObs : SampleObservable Λ := fun _ _ => 1
private structure PointBounds (S : MomentPoint Λ) (CM CM1 CO C₀ cE : ℝ) : Prop where
  admissible : Λ.stepParams.Admissible
  k_le : Λ.k ≤ 8
  one_le_coupling : 1 ≤ S.scaleCoupling
  window : S.lastSeparated + 2 * S.logIndex + 3 ≤ S.data.windowLevel
  decay_le : (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) ≤ S.scaleCoupling⁻¹
  log_measurable : MeasurableQuaternion (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]))
  stage_measurable : ∀ (u n : ℕ) [NeZero n], Measurable (stageState S.tower u n)
  isProbability : ∀ (u n : ℕ) [NeZero n], IsProbabilityMeasure (S.law u n)
  sampleBelow_map : ∀ (s d n : ℕ) [NeZero n], Measurable (sampleBelow Λ.stepParams s d n) ∧
    Measure.map (sampleBelow Λ.stepParams s d n) (markedSampleLaw S.tower S.β (s + d) n) =
      markedSampleLaw S.tower S.β s (fineSide Λ.stepParams.side d n)
  cutoff_measurable : cutoffMeasurableStatement
  means : ∀ (d n : ℕ) [NeZero n], d ≤ S.logIndex + 1 → n = S.levelSide (S.lastSeparated + d) →
      ∀ (B : Finset (Fin Λ.k)) (Ω : Type) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (A A' : Ω → ColourForm n), Measurable A → Measurable A' →
      ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w)| ∂μ ≤
        ENNReal.ofReal (CM * (S.range : ℝ) ^ (4 * B.card)) * (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A +
            weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A')) ^ (2 * B.card) ∧
      ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w) - S.formProductMean d n B 0| ∂μ ≤
        ENNReal.ofReal (CM * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(d : ℝ) / 4)) *
          (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A +
            weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A')) ^ (2 * B.card)
  chain : ∀ (N d n : ℕ) [NeZero n], S.lastSeparated + d = S.data.windowLevel → N ≤ d →
      n = S.levelSide (S.lastSeparated + N) →
      ∀ μ : Measure (LevelChain Λ.stepParams.side (S.lastSeparated + d) (S.data.period Λ.stepParams.side)),
      IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling (S.lastSeparated + d) (S.data.period Λ.stepParams.side)) μ →
      ∀ B : Finset (Fin Λ.k), |S.formProductMean N n B 0 -
          ∫ X, ∏ i ∈ B, S.halfForm d (S.data.period Λ.stepParams.side) i X ∂μ| ≤
        CM1 * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(N : ℝ) / 4)
  zero : ∀ (n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)) (A : ColourForm n),
    S.formProductMean 0 n B A = S.formProduct S.lastSeparated n B A
  one_step : ∀ (d n : ℕ) [NeZero n], d < S.logIndex → n = S.levelSide (S.lastSeparated + d + 1) →
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
          (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature (S.lastSeparated + d + 1) n V) ^ (2 * B.card + 1)
  cutoff : ∀ u, S.lastSeparated ≤ u → u ≤ S.lastSeparated + 2 * S.logIndex + 3 → ∀ (n : ℕ) [NeZero n],
      n = S.levelSide u → ∀ (W : TorusField n) (Y : Finset (TorusSite n)),
      S.IsGoodConfig u n W Y → ∀ p : OrientedPlaquette n,
        curlNorm (S.cutoffColourForm u n W) p.1 ≤ 60 * S.localCurvature u n W
  near : ∀ (i : Fin Λ.k) (q : StageState S.tower S.lastSeparated (S.levelSide S.lastSeparated)),
    IsLiveState Λ.stepParams (S.tower.stage S.lastSeparated).coupling (S.tower.stage S.lastSeparated).labelWeight
      q.1 q.2.1 q.2.2 → S.IsGoodConfig S.lastSeparated (S.levelSide S.lastSeparated) q.1 q.2.1 →
    |S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i q -
        1 / 2 * colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i)
          (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) q.1)
          (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) q.1)| ≤
      C₀ * ((S.range : ℝ) ^ 7 * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 3 +
        (S.range : ℝ) ^ 4 * S.scaleCoupling ^ (-(1 / 2) : ℝ) *
          S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 2 +
        (S.range : ℝ) ^ 4 * Real.exp (-(cE * (S.range : ℝ) ^ 2)) *
          S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i q) ∧
    |colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i)
        (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) q.1)
        (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) q.1)| ≤
      C₀ * (S.range : ℝ) ^ 4 * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 2
  live : ∀ u ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide Λ.stepParams n → ∀ᵐ w ∂(S.law u n),
    IsLiveState Λ.stepParams (S.tower.stage u).coupling (S.tower.stage u).labelWeight
      (S.state u n w).1 (S.state u n w).2.1 (S.state u n w).2.2
  condMean_eq : ∀ u, u + 2 ≤ S.data.windowLevel →
      ∀ F : TorusField (S.levelSide (u + 1)) → CaseFunction (S.tower.stage u).toStepSetup (S.levelSide (u + 1)),
      Measurable (caseLiftOf S.tower u (S.levelSide (u + 1)) F) →
      (∃ C : ℝ, ∀ z, |caseLiftOf S.tower u (S.levelSide (u + 1)) F z| ≤ C) →
      (S.law (u + 1) (S.levelSide (u + 1)))[caseLiftOf S.tower u (S.levelSide (u + 1)) F |
        stageSigma S.tower (u + 1) (S.levelSide (u + 1))]
        =ᵐ[S.law (u + 1) (S.levelSide (u + 1))]
        fun z => caseMean (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup z.2.2.1) z.2.2.1
          (stageState S.tower (u + 1) (S.levelSide (u + 1)) z).2 (F z.2.2.1)
  weight_nonneg : ∀ u, u + 2 ≤ S.data.windowLevel →
      ∀ (C : Finset (TorusSite (S.levelSide (u + 1)))) (V : TorusField (S.levelSide (u + 1))) W Yt ωt bad b,
      0 ≤ stepWeight (S.tower.stage u).toStepSetup C V W Yt ωt bad b
namespace MomentPoint
variable (S : MomentPoint Λ) {CM CM1 CO C₀ cE : ℝ}
private theorem sideAtLevel_eq (u : ℕ) : S.sideAtLevel u = S.levelSide u := by apply _root_.YangMills.SharedProofs.p7138 <;> assumption
private theorem sampleAtLevel_map (h : PointBounds S CM CM1 CO C₀ cE) (u : ℕ) (hu : u ≤ S.data.windowLevel) :
    Measurable (S.sampleAtLevel u hu) ∧
      (S.law S.data.windowLevel (S.data.period Λ.stepParams.side)).map (S.sampleAtLevel u hu) =
        S.law u (S.sideAtLevel u) := by
  have hc := map_cast_markedSampleLaw S.tower S.β (Nat.add_sub_of_le hu).symm (S.data.period Λ.stepParams.side)
  obtain ⟨m1, e1⟩ := h.sampleBelow_map u (S.data.windowLevel - u) (S.data.period Λ.stepParams.side)
  refine ⟨m1.comp hc.1, ?_⟩
  have e2 := Measure.map_map (μ := markedSampleLaw S.tower S.β S.data.windowLevel (S.data.period Λ.stepParams.side))
    m1 hc.1
  rw [hc.2, e1] at e2
  exact e2.symm
private theorem ae_of_sampleAtLevel (h : PointBounds S CM CM1 CO C₀ cE) (u : ℕ) (hu : u ≤ S.data.windowLevel)
    {p : MarkedSample Λ.stepParams u (S.sideAtLevel u) → Prop}
    (hp : ∀ᵐ x ∂(S.law u (S.sideAtLevel u)), p x) :
    ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)), p (S.sampleAtLevel u hu w) := by
  obtain ⟨m1, e1⟩ := S.sampleAtLevel_map h u hu
  rw [← e1] at hp
  exact ae_of_ae_map m1.aemeasurable hp
private theorem sampleAtLevel_succ_fst (u : ℕ) (h1 : u + 1 ≤ S.data.windowLevel) (h0 : u ≤ S.data.windowLevel)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    S.sideAtLevel (u + 1) * Λ.stepParams.side = S.sideAtLevel u ∧
      HEq (S.sampleAtLevel (u + 1) h1 w).1 (S.sampleAtLevel u h0 w) := by
  exact sampleBelow_cast_heq u S.data.windowLevel (S.data.period Λ.stepParams.side) w (Nat.add_sub_of_le h1).symm
    (Nat.add_sub_of_le h0).symm (by omega)
end MomentPoint
end Window
section Bounds
variable {Λ : MomentParameters}
private theorem le_of_dirac_bound {n : ℕ} [NeZero n] {ω : TorusPlaquette n → ℝ} (hω : ∀ p, ω p ≤ 1) {q : ENNReal}
    (hq : q ≠ 0) {Φ c sx v : ℝ} {k : ℕ}
    (X : ColourForm n) (hv : 0 ≤ v) (hX : ∀ p : OrientedPlaquette n, curlNorm X p.1 ≤ 60 * v) (hs : 0 ≤ sx)
    (hΦ : 0 ≤ Φ)
    (h : ENNReal.ofReal Φ ≤ ENNReal.ofReal c * (1 + ENNReal.ofReal sx *
      (weightedCurvatureNorm (Measure.dirac ()) ω q (fun _ : Unit => X) +
        weightedCurvatureNorm (Measure.dirac ()) ω q (fun _ : Unit => X))) ^ k) :
    Φ ≤ |c| * (1 + 120 * sx * v) ^ k := by
  have hc : weightedCurvatureNorm (Measure.dirac ()) ω q (fun _ : Unit => X) ≤ ENNReal.ofReal (60 * v) := by
    refine (weightedCurvatureNorm_le_eLpNorm _ hω _ _ (fun _ => 60 * v) (fun _ p => hX p)).trans ?_
    rw [eLpNorm_const _ hq (by simp)]
    simp [Real.enorm_of_nonneg (show (0 : ℝ) ≤ 60 * v by positivity)]
  have h2 : (1 + ENNReal.ofReal sx *
      (weightedCurvatureNorm (Measure.dirac ()) ω q (fun _ : Unit => X) +
        weightedCurvatureNorm (Measure.dirac ()) ω q (fun _ : Unit => X))) ≤
      ENNReal.ofReal (1 + 120 * sx * v) := by
    have e : (1 + 120 * sx * v) = 1 + sx * (60 * v + 60 * v) := by ring
    rw [e, ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_mul hs,
      ENNReal.ofReal_add (by positivity) (by positivity)]
    gcongr
  have hY0 : 0 ≤ 1 + 120 * sx * v := by positivity
  have h3 : ENNReal.ofReal Φ ≤ ENNReal.ofReal (|c| * (1 + 120 * sx * v) ^ k) := by
    refine h.trans ?_
    rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_pow hY0]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_abs_self _)) (pow_le_pow_left' h2 _)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
namespace MomentPoint
variable (S : MomentPoint Λ) {CM CM1 CO C₀ cE : ℝ}
private theorem exponent_ne_zero (h : PointBounds S CM CM1 CO C₀ cE) : (8 * (Λ.k : ENNReal)) ≠ 0 := by
  have : (Λ.k : ENNReal) ≠ 0 := by exact_mod_cast NeZero.ne Λ.k
  simpa using this
private theorem rpow_half_nonneg (h : PointBounds S CM CM1 CO C₀ cE) : 0 ≤ S.scaleCoupling ^ ((1 : ℝ) / 2) :=
  Real.rpow_nonneg (by linarith [h.one_le_coupling]) _
private theorem card_le_eight (h : PointBounds S CM CM1 CO C₀ cE) (B : Finset (Fin Λ.k)) : B.card ≤ 8 := by
  have := Finset.card_le_univ B
  simp only [Fintype.card_fin] at this
  have := h.k_le
  omega
private theorem abs_formProductMean_le_of_curl (h : PointBounds S CM CM1 CO C₀ cE) {d n : ℕ} [NeZero n]
    (hd : d ≤ S.logIndex + 1) (hn : n = S.levelSide (S.lastSeparated + d))
    (B : Finset (Fin Λ.k)) (X : ColourForm n) {v : ℝ} (hv : 0 ≤ v)
    (hX : ∀ p : OrientedPlaquette n, curlNorm X p.1 ≤ 60 * v) :
    |S.formProductMean d n B X| ≤
      |CM * (S.range : ℝ) ^ (4 * B.card)| * (1 + 120 * S.scaleCoupling ^ ((1 : ℝ) / 2) * v) ^ (2 * B.card) := by
  have h1 := (h.means d n hd hn B Unit (Measure.dirac ()) (fun _ => X) (fun _ => X) measurable_const
    measurable_const).1
  rw [lintegral_dirac] at h1
  exact le_of_dirac_bound (fun p => S.distanceWeight_le_one h.admissible.rt_pos.le _ n p) (S.exponent_ne_zero h) X hv hX
    (S.rpow_half_nonneg h) (abs_nonneg _) h1
private theorem abs_formProductMean_sub_zero_le (h : PointBounds S CM CM1 CO C₀ cE) {d n : ℕ} [NeZero n]
    (hd : d ≤ S.logIndex + 1) (hn : n = S.levelSide (S.lastSeparated + d))
    (B : Finset (Fin Λ.k)) (X : ColourForm n) {v : ℝ} (hv : 0 ≤ v)
    (hX : ∀ p : OrientedPlaquette n, curlNorm X p.1 ≤ 60 * v) :
    |S.formProductMean d n B X - S.formProductMean d n B 0| ≤
      |CM * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(d : ℝ) / 4)| *
        (1 + 120 * S.scaleCoupling ^ ((1 : ℝ) / 2) * v) ^ (2 * B.card) := by
  have h1 := (h.means d n hd hn B Unit (Measure.dirac ()) (fun _ => X) (fun _ => X) measurable_const
    measurable_const).2
  rw [lintegral_dirac] at h1
  exact le_of_dirac_bound (fun p => S.distanceWeight_le_one h.admissible.rt_pos.le _ n p) (S.exponent_ne_zero h) X hv hX
    (S.rpow_half_nonneg h) (abs_nonneg _) h1
private def goodBound (CM : ℝ) (B : Finset (Fin Λ.k)) : ℝ :=
  |CM * (S.range : ℝ) ^ (4 * B.card)| * (121 ^ 16 * S.scaleCoupling ^ 4)
private theorem goodBound_nonneg (h : PointBounds S CM CM1 CO C₀ cE) (B : Finset (Fin Λ.k)) : 0 ≤ S.goodBound CM B := by
  have := h.one_le_coupling
  unfold goodBound
  have : 0 ≤ S.scaleCoupling := by linarith
  positivity
private theorem abs_formProductMean_cutoff_le (h : PointBounds S CM CM1 CO C₀ cE) {d n : ℕ} [NeZero n]
    (hd : d ≤ S.logIndex + 1) (hn : n = S.levelSide (S.lastSeparated + d))
    (B : Finset (Fin Λ.k)) (W : TorusField n) (Y : Finset (TorusSite n))
    (hg : S.IsGoodConfig (S.lastSeparated + d) n W Y) :
    |S.formProductMean d n B (S.cutoffColourForm (S.lastSeparated + d) n W)| ≤ S.goodBound CM B := by
  have hv := S.localCurvature_nonneg (S.lastSeparated + d) n W
  have h1 := S.abs_formProductMean_le_of_curl h hd hn B _ hv
    (h.cutoff (S.lastSeparated + d) (by omega) (by omega) n hn W Y hg)
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h2 := one_add_mul_le_rpow_quarter h.one_le_coupling hv hg.curvature_le
  have h3 : 0 ≤ 1 + 120 * S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature (S.lastSeparated + d) n W := by
    have := S.rpow_half_nonneg h
    positivity
  exact (pow_le_pow_left₀ h3 h2 _).trans (pow_le_rpow_four h.one_le_coupling (by have := S.card_le_eight h B; omega))
private theorem abs_goodCaseForms_le (h : PointBounds S CM CM1 CO C₀ cE) {d n : ℕ} [NeZero n] (hd : d ≤ S.logIndex + 1)
    (hn : n * Λ.stepParams.side = S.levelSide (S.lastSeparated + d))
    (B : Finset (Fin Λ.k)) (W Yt ωt bad b) :
    |S.goodCaseForms (S.lastSeparated + d) d n B W Yt ωt bad b| ≤ S.goodBound CM B := by
  classical
  unfold goodCaseForms
  split_ifs with hg
  · exact S.abs_formProductMean_cutoff_le h hd hn B W Yt hg
  · simpa using S.goodBound_nonneg h B
private theorem caseLiftOf_goodCaseForms (u d n : ℕ) [NeZero n] (B : Finset (Fin Λ.k))
    (z : MarkedSample Λ.stepParams (u + 1) n) :
    caseLiftOf S.tower u n (fun _ => S.goodCaseForms u d n B) z =
      (S.goodSet u (n * Λ.stepParams.side)).indicator (S.cutoffMean u d (n * Λ.stepParams.side) B) z.1 := by
  classical
  unfold caseLiftOf goodCaseForms goodSet cutoffMean
  simp only [Set.indicator_apply, Set.mem_setOf_eq, state]
  rw [stageState_fst]
private theorem measurable_caseLift_goodCaseForms (h : PointBounds S CM CM1 CO C₀ cE) (u d n : ℕ) [NeZero n]
    (B : Finset (Fin Λ.k)) :
    Measurable (FreeEnergies.caseLift S.tower u n (fun _ => S.goodCaseForms u d n B)) := by
  have hq0 := h.stage_measurable u (n * Λ.stepParams.side)
  have hf0 : Measurable ((S.goodSet u (n * Λ.stepParams.side)).indicator
      (S.cutoffMean u d (n * Λ.stepParams.side) B)) :=
    (S.measurable_cutoffMean h.log_measurable u d _ B hq0).indicator (S.measurableSet_goodSet _ _ hq0)
  have hfst : Measurable fun z : MarkedSample Λ.stepParams (u + 1) n => z.1 := by
    let _ := markedSampleMeasurableSpace Λ.stepParams u (n * Λ.stepParams.side)
    exact measurable_fst
  have el : FreeEnergies.caseLift S.tower u n (fun _ => S.goodCaseForms u d n B) =
      fun z => (S.goodSet u (n * Λ.stepParams.side)).indicator (S.cutoffMean u d (n * Λ.stepParams.side) B) z.1 :=
    funext (S.caseLiftOf_goodCaseForms u d n B)
  rw [el]
  exact hf0.comp hfst
private theorem indicator_cutoffMean_congr (u d : ℕ) {a b : ℕ} [NeZero a] [NeZero b] (e : a = b)
    (x : MarkedSample Λ.stepParams u a) (y : MarkedSample Λ.stepParams u b)
    (hxy : HEq x y) (B : Finset (Fin Λ.k)) :
    (S.goodSet u a).indicator (S.cutoffMean u d a B) x = (S.goodSet u b).indicator (S.cutoffMean u d b B) y := by
  subst e
  rw [eq_of_heq hxy]
open Classical in
private theorem formMeanObs_of_le {t d : ℕ} (B : Finset (Fin Λ.k)) (hu : t + d ≤ S.data.windowLevel)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    formMeanObs t d B S w = if S.IsGoodConfig (t + d) (S.sideAtLevel (t + d)) (S.stateAtLevel (t + d) hu w).1
        (S.stateAtLevel (t + d) hu w).2.1 then
      S.formProductMean d (S.sideAtLevel (t + d)) B
        (S.cutoffColourForm (t + d) (S.sideAtLevel (t + d)) (S.stateAtLevel (t + d) hu w).1) else 0 := dif_pos hu
open Classical in
private theorem notGoodIndicator_of_le {u : ℕ} (hu : u ≤ S.data.windowLevel)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    notGoodIndicator u S w =
      if S.IsGoodConfig u (S.sideAtLevel u) (S.stateAtLevel u hu w).1 (S.stateAtLevel u hu w).2.1 then 0 else 1 :=
  dif_pos hu
open Classical in
private theorem goodCurvaturePower_of_le {u : ℕ} (k : ℕ) (hu : u ≤ S.data.windowLevel)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    goodCurvaturePower u k S w =
      if S.IsGoodConfig u (S.sideAtLevel u) (S.stateAtLevel u hu w).1 (S.stateAtLevel u hu w).2.1 then
        (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature u (S.sideAtLevel u) (S.stateAtLevel u hu w).1) ^ k
      else 0 := dif_pos hu
private theorem levelObservable_of_not_le {u : ℕ}
    {f : (S : MomentPoint Λ) → StageState S.tower u (S.sideAtLevel u) → ℝ} (hu : ¬ u ≤ S.data.windowLevel)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    levelObservable u f S w = 0 := dif_neg hu
private theorem formMeanObs_eq_indicator {t d : ℕ} (B : Finset (Fin Λ.k)) (hu : t + d ≤ S.data.windowLevel)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    formMeanObs t d B S w = (S.goodSet (t + d) (S.sideAtLevel (t + d))).indicator
      (S.cutoffMean (t + d) d (S.sideAtLevel (t + d)) B) (S.sampleAtLevel (t + d) hu w) := by
  classical
  rw [S.formMeanObs_of_le B hu]
  by_cases hg : S.sampleAtLevel (t + d) hu w ∈ S.goodSet (t + d) (S.sideAtLevel (t + d))
  · have hg' : S.IsGoodConfig (t + d) (S.sideAtLevel (t + d)) (S.stateAtLevel (t + d) hu w).1
        (S.stateAtLevel (t + d) hu w).2.1 := hg
    rw [Set.indicator_of_mem hg, if_pos hg']
    rfl
  · have hg' : ¬ S.IsGoodConfig (t + d) (S.sideAtLevel (t + d)) (S.stateAtLevel (t + d) hu w).1
        (S.stateAtLevel (t + d) hu w).2.1 := hg
    rw [Set.indicator_of_notMem hg, if_neg hg']
private theorem liftObs_eq (h : PointBounds S CM CM1 CO C₀ cE) {t d : ℕ} (B : Finset (Fin Λ.k))
    (hu : t + d + 1 ≤ S.data.windowLevel)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    liftObs t d B S w = formMeanObs t d B S w := by
  have h0 : t + d ≤ S.data.windowLevel := by omega
  obtain ⟨e, hh⟩ := S.sampleAtLevel_succ_fst (t + d) hu h0 w
  unfold liftObs
  rw [dif_pos hu, S.formMeanObs_eq_indicator B h0 w]
  show caseLiftOf S.tower (t + d) (S.sideAtLevel (t + d + 1))
    (fun _ => S.goodCaseForms (t + d) d (S.sideAtLevel (t + d + 1)) B) (S.sampleAtLevel (t + d + 1) hu w) = _
  rw [S.caseLiftOf_goodCaseForms]
  exact S.indicator_cutoffMean_congr _ _ e _ _ hh B
private theorem measurable_formMeanObs (h : PointBounds S CM CM1 CO C₀ cE) {t d : ℕ} (B : Finset (Fin Λ.k))
    (hu : t + d ≤ S.data.windowLevel) : Measurable (formMeanObs t d B S) := by
  have e : formMeanObs t d B S = fun w => (S.goodSet (t + d) (S.sideAtLevel (t + d))).indicator
      (S.cutoffMean (t + d) d (S.sideAtLevel (t + d)) B) (S.sampleAtLevel (t + d) hu w) :=
    funext (S.formMeanObs_eq_indicator B hu)
  rw [e]
  have hq := h.stage_measurable (t + d) (S.sideAtLevel (t + d))
  exact ((S.measurable_cutoffMean h.log_measurable _ d _ B hq).indicator (S.measurableSet_goodSet _ _ hq)).comp
    (S.sampleAtLevel_map h _ hu).1
private theorem abs_formMeanObs_le (h : PointBounds S CM CM1 CO C₀ cE) {t d : ℕ} (ht : S.lastSeparated = t)
    (B : Finset (Fin Λ.k)) (hd : d ≤ S.logIndex + 1)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    |formMeanObs t d B S w| ≤ S.goodBound CM B := by
  classical
  subst ht
  have hu : S.lastSeparated + d ≤ S.data.windowLevel := by have := h.window; omega
  rw [S.formMeanObs_of_le B hu]
  split_ifs with hg
  · exact S.abs_formProductMean_cutoff_le h hd (S.sideAtLevel_eq _) B _ _ hg
  · simpa using S.goodBound_nonneg h B
private theorem measurableSet_good_sample (h : PointBounds S CM CM1 CO C₀ cE) {u : ℕ} (hu : u ≤ S.data.windowLevel) :
    MeasurableSet {w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side) |
      S.sampleAtLevel u hu w ∈ S.goodSet u (S.sideAtLevel u)} :=
  (S.sampleAtLevel_map h u hu).1 (S.measurableSet_goodSet u _ (h.stage_measurable u _))
private theorem measurable_notGoodIndicator (h : PointBounds S CM CM1 CO C₀ cE) {u : ℕ}
    (hu : u ≤ S.data.windowLevel) : Measurable (notGoodIndicator u S) := by
  classical
  have e : notGoodIndicator u S = fun w => if S.sampleAtLevel u hu w ∈ S.goodSet u (S.sideAtLevel u) then 0 else 1 := by
    funext w
    rw [S.notGoodIndicator_of_le hu]
    rfl
  rw [e]
  exact Measurable.ite (S.measurableSet_good_sample h hu) measurable_const measurable_const
private theorem notGoodIndicator_nonneg (u : ℕ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    0 ≤ notGoodIndicator u S w := by apply _root_.YangMills.SharedProofs.p125034 <;> assumption
private theorem abs_notGoodIndicator_le (u : ℕ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    |notGoodIndicator u S w| ≤ 1 := by apply _root_.YangMills.SharedProofs.p4667 <;> assumption
private theorem measurable_goodCurvaturePower (h : PointBounds S CM CM1 CO C₀ cE) {u : ℕ}
    (hu : u ≤ S.data.windowLevel) (k : ℕ) : Measurable (goodCurvaturePower u k S) := by
  classical
  have e : goodCurvaturePower u k S = fun w => if S.sampleAtLevel u hu w ∈ S.goodSet u (S.sideAtLevel u) then
      (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) *
        S.localCurvature u (S.sideAtLevel u) (S.state u (S.sideAtLevel u) (S.sampleAtLevel u hu w)).1) ^ k else 0 := by
    funext w
    rw [S.goodCurvaturePower_of_le k hu]
    rfl
  rw [e]
  refine Measurable.ite (S.measurableSet_good_sample h hu) ?_ measurable_const
  refine (measurable_const.add (measurable_const.mul ?_)).pow_const k
  exact (S.measurable_localCurvature u _).comp
    (measurable_fst.comp ((h.stage_measurable u _).comp (S.sampleAtLevel_map h u hu).1))
private theorem abs_goodCurvaturePower_le (h : PointBounds S CM CM1 CO C₀ cE) (u k : ℕ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    |goodCurvaturePower u k S w| ≤ (1 + S.scaleCoupling ^ ((1 : ℝ) / 4)) ^ k := by
  classical
  have hx := h.one_le_coupling
  have hx0 : 0 < S.scaleCoupling := by linarith
  have h0 : (0 : ℝ) ≤ (1 + S.scaleCoupling ^ ((1 : ℝ) / 4)) ^ k := by positivity
  by_cases hu : u ≤ S.data.windowLevel
  swap
  · have e : goodCurvaturePower u k S w = 0 := S.levelObservable_of_not_le hu w
    rw [e]
    simpa using h0
  rw [S.goodCurvaturePower_of_le k hu]
  split_ifs with hg
  · have hv := S.localCurvature_nonneg u (S.sideAtLevel u) (S.stateAtLevel u hu w).1
    have hs := S.rpow_half_nonneg h
    have h2 : S.scaleCoupling ^ ((1 : ℝ) / 2) * S.scaleCoupling ^ (-(1 / 4) : ℝ) = S.scaleCoupling ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hx0]
      norm_num
    have h3 : S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature u (S.sideAtLevel u) (S.stateAtLevel u hu w).1 ≤
        S.scaleCoupling ^ ((1 : ℝ) / 4) := by
      rw [← h2]
      exact mul_le_mul_of_nonneg_left hg.curvature_le hs
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  · simpa using h0
private theorem goodCurvaturePower_nonneg (h : PointBounds S CM CM1 CO C₀ cE) (u k : ℕ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    0 ≤ goodCurvaturePower u k S w := by
  classical
  by_cases hu : u ≤ S.data.windowLevel
  swap
  · exact (S.levelObservable_of_not_le hu w).ge
  rw [S.goodCurvaturePower_of_le k hu]
  split_ifs with hg
  · have hv := S.localCurvature_nonneg u (S.sideAtLevel u) (S.stateAtLevel u hu w).1
    have hs := S.rpow_half_nonneg h
    positivity
  · exact le_rfl
end MomentPoint
end Bounds
section Relations
variable {Λ : MomentParameters}
private theorem abs_scaled_prod_sub_le {ι : Type} [DecidableEq ι] (B : Finset ι) {Fi Ni Qi : ι → ℝ}
    {v x s r C E : ℝ} (hs : 1 ≤ s) (hx : x = s ^ 2)
    (hr : 1 ≤ r) (hε : r ^ 3 * s⁻¹ ≤ 1) (hC : 0 ≤ C) (hE0 : 0 ≤ E) (hE : s ^ 3 * E ≤ 1) (hv : 0 ≤ v)
    (hN1 : ∀ i, 1 ≤ Ni i)
    (hpt : ∀ i, |Fi i - 1 / 2 * Qi i| ≤ C * (r ^ 7 * v ^ 3 + r ^ 4 * s⁻¹ * v ^ 2 + r ^ 4 * E * Ni i) ∧
      |Qi i| ≤ C * r ^ 4 * v ^ 2) :
    |x ^ B.card * ∏ i ∈ B, Fi i - ∏ i ∈ B, x / 2 * Qi i| ≤
      r ^ 3 * s⁻¹ * (2 * (3 * C + 1) * r ^ 4) ^ B.card * ((1 + s * v) ^ (6 * B.card) + (∏ i ∈ B, Ni i) ^ 2) := by
  set b := B.card with hb
  set K := 3 * C + 1 with hK
  have hK0 : 0 < K := by rw [hK]; linarith
  set κ := (2 * K * r ^ 4) ^ b with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set ε := r ^ 3 * s⁻¹ with hεd
  have hε0 : 0 ≤ ε := by positivity
  have hone := fun i => scaled_factor_bounds hs hx hr hv (hN1 i) hC hE0 hE (hpt i).1 (hpt i).2
  have hTn : ∀ i ∈ B, 0 ≤ K * r ^ 4 * (1 + s * v) ^ 3 * Ni i := fun i _ => by
    have : 0 ≤ Ni i := by linarith [hN1 i]
    positivity
  have hpn := abs_prod_sub_prod_le B (fun i => x * Fi i) (fun i => x / 2 * Qi i)
    (fun i => K * r ^ 4 * (1 + s * v) ^ 3 * Ni i) hε0 hε hTn (fun i _ => (hone i).1) (fun i _ => (hone i).2)
  have hNp : 0 ≤ ∏ i ∈ B, Ni i := Finset.prod_nonneg fun i _ => by linarith [hN1 i]
  have eT : 2 ^ b * ∏ i ∈ B, K * r ^ 4 * (1 + s * v) ^ 3 * Ni i = κ * ((1 + s * v) ^ (3 * b) * ∏ i ∈ B, Ni i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, hκ, ← hb]
    generalize (1 + s * v) = u
    ring
  have eA : ∏ i ∈ B, x * Fi i = x ^ b * ∏ i ∈ B, Fi i := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← hb]
  set a := (1 + s * v) ^ (3 * b) with ha
  have ea : (1 + s * v) ^ (6 * b) = a ^ 2 := by rw [ha]; ring
  have ha0 : 0 ≤ a := by positivity
  set P := ∏ i ∈ B, Ni i with hPd
  have hab : a * P ≤ a ^ 2 + P ^ 2 := by nlinarith [sq_nonneg (a - P), mul_nonneg ha0 hNp]
  rw [ea]
  obtain ⟨p1, -⟩ := hpn
  beta_reduce at p1
  rw [eT, eA] at p1
  refine p1.trans ?_
  rw [mul_assoc ε κ]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hab hκ0) hε0
private theorem one_add_mul_pow_le {y : ℝ} (hy : 0 ≤ y) {k : ℕ} (hk : k ≤ 16) :
    (1 + 120 * y) ^ k ≤ 120 ^ 16 * (1 + y) ^ k := by
  calc (1 + 120 * y) ^ k ≤ (120 * (1 + y)) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) _
    _ = 120 ^ k * (1 + y) ^ k := mul_pow _ _ _
    _ ≤ 120 ^ 16 * (1 + y) ^ k := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) (by positivity)
private theorem one_le_list_prod {α : Type} (f : α → ℝ) (hf : ∀ a, 1 ≤ f a) (J : List α) : 1 ≤ (J.map f).prod := by apply _root_.YangMills.SharedProofs.p58552 <;> assumption
private theorem prod_flatten_replicate {α : Type} (f : α → ℝ) (J : List α) (q : ℕ) :
    (((List.replicate q J).flatten).map f).prod = ((J.map f).prod) ^ q := by apply _root_.YangMills.SharedProofs.p31647 <;> assumption
private theorem length_flatten_replicate {α : Type} (J : List α) (q : ℕ) :
    ((List.replicate q J).flatten).length = q * J.length := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]
    ring
namespace MomentPoint
variable (S : MomentPoint Λ) {CM CM1 CO C₀ cE : ℝ}
private theorem levelSide_eq_succ_mul {u : ℕ} (h : u + 1 ≤ S.data.windowLevel) :
    S.levelSide u = S.levelSide (u + 1) * Λ.stepParams.side := by
  have e : S.data.windowLevel - u = S.data.windowLevel - (u + 1) + 1 := by omega
  show S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - u) =
    S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (u + 1)) * Λ.stepParams.side
  rw [e, pow_succ, mul_assoc]
abbrev _root_.YangMills.SharedProofs.p19020 := @levelSide_eq_succ_mul
private theorem caseMeanAtSample_bounds (h : PointBounds S CM CM1 CO C₀ cE) {d : ℕ} (hd : d < S.logIndex)
    (B : Finset (Fin Λ.k)) :
    ∀ (n : ℕ) [NeZero n], n = S.levelSide (S.lastSeparated + d + 1) →
    AEStronglyMeasurable (FreeEnergies.caseMeanAtSample S.tower (S.lastSeparated + d) n
      (fun _ => S.goodCaseForms (S.lastSeparated + d) d n B)) (S.law (S.lastSeparated + d + 1) n) ∧
    ∀ᵐ z ∂(S.law (S.lastSeparated + d + 1) n),
      |FreeEnergies.caseMeanAtSample S.tower (S.lastSeparated + d) n
        (fun _ => S.goodCaseForms (S.lastSeparated + d) d n B) z| ≤ S.goodBound CM B ∧
      (z ∈ S.goodSet (S.lastSeparated + d + 1) n →
        |FreeEnergies.caseMeanAtSample S.tower (S.lastSeparated + d) n
            (fun _ => S.goodCaseForms (S.lastSeparated + d) d n B) z -
          S.formProductMean (d + 1) n B
            (S.cutoffColourForm (S.lastSeparated + d + 1) n (S.state (S.lastSeparated + d + 1) n z).1)| ≤
        CO * (S.range : ℝ) ^ (4 * B.card + 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ) *
          (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) *
            S.localCurvature (S.lastSeparated + d + 1) n (S.state (S.lastSeparated + d + 1) n z).1) ^
              (2 * B.card + 1)) := by
  intro n _ hn
  subst hn
  have hwin := h.window
  have hu2 : S.lastSeparated + d + 2 ≤ S.data.windowLevel := by omega
  haveI hP := h.isProbability (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1))
  have hq0 := h.stage_measurable (S.lastSeparated + d) (S.levelSide (S.lastSeparated + d + 1) * Λ.stepParams.side)
  have hq1 := h.stage_measurable (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1))
  have hm : stageSigma S.tower (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1)) ≤
      markedSampleMeasurableSpace Λ.stepParams (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1)) :=
    hq1.comap_le
  have hfst : Measurable fun z : MarkedSample Λ.stepParams (S.lastSeparated + d + 1)
      (S.levelSide (S.lastSeparated + d + 1)) => z.1 := by
    let _ := markedSampleMeasurableSpace Λ.stepParams (S.lastSeparated + d)
      (S.levelSide (S.lastSeparated + d + 1) * Λ.stepParams.side)
    exact measurable_fst
  have hf0 : Measurable ((S.goodSet (S.lastSeparated + d) (S.levelSide (S.lastSeparated + d + 1) * Λ.stepParams.side)).indicator
      (S.cutoffMean (S.lastSeparated + d) d (S.levelSide (S.lastSeparated + d + 1) * Λ.stepParams.side) B)) :=
    (S.measurable_cutoffMean h.log_measurable (S.lastSeparated + d) d _ B hq0).indicator
      (S.measurableSet_goodSet _ _ hq0)
  have el : caseLiftOf S.tower (S.lastSeparated + d) (S.levelSide (S.lastSeparated + d + 1))
      (fun _ => S.goodCaseForms (S.lastSeparated + d) d (S.levelSide (S.lastSeparated + d + 1)) B) =
      fun z => (S.goodSet (S.lastSeparated + d) (S.levelSide (S.lastSeparated + d + 1) * Λ.stepParams.side)).indicator
        (S.cutoffMean (S.lastSeparated + d) d (S.levelSide (S.lastSeparated + d + 1) * Λ.stepParams.side) B) z.1 :=
    funext (S.caseLiftOf_goodCaseForms (S.lastSeparated + d) d _ B)
  have hlm : Measurable (caseLiftOf S.tower (S.lastSeparated + d) (S.levelSide (S.lastSeparated + d + 1))
      (fun _ => S.goodCaseForms (S.lastSeparated + d) d (S.levelSide (S.lastSeparated + d + 1)) B)) := by
    rw [el]
    exact hf0.comp hfst
  have hlb : ∀ z, |caseLiftOf S.tower (S.lastSeparated + d) (S.levelSide (S.lastSeparated + d + 1))
      (fun _ => S.goodCaseForms (S.lastSeparated + d) d (S.levelSide (S.lastSeparated + d + 1)) B) z| ≤
        S.goodBound CM B := fun z =>
    S.abs_goodCaseForms_le h (by omega) (S.levelSide_eq_succ_mul (by omega)).symm B
      (topField Λ.stepParams (S.lastSeparated + d) (S.levelSide (S.lastSeparated + d + 1) * Λ.stepParams.side) z.1)
      (stageState S.tower (S.lastSeparated + d) (S.levelSide (S.lastSeparated + d + 1) * Λ.stepParams.side) z.1).2.1
      (stageState S.tower (S.lastSeparated + d) (S.levelSide (S.lastSeparated + d + 1) * Λ.stepParams.side) z.1).2.2
      z.2.2.2 z.2.1
  have hc := h.condMean_eq (S.lastSeparated + d) hu2 _ hlm ⟨_, hlb⟩
  have hone : caseLiftOf S.tower (S.lastSeparated + d) (S.levelSide (S.lastSeparated + d + 1))
      (fun _ _ _ _ _ _ => 1) = fun _ => (1 : ℝ) := rfl
  have h1 := h.condMean_eq (S.lastSeparated + d) hu2 (fun _ _ _ _ _ _ => 1) (by rw [hone]; exact measurable_const)
    ⟨1, fun z => by rw [hone]; simp⟩
  have hP' : IsProbabilityMeasure (markedSampleLaw S.tower S.β (S.lastSeparated + d + 1)
      (S.levelSide (S.lastSeparated + d + 1))) := hP
  have hpos := coarseStateWeight_pos_ae S.tower S.β (S.lastSeparated + d) (S.levelSide (S.lastSeparated + d + 1)) hm
    (h.weight_nonneg (S.lastSeparated + d) hu2) h1
  refine ⟨integrable_condExp.aestronglyMeasurable.congr hc, ?_⟩
  have hM0 := S.goodBound_nonneg h (CM := CM) B
  have h0 : ∀ᵐ w ∂(S.law (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1))),
      |caseLiftOf S.tower (S.lastSeparated + d) (S.levelSide (S.lastSeparated + d + 1))
        (fun _ => S.goodCaseForms (S.lastSeparated + d) d (S.levelSide (S.lastSeparated + d + 1)) B) w| ≤
        ((S.goodBound CM B).toNNReal : ℝ) :=
    ae_of_all _ fun w => (hlb w).trans (Real.le_coe_toNNReal _)
  have hb1 := ae_bdd_condExp_of_ae_bdd
    (m := stageSigma S.tower (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1))) h0
  filter_upwards [hb1, hc, hpos] with z hz hcz hp
  refine ⟨?_, fun hg => ?_⟩
  · have e : FreeEnergies.caseMeanAtSample S.tower (S.lastSeparated + d) (S.levelSide (S.lastSeparated + d + 1))
        (fun _ => S.goodCaseForms (S.lastSeparated + d) d (S.levelSide (S.lastSeparated + d + 1)) B) z =
        ((S.law (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1)))[caseLiftOf S.tower
          (S.lastSeparated + d) (S.levelSide (S.lastSeparated + d + 1))
          (fun _ => S.goodCaseForms (S.lastSeparated + d) d (S.levelSide (S.lastSeparated + d + 1)) B) |
            stageSigma S.tower (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1))]) z := hcz.symm
    rw [e]
    refine hz.trans ?_
    rw [Real.coe_toNNReal _ hM0]
  · exact h.one_step d (S.levelSide (S.lastSeparated + d + 1)) hd rfl z.2.2.1
      (stageState S.tower (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1)) z).2.1
      (stageState S.tower (S.lastSeparated + d + 1) (S.levelSide (S.lastSeparated + d + 1)) z).2.2 hg hp B
private theorem caseMeanObs_step (h : PointBounds S CM CM1 CO C₀ cE) {t d : ℕ} (ht : S.lastSeparated = t)
    (hd : d < S.logIndex) (B : Finset (Fin Λ.k)) :
    AEStronglyMeasurable (caseMeanObs t d B S) (S.law S.data.windowLevel (S.data.period Λ.stepParams.side)) ∧
    (∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)), |caseMeanObs t d B S w| ≤ S.goodBound CM B) ∧
    ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)),
      |caseMeanObs t d B S w - formMeanObs t (d + 1) B S w| ≤
        |CO * (S.range : ℝ) ^ (4 * B.card + 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ)| *
          goodCurvaturePower (t + (d + 1)) (2 * B.card + 1) S w +
        S.goodBound CM B * notGoodIndicator (t + (d + 1)) S w := by
  classical
  subst ht
  have hwin := h.window
  have hu : S.lastSeparated + d + 1 ≤ S.data.windowLevel := by omega
  obtain ⟨m1, e1⟩ := S.sampleAtLevel_map h (S.lastSeparated + d + 1) hu
  obtain ⟨ha, hb⟩ := S.caseMeanAtSample_bounds h hd B (S.sideAtLevel (S.lastSeparated + d + 1)) (S.sideAtLevel_eq _)
  have e : caseMeanObs S.lastSeparated d B S = fun w => FreeEnergies.caseMeanAtSample S.tower (S.lastSeparated + d)
      (S.sideAtLevel (S.lastSeparated + d + 1))
      (fun _ => S.goodCaseForms (S.lastSeparated + d) d (S.sideAtLevel (S.lastSeparated + d + 1)) B)
      (S.sampleAtLevel (S.lastSeparated + d + 1) hu w) := funext fun w => dif_pos hu
  have hl := S.ae_of_sampleAtLevel h _ hu hb
  refine ⟨?_, ?_, ?_⟩
  · rw [e]
    rw [← e1] at ha
    exact ha.comp_measurable m1
  · filter_upwards [hl] with w hw
    rw [e]
    exact hw.1
  · filter_upwards [hl] with w hw
    obtain ⟨b1, b2⟩ := hw
    have eM : caseMeanObs S.lastSeparated d B S w = FreeEnergies.caseMeanAtSample S.tower (S.lastSeparated + d)
      (S.sideAtLevel (S.lastSeparated + d + 1))
      (fun _ => S.goodCaseForms (S.lastSeparated + d) d (S.sideAtLevel (S.lastSeparated + d + 1)) B)
      (S.sampleAtLevel (S.lastSeparated + d + 1) hu w) := congrFun e w
    rw [eM, show S.lastSeparated + (d + 1) = S.lastSeparated + d + 1 from rfl]
    have hC := S.goodCurvaturePower_nonneg h (S.lastSeparated + d + 1) (2 * B.card + 1) w
    have hB0 := S.goodBound_nonneg h (CM := CM) B
    have hG0 := S.notGoodIndicator_nonneg (S.lastSeparated + d + 1) w
    by_cases hg : S.IsGoodConfig (S.lastSeparated + d + 1) (S.sideAtLevel (S.lastSeparated + d + 1))
      (S.stateAtLevel (S.lastSeparated + d + 1) hu w).1 (S.stateAtLevel (S.lastSeparated + d + 1) hu w).2.1
    · have e2 : formMeanObs S.lastSeparated (d + 1) B S w = S.formProductMean (d + 1)
          (S.sideAtLevel (S.lastSeparated + d + 1)) B
          (S.cutoffColourForm (S.lastSeparated + d + 1) (S.sideAtLevel (S.lastSeparated + d + 1))
            (S.stateAtLevel (S.lastSeparated + d + 1) hu w).1) := by
        rw [S.formMeanObs_of_le (t := S.lastSeparated) (d := d + 1) B hu]
        exact if_pos hg
      rw [e2, S.goodCurvaturePower_of_le _ hu, if_pos hg]
      have b3 := b2 hg
      have hy : 0 ≤ (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature (S.lastSeparated + d + 1)
          (S.sideAtLevel (S.lastSeparated + d + 1)) (S.stateAtLevel (S.lastSeparated + d + 1) hu w).1) ^
            (2 * B.card + 1) := by
        have := S.localCurvature_nonneg (S.lastSeparated + d + 1) (S.sideAtLevel (S.lastSeparated + d + 1))
          (S.stateAtLevel (S.lastSeparated + d + 1) hu w).1
        have := S.rpow_half_nonneg h
        positivity
      refine b3.trans ?_
      have := mul_le_mul_of_nonneg_right
        (le_abs_self (CO * (S.range : ℝ) ^ (4 * B.card + 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ))) hy
      have h5 := mul_nonneg hB0 hG0
      exact this.trans (le_add_of_nonneg_right h5)
    · have e2 : formMeanObs S.lastSeparated (d + 1) B S w = 0 := by
        rw [S.formMeanObs_of_le (t := S.lastSeparated) (d := d + 1) B hu]
        exact if_neg hg
      have e3 : goodCurvaturePower (S.lastSeparated + d + 1) (2 * B.card + 1) S w = 0 := by
        rw [S.goodCurvaturePower_of_le _ hu]
        exact if_neg hg
      have e4 : notGoodIndicator (S.lastSeparated + d + 1) S w = 1 := by
        rw [S.notGoodIndicator_of_le hu]
        exact if_neg hg
      rw [e2, e3, e4, sub_zero, mul_zero, zero_add, mul_one]
      exact b1
private theorem formMeanObs_top (h : PointBounds S CM CM1 CO C₀ cE) {t : ℕ} (ht : S.lastSeparated = t)
    (B : Finset (Fin Λ.k)) :
    ∃ p₀ : ℝ, |p₀| ≤ |CM * (S.range : ℝ) ^ (4 * B.card)| ∧
      (∀ (d : ℕ), S.lastSeparated + d = S.data.windowLevel →
        ∀ μ : Measure (LevelChain Λ.stepParams.side (S.lastSeparated + d) (S.data.period Λ.stepParams.side)),
        IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling (S.lastSeparated + d)
          (S.data.period Λ.stepParams.side)) μ →
        |p₀ - ∫ X, ∏ i ∈ B, S.halfForm d (S.data.period Λ.stepParams.side) i X ∂μ| ≤
          CM1 * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4)) ∧
      ∀ w, |formMeanObs t S.logIndex B S w - p₀| ≤
        |CM * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4)| * 120 ^ 16 *
            goodCurvaturePower (t + S.logIndex) (2 * B.card) S w +
          |CM * (S.range : ℝ) ^ (4 * B.card)| * notGoodIndicator (t + S.logIndex) S w := by
  classical
  subst ht
  have hwin := h.window
  have hu : S.lastSeparated + S.logIndex ≤ S.data.windowLevel := by omega
  have hs := S.rpow_half_nonneg h
  have hp0 : |S.formProductMean S.logIndex (S.sideAtLevel (S.lastSeparated + S.logIndex)) B 0| ≤
      |CM * (S.range : ℝ) ^ (4 * B.card)| := by
    have h1 := S.abs_formProductMean_le_of_curl h (d := S.logIndex) (by omega) (S.sideAtLevel_eq _) B 0
      (le_refl (0 : ℝ)) (fun p => by rw [MomentPoint.curlNorm_zero]; simp)
    simpa using h1
  refine ⟨S.formProductMean S.logIndex (S.sideAtLevel (S.lastSeparated + S.logIndex)) B 0, hp0, ?_, fun w => ?_⟩
  · intro d hd μ hμ
    exact h.chain S.logIndex d _ hd (by omega) (S.sideAtLevel_eq _) μ hμ B
  · have hG0 := S.notGoodIndicator_nonneg (S.lastSeparated + S.logIndex) w
    by_cases hg : S.IsGoodConfig (S.lastSeparated + S.logIndex) (S.sideAtLevel (S.lastSeparated + S.logIndex))
      (S.stateAtLevel (S.lastSeparated + S.logIndex) hu w).1 (S.stateAtLevel (S.lastSeparated + S.logIndex) hu w).2.1
    · have e2 : formMeanObs S.lastSeparated S.logIndex B S w = S.formProductMean S.logIndex
          (S.sideAtLevel (S.lastSeparated + S.logIndex)) B
          (S.cutoffColourForm (S.lastSeparated + S.logIndex) (S.sideAtLevel (S.lastSeparated + S.logIndex))
            (S.stateAtLevel (S.lastSeparated + S.logIndex) hu w).1) := by
        rw [S.formMeanObs_of_le B hu]
        exact if_pos hg
      rw [e2, S.goodCurvaturePower_of_le _ hu, if_pos hg]
      have hv := S.localCurvature_nonneg (S.lastSeparated + S.logIndex) (S.sideAtLevel (S.lastSeparated + S.logIndex))
        (S.stateAtLevel (S.lastSeparated + S.logIndex) hu w).1
      have h1 := S.abs_formProductMean_sub_zero_le h (d := S.logIndex) (by omega) (S.sideAtLevel_eq _) B _ hv
        (h.cutoff (S.lastSeparated + S.logIndex) (by omega) (by omega) _ (S.sideAtLevel_eq _) _ _ hg)
      refine h1.trans ?_
      have hs0 : 0 ≤ S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature (S.lastSeparated + S.logIndex)
          (S.sideAtLevel (S.lastSeparated + S.logIndex)) (S.stateAtLevel (S.lastSeparated + S.logIndex) hu w).1 := by
        positivity
      have h2 := one_add_mul_pow_le hs0 (k := 2 * B.card) (by have := S.card_le_eight h B; omega)
      rw [← mul_assoc] at h2
      have h3 := mul_le_mul_of_nonneg_left h2
        (abs_nonneg (CM * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4)))
      rw [← mul_assoc] at h3
      exact h3.trans (le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) hG0))
    · have e2 : formMeanObs S.lastSeparated S.logIndex B S w = 0 := by
        rw [S.formMeanObs_of_le B hu]
        exact if_neg hg
      have e3 : goodCurvaturePower (S.lastSeparated + S.logIndex) (2 * B.card) S w = 0 := by
        rw [S.goodCurvaturePower_of_le _ hu]
        exact if_neg hg
      have e4 : notGoodIndicator (S.lastSeparated + S.logIndex) S w = 1 := by
        rw [S.notGoodIndicator_of_le hu]
        exact if_neg hg
      rw [e2, e3, e4, zero_sub, abs_neg, mul_zero, zero_add, mul_one]
      exact hp0
private theorem isBlockTorusSide_lastSeparated (h : PointBounds S CM CM1 CO C₀ cE) :
    IsBlockTorusSide Λ.stepParams (S.levelSide S.lastSeparated) := by
  have hwin := h.window
  refine ⟨Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _, S.side_le.trans ?_⟩
  exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)))
private theorem lead_at_good (h : PointBounds S CM CM1 CO C₀ cE) (hC₀ : 0 ≤ C₀)
    (hf₁ : (S.range : ℝ) ^ 3 * (S.scaleCoupling ^ ((1 : ℝ) / 2))⁻¹ ≤ 1)
    (hf₂ : (S.scaleCoupling ^ ((1 : ℝ) / 2)) ^ 3 * Real.exp (-(cE * (S.range : ℝ) ^ 2)) ≤ 1)
    (B : Finset (Fin Λ.k)) :
    ∀ (n : ℕ) [NeZero n], n = S.levelSide S.lastSeparated → ∀ᵐ z ∂(S.law S.lastSeparated n),
      z ∈ S.goodSet S.lastSeparated n →
      |S.scaleCoupling ^ B.card * ∏ i ∈ B, S.supportTotal S.lastSeparated n i (S.state S.lastSeparated n z) -
          S.formProductMean 0 n B (S.cutoffColourForm S.lastSeparated n (S.state S.lastSeparated n z).1)| ≤
        (S.range : ℝ) ^ 3 * (S.scaleCoupling ^ ((1 : ℝ) / 2))⁻¹ * (2 * (3 * C₀ + 1) * (S.range : ℝ) ^ 4) ^ B.card *
          ((1 + S.scaleCoupling ^ ((1 : ℝ) / 2) *
              S.localCurvature S.lastSeparated n (S.state S.lastSeparated n z).1) ^ (6 * B.card) +
            (∏ i ∈ B, S.meanScore S.lastSeparated n i (S.state S.lastSeparated n z)) ^ 2) := by
  intro n _ hn
  subst hn
  have hwin := h.window
  have htK : S.lastSeparated ≤ S.data.windowLevel := by omega
  have hrow := resp_isAdmissible S htK
  have hs0 : ∀ w, 0 ≤ (S.resp S.lastSeparated).score w := hrow.price.nonneg
  have hxone := h.one_le_coupling
  have hxpos : 0 < S.scaleCoupling := by linarith
  have hs : 1 ≤ S.scaleCoupling ^ ((1 : ℝ) / 2) := Real.one_le_rpow hxone (by norm_num)
  have hxs : S.scaleCoupling = (S.scaleCoupling ^ ((1 : ℝ) / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    norm_num
  have hsinv : S.scaleCoupling ^ (-(1 / 2) : ℝ) = (S.scaleCoupling ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg hxpos.le]
  have hr : (1 : ℝ) ≤ S.range := by
    have h1 : (1 : ℝ) ≤ S.scaleCoupling ^ ((1 : ℝ) / 100) := Real.one_le_rpow hxone (by norm_num)
    have h2 : S.scaleCoupling ^ ((1 : ℝ) / 100) ≤ (S.range : ℝ) := Nat.le_ceil _
    linarith
  filter_upwards [h.live S.lastSeparated htK _ (S.isBlockTorusSide_lastSeparated h)] with z hz hg
  rw [h.zero]
  refine abs_scaled_prod_sub_le B
    (Fi := fun i => S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
      (S.state S.lastSeparated (S.levelSide S.lastSeparated) z))
    (Ni := fun i => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
      (S.state S.lastSeparated (S.levelSide S.lastSeparated) z))
    (Qi := fun i => colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i)
      (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated)
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) z).1)
      (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated)
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) z).1))
    (E := Real.exp (-(cE * (S.range : ℝ) ^ 2)))
    hs hxs hr hf₁ hC₀ (Real.exp_pos _).le hf₂ (S.localCurvature_nonneg _ _ _)
    (fun i => one_le_meanScore S S.lastSeparated (S.levelSide S.lastSeparated) hs0 i _) (fun i => ?_)
  have := h.near i (S.state S.lastSeparated (S.levelSide S.lastSeparated) z) hz hg
  rw [hsinv] at this
  exact this
private def scoreList (B : Finset (Fin Λ.k)) : List (Fin Λ.k) := 0 :: (B.toList ++ B.toList)
private theorem lead_relation (h : PointBounds S CM CM1 CO C₀ cE) (hC₀ : 0 ≤ C₀)
    (hf₁ : (S.range : ℝ) ^ 3 * (S.scaleCoupling ^ ((1 : ℝ) / 2))⁻¹ ≤ 1)
    (hf₂ : (S.scaleCoupling ^ ((1 : ℝ) / 2)) ^ 3 * Real.exp (-(cE * (S.range : ℝ) ^ 2)) ≤ 1) {t : ℕ}
    (ht : S.lastSeparated = t) (B : Finset (Fin Λ.k)) :
    ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)),
      |S.scaleCoupling ^ B.card * responseProduct B S w - formMeanObs t 0 B S w| ≤
        (S.range : ℝ) ^ 3 * (S.scaleCoupling ^ ((1 : ℝ) / 2))⁻¹ * (2 * (3 * C₀ + 1) * (S.range : ℝ) ^ 4) ^ B.card *
          (goodCurvaturePower (t + 0) (6 * B.card) S w + meanScoreProduct (scoreList B) S w) +
        S.scaleCoupling ^ B.card * badResponseProduct B S w := by
  classical
  subst ht
  have htK : S.lastSeparated ≤ S.data.windowLevel := S.lastSeparated_le
  have hu' : S.lastSeparated + 0 ≤ S.data.windowLevel := htK
  have hrow := resp_isAdmissible S htK
  have hs0 : ∀ w, 0 ≤ (S.resp S.lastSeparated).score w := hrow.price.nonneg
  have hxone := h.one_le_coupling
  have hxb : 0 ≤ S.scaleCoupling ^ B.card := by positivity
  have hA : 0 ≤ (S.range : ℝ) ^ 3 * (S.scaleCoupling ^ ((1 : ℝ) / 2))⁻¹ *
      (2 * (3 * C₀ + 1) * (S.range : ℝ) ^ 4) ^ B.card := by positivity
  filter_upwards [S.ae_of_sampleAtLevel h S.lastSeparated htK (S.lead_at_good h hC₀ hf₁ hf₂ B _ (S.sideAtLevel_eq _))]
    with w hw
  have hN1 : ∀ i, 1 ≤ S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i (S.stateAtLevel S.lastSeparated htK w) :=
    fun i => one_le_meanScore S S.lastSeparated _ hs0 i _
  have hsc : (∏ i ∈ B, S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i
      (S.stateAtLevel S.lastSeparated htK w)) ^ 2 ≤ meanScoreProduct (scoreList B) S w := by
    show _ ≤ (((0 : Fin Λ.k) :: (B.toList ++ B.toList)).map fun i =>
      S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i
        (S.stateAtLevel S.lastSeparated S.lastSeparated_le w)).prod
    simp only [List.map_cons, List.prod_cons, List.map_append, List.prod_append, Finset.prod_map_toList]
    have h1 := hN1 0
    have h2 : 0 ≤ (∏ i ∈ B, S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i
        (S.stateAtLevel S.lastSeparated htK w)) *
        ∏ i ∈ B, S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i
          (S.stateAtLevel S.lastSeparated htK w) := mul_self_nonneg _
    rw [sq]
    exact le_mul_of_one_le_left h2 h1
  have hP0 : 0 ≤ meanScoreProduct (scoreList B) S w := (sq_nonneg _).trans hsc
  have hC0 := S.goodCurvaturePower_nonneg h (S.lastSeparated + 0) (6 * B.card) w
  by_cases hg : S.IsGoodConfig S.lastSeparated (S.sideAtLevel S.lastSeparated)
    (S.stateAtLevel S.lastSeparated htK w).1 (S.stateAtLevel S.lastSeparated htK w).2.1
  · have e1 : formMeanObs S.lastSeparated 0 B S w = S.formProductMean 0 (S.sideAtLevel S.lastSeparated) B
        (S.cutoffColourForm S.lastSeparated (S.sideAtLevel S.lastSeparated)
          (S.stateAtLevel S.lastSeparated htK w).1) := by
      rw [S.formMeanObs_of_le B hu']
      exact if_pos hg
    have e2 : goodCurvaturePower (S.lastSeparated + 0) (6 * B.card) S w =
        (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature S.lastSeparated (S.sideAtLevel S.lastSeparated)
          (S.stateAtLevel S.lastSeparated htK w).1) ^ (6 * B.card) := by
      rw [S.goodCurvaturePower_of_le _ hu']
      exact if_pos hg
    have e3 : badResponseProduct B S w = 0 := if_pos hg
    rw [e1, e2, e3, mul_zero, add_zero]
    refine (hw hg).trans (mul_le_mul_of_nonneg_left ?_ hA)
    exact add_le_add_right hsc _
  · have e1 : formMeanObs S.lastSeparated 0 B S w = 0 := by
      rw [S.formMeanObs_of_le B hu']
      exact if_neg hg
    have e3 : badResponseProduct B S w = ∏ i ∈ B, |S.supportTotal S.lastSeparated (S.sideAtLevel S.lastSeparated) i
        (S.stateAtLevel S.lastSeparated S.lastSeparated_le w)| := if_neg hg
    have e4 : |S.scaleCoupling ^ B.card * responseProduct B S w| = S.scaleCoupling ^ B.card *
        ∏ i ∈ B, |S.supportTotal S.lastSeparated (S.sideAtLevel S.lastSeparated) i
          (S.stateAtLevel S.lastSeparated S.lastSeparated_le w)| := by
      rw [abs_mul, abs_of_nonneg hxb]
      exact congrArg _ (Finset.abs_prod _ _)
    rw [e1, e3, sub_zero, e4]
    exact le_add_of_nonneg_left (mul_nonneg hA (add_nonneg hC0 hP0))
private theorem badResponseProduct_eq {t : ℕ} (ht : S.lastSeparated = t) (B : Finset (Fin Λ.k))
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    badResponseProduct B S w = notGoodIndicator t S w * |responseProduct B S w| := by
  classical
  subst ht
  have e : |responseProduct B S w| = ∏ i ∈ B, |S.supportTotal S.lastSeparated (S.sideAtLevel S.lastSeparated) i
      (S.stateAtLevel S.lastSeparated S.lastSeparated_le w)| := Finset.abs_prod _ _
  rw [S.notGoodIndicator_of_le S.lastSeparated_le, e]
  by_cases hg : S.IsGoodConfig S.lastSeparated (S.sideAtLevel S.lastSeparated)
    (S.stateAtLevel S.lastSeparated S.lastSeparated_le w).1 (S.stateAtLevel S.lastSeparated S.lastSeparated_le w).2.1
  · rw [if_pos hg, zero_mul]
    exact if_pos hg
  · rw [if_neg hg, one_mul]
    exact if_neg hg
private theorem measurable_meanScoreProduct (h : PointBounds S CM CM1 CO C₀ cE) (J : List (Fin Λ.k)) :
    Measurable (meanScoreProduct J S) := by
  have htK : S.lastSeparated ≤ S.data.windowLevel := S.lastSeparated_le
  have hq := (h.stage_measurable S.lastSeparated (S.sideAtLevel S.lastSeparated)).comp
    (S.sampleAtLevel_map h S.lastSeparated htK).1
  have hsm : Measurable (S.resp S.lastSeparated).score := (resp_isAdmissible S htK).price.borel
  have hN : ∀ i, Measurable fun w => S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i
      (S.stateAtLevel S.lastSeparated S.lastSeparated_le w) := fun i =>
    (measurable_meanScore S S.lastSeparated _ hsm i).comp hq
  unfold meanScoreProduct
  induction J with
  | nil => simpa using measurable_const
  | cons a J ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hN a).mul ih
private theorem lintegral_meanScoreProduct_pow_le (h : PointBounds S CM CM1 CO C₀ cE) {Cs : ℝ}
    (hsc : ∀ (p : ℕ), 1 ≤ p → ∀ J : List (Fin Λ.k), J.length = p →
      ∫⁻ w, ENNReal.ofReal (J.map fun i => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)).prod
          ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) ≤
        ENNReal.ofReal (Cs ^ p * (p.factorial : ℝ) ^ 6)) (J : List (Fin Λ.k)) (q : ℕ) :
    ∫⁻ w, ENNReal.ofReal (|meanScoreProduct J S w| ^ q) ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)) ≤
      ENNReal.ofReal (Cs ^ (q * J.length + 1) * ((q * J.length + 1).factorial : ℝ) ^ 6) := by
  have htK : S.lastSeparated ≤ S.data.windowLevel := S.lastSeparated_le
  have hsm : Measurable (S.resp S.lastSeparated).score := (resp_isAdmissible S htK).price.borel
  have hs0 : ∀ w, 0 ≤ (S.resp S.lastSeparated).score w := (resp_isAdmissible S htK).price.nonneg
  obtain ⟨m1, e1⟩ := S.sampleAtLevel_map h S.lastSeparated htK
  have hq := h.stage_measurable S.lastSeparated (S.sideAtLevel S.lastSeparated)
  have hf : Measurable fun x => ENNReal.ofReal (|(J.map fun i => S.meanScore S.lastSeparated
      (S.sideAtLevel S.lastSeparated) i (S.state S.lastSeparated (S.sideAtLevel S.lastSeparated) x)).prod| ^ q) := by
    refine ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp ?_).pow_const q)
    have hN : ∀ i, Measurable fun x => S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i
        (S.state S.lastSeparated (S.sideAtLevel S.lastSeparated) x) := fun i =>
      (measurable_meanScore S S.lastSeparated _ hsm i).comp hq
    induction J with
    | nil => simpa using measurable_const
    | cons a J ih =>
      simp only [List.map_cons, List.prod_cons]
      exact (hN a).mul ih
  have key : ∀ (n : ℕ) [NeZero n], n = S.levelSide S.lastSeparated →
      ∫⁻ x, ENNReal.ofReal (|(J.map fun i => S.meanScore S.lastSeparated n i (S.state S.lastSeparated n x)).prod| ^ q)
        ∂(S.law S.lastSeparated n) ≤
      ENNReal.ofReal (Cs ^ (q * J.length + 1) * ((q * J.length + 1).factorial : ℝ) ^ 6) := by
    intro n _ hn
    subst hn
    refine le_trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_)
      (hsc _ (by omega) (0 :: (List.replicate q J).flatten) ?_)
    · have hN1 := fun i => one_le_meanScore S S.lastSeparated (S.levelSide S.lastSeparated) hs0 i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) x)
      rw [List.map_cons, List.prod_cons, prod_flatten_replicate]
      have h1 := one_le_list_prod _ hN1 J
      rw [abs_of_nonneg (by linarith)]
      exact le_mul_of_one_le_left (by positivity) (hN1 0)
    · simp [length_flatten_replicate]
  have k := key (S.sideAtLevel S.lastSeparated) (S.sideAtLevel_eq _)
  rw [← e1, lintegral_map hf m1] at k
  exact k
end MomentPoint
end Relations
section Field
variable {Λ : MomentParameters}
private def windowObs (t N : ℕ) (B : Finset (Fin Λ.k)) : ℕ × ℕ × ℕ → SampleObservable Λ
  | (1, a, _) => if a ≤ N then formMeanObs t a B else oneObs
  | (2, a, _) => if a < N then liftObs t a B else oneObs
  | (3, a, _) => if a < N then caseMeanObs t a B else oneObs
  | (4, a, _) => if a ≤ N then notGoodIndicator (t + a) else oneObs
  | (5, a, b) => if a ≤ N then goodCurvaturePower (t + a) b else oneObs
  | (6, _, _) => badResponseProduct B
  | (7, _, _) => meanScoreProduct (MomentPoint.scoreList B)
  | _ => oneObs
private theorem hasBoundedMoments_of_bound {T : TranslatedLaws} {X : T.Family}
    (hp : ∀ i, IsProbabilityMeasure (T.μ i)) (hb : ∀ i, AEMeasurable (X i) (T.μ i))
    {C : ℝ} (hC : ∀ i, ∀ᵐ ω ∂(T.μ i), |X i ω| ≤ C) : TranslatedLaws.HasBoundedMoments X := by apply _root_.YangMills.SharedProofs.p39822 <;> assumption
private structure SequenceBounds (rule : ChainNoise.NoiseRule Λ.stepParams) (Sq : ℕ → MomentPoint Λ) (p t N : ℕ)
    (x : ℝ) (r : ℕ) (CM CM1 CO C₀ cE Cs : ℝ) : Prop where
  isPreserving : (translatedTori Sq p).IsPreserving
  bounds : ∀ i, PointBounds (Sq i) CM CM1 CO C₀ cE
  lastSeparated_eq : ∀ i, (Sq i).lastSeparated = t
  logIndex_eq : ∀ i, (Sq i).logIndex = N
  coupling_eq : ∀ i, (Sq i).scaleCoupling = x
  range_eq : ∀ i, (Sq i).range = r
  sample : ∀ i, Measurable ((Sq i).sampleOf rule) ∧
    (Sq i).sampleLaw.map ((Sq i).sampleOf rule) = (Sq i).law (Sq i).data.windowLevel ((Sq i).data.period Λ.stepParams.side)
  responses : ∀ B : Finset (Fin Λ.k), TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (responseProduct B))
  meanScores : ∀ i (q : ℕ) (J : List (Fin Λ.k)),
    ∫⁻ w, ENNReal.ofReal (|meanScoreProduct J (Sq i) w| ^ q)
        ∂((Sq i).law (Sq i).data.windowLevel ((Sq i).data.period Λ.stepParams.side)) ≤
      ENNReal.ofReal (Cs ^ (q * J.length + 1) * ((q * J.length + 1).factorial : ℝ) ^ 6)
namespace SequenceBounds
variable {rule : ChainNoise.NoiseRule Λ.stepParams} {Sq : ℕ → MomentPoint Λ} {p t N : ℕ} {x : ℝ} {r : ℕ}
  {CM CM1 CO C₀ cE Cs : ℝ}
private theorem aemeasurable_sampleFamily (h : SequenceBounds rule Sq p t N x r CM CM1 CO C₀ cE Cs)
    {g : SampleObservable Λ} (i : ℕ)
    (hg : AEMeasurable (g (Sq i)) ((Sq i).law (Sq i).data.windowLevel ((Sq i).data.period Λ.stepParams.side))) :
    AEMeasurable (sampleFamily rule Sq p g i) ((translatedTori Sq p).μ i) := by
  rw [← (h.sample i).2] at hg
  exact hg.comp_measurable (h.sample i).1
private theorem ae_sampleOf (h : SequenceBounds rule Sq p t N x r CM CM1 CO C₀ cE Cs) (i : ℕ)
    {P : MarkedSample Λ.stepParams (Sq i).data.windowLevel ((Sq i).data.period Λ.stepParams.side) → Prop}
    (hP : ∀ᵐ w ∂((Sq i).law (Sq i).data.windowLevel ((Sq i).data.period Λ.stepParams.side)), P w) :
    ∀ᵐ ω ∂((Sq i).sampleLaw), P ((Sq i).sampleOf rule ω) := by
  rw [← (h.sample i).2] at hP
  exact ae_of_ae_map (h.sample i).1.aemeasurable hP
private theorem hasBoundedMoments_of_ae_bound (h : SequenceBounds rule Sq p t N x r CM CM1 CO C₀ cE Cs)
    {g : SampleObservable Λ} {C : ℝ}
    (hg : ∀ i, AEMeasurable (g (Sq i)) ((Sq i).law (Sq i).data.windowLevel ((Sq i).data.period Λ.stepParams.side)))
    (hC : ∀ i, ∀ᵐ w ∂((Sq i).law (Sq i).data.windowLevel ((Sq i).data.period Λ.stepParams.side)), |g (Sq i) w| ≤ C) :
    TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p g) :=
  hasBoundedMoments_of_bound h.isPreserving.isProbability (fun i => h.aemeasurable_sampleFamily i (hg i))
    (fun i => h.ae_sampleOf i (hC i))
private theorem goodBound_eq (h : SequenceBounds rule Sq p t N x r CM CM1 CO C₀ cE Cs) (i : ℕ) (B : Finset (Fin Λ.k)) :
    (Sq i).goodBound CM B = |CM * (r : ℝ) ^ (4 * B.card)| * (121 ^ 16 * x ^ 4) := by
  unfold MomentPoint.goodBound
  rw [h.range_eq i, h.coupling_eq i]
private theorem window_le_windowLevel (h : SequenceBounds rule Sq p t N x r CM CM1 CO C₀ cE Cs) (i : ℕ) {a : ℕ}
    (ha : a ≤ N + 1) : t + a + 1 ≤ (Sq i).data.windowLevel := by
  have h1 := (h.bounds i).window
  have h2 := h.lastSeparated_eq i
  have h3 := h.logIndex_eq i
  omega
private theorem hasBoundedMoments_one (h : SequenceBounds rule Sq p t N x r CM CM1 CO C₀ cE Cs) :
    TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (oneObs (Λ := Λ))) :=
  h.hasBoundedMoments_of_ae_bound (C := 1) (fun _ => measurable_const.aemeasurable)
    (fun _ => ae_of_all _ fun _ => by simp [oneObs])
private theorem abs_formMeanObs_le_bound (h : SequenceBounds rule Sq p t N x r CM CM1 CO C₀ cE Cs)
    (B : Finset (Fin Λ.k)) {a : ℕ} (ha : a ≤ N + 1) (i : ℕ)
    (w : MarkedSample Λ.stepParams (Sq i).data.windowLevel ((Sq i).data.period Λ.stepParams.side)) :
    |formMeanObs t a B (Sq i) w| ≤ |CM * (r : ℝ) ^ (4 * B.card)| * (121 ^ 16 * x ^ 4) := by
  have := (Sq i).abs_formMeanObs_le (h.bounds i) (h.lastSeparated_eq i) B (d := a) (by rw [h.logIndex_eq i]; exact ha) w
  rwa [h.goodBound_eq] at this
private theorem abs_goodCaseForms_le_bound (h : SequenceBounds rule Sq p t N x r CM CM1 CO C₀ cE Cs)
    (B : Finset (Fin Λ.k)) {a : ℕ} (ha : a ≤ N) (i : ℕ) (W Yt ωt bad b) :
    |(Sq i).goodCaseForms (t + a) a ((Sq i).sideAtLevel (t + a + 1)) B W Yt ωt bad b| ≤
      |CM * (r : ℝ) ^ (4 * B.card)| * (121 ^ 16 * x ^ 4) := by
  have hu := h.window_le_windowLevel i (a := a) (by omega)
  have hN := h.logIndex_eq i
  have ht := h.lastSeparated_eq i
  have key : ∀ {S' : MomentPoint Λ}, PointBounds S' CM CM1 CO C₀ cE → S'.lastSeparated = t → S'.logIndex = N →
      t + a + 1 ≤ S'.data.windowLevel → ∀ (W Yt ωt bad b),
      |S'.goodCaseForms (t + a) a (S'.sideAtLevel (t + a + 1)) B W Yt ωt bad b| ≤ S'.goodBound CM B := by
    intro S' hf ht' hN' hu' W Yt ωt bad b
    subst ht'
    exact S'.abs_goodCaseForms_le hf (by omega)
      (by rw [S'.sideAtLevel_eq]; exact (S'.levelSide_eq_succ_mul hu').symm) B W Yt ωt bad b
  have := key (h.bounds i) ht hN hu W Yt ωt bad b
  rwa [h.goodBound_eq] at this
private theorem hasBoundedMoments_window (h : SequenceBounds rule Sq p t N x r CM CM1 CO C₀ cE Cs)
    (B : Finset (Fin Λ.k)) :
    ∀ c, TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (windowObs t N B c))
  | (0, _, _) => h.hasBoundedMoments_one
  | (1, a, _) => by
    show TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (if a ≤ N then formMeanObs t a B else oneObs))
    by_cases ha : a ≤ N
    · rw [if_pos ha]
      exact h.hasBoundedMoments_of_ae_bound (fun i => ((Sq i).measurable_formMeanObs (h.bounds i) B
          (by have := h.window_le_windowLevel i (a := a) (by omega); omega)).aemeasurable)
        (fun i => ae_of_all _ (h.abs_formMeanObs_le_bound B (by omega) i))
    · rw [if_neg ha]
      exact h.hasBoundedMoments_one
  | (2, a, _) => by
    show TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (if a < N then liftObs t a B else oneObs))
    by_cases ha : a < N
    · rw [if_pos ha]
      have e : ∀ i, liftObs t a B (Sq i) = formMeanObs t a B (Sq i) := fun i => funext fun w =>
        (Sq i).liftObs_eq (h.bounds i) B (h.window_le_windowLevel i (by omega)) w
      refine h.hasBoundedMoments_of_ae_bound (C := |CM * (r : ℝ) ^ (4 * B.card)| * (121 ^ 16 * x ^ 4))
        (fun i => ?_) (fun i => ae_of_all _ fun w => ?_)
      · rw [e i]
        exact ((Sq i).measurable_formMeanObs (h.bounds i) B
          (by have := h.window_le_windowLevel i (a := a) (by omega); omega)).aemeasurable
      · rw [e i]
        exact h.abs_formMeanObs_le_bound B (by omega) i w
    · rw [if_neg ha]
      exact h.hasBoundedMoments_one
  | (3, a, _) => by
    show TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (if a < N then caseMeanObs t a B else oneObs))
    by_cases ha : a < N
    · rw [if_pos ha]
      have e := fun i => (Sq i).caseMeanObs_step (h.bounds i) (h.lastSeparated_eq i) (d := a)
        (by rw [h.logIndex_eq i]; exact ha) B
      refine h.hasBoundedMoments_of_ae_bound (C := |CM * (r : ℝ) ^ (4 * B.card)| * (121 ^ 16 * x ^ 4))
        (fun i => (e i).1.aemeasurable) (fun i => ?_)
      have := (e i).2.1
      rwa [h.goodBound_eq] at this
    · rw [if_neg ha]
      exact h.hasBoundedMoments_one
  | (4, a, _) => by
    show TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (if a ≤ N then notGoodIndicator (t + a) else oneObs))
    by_cases ha : a ≤ N
    · rw [if_pos ha]
      exact h.hasBoundedMoments_of_ae_bound (C := 1) (fun i => ((Sq i).measurable_notGoodIndicator (h.bounds i)
        (by have := h.window_le_windowLevel i (a := a) (by omega); omega)).aemeasurable)
        (fun i => ae_of_all _ ((Sq i).abs_notGoodIndicator_le _))
    · rw [if_neg ha]
      exact h.hasBoundedMoments_one
  | (5, a, b) => by
    show TranslatedLaws.HasBoundedMoments
      (sampleFamily rule Sq p (if a ≤ N then goodCurvaturePower (t + a) b else oneObs))
    by_cases ha : a ≤ N
    · rw [if_pos ha]
      refine h.hasBoundedMoments_of_ae_bound (C := (1 + x ^ ((1 : ℝ) / 4)) ^ b)
        (fun i => ((Sq i).measurable_goodCurvaturePower (h.bounds i)
          (by have := h.window_le_windowLevel i (a := a) (by omega); omega) b).aemeasurable)
        (fun i => ae_of_all _ fun w => ?_)
      have := (Sq i).abs_goodCurvaturePower_le (h.bounds i) (t + a) b w
      rwa [h.coupling_eq i] at this
    · rw [if_neg ha]
      exact h.hasBoundedMoments_one
  | (6, _, _) => by
    show TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (badResponseProduct B))
    have e : ∀ i ω, sampleFamily rule Sq p (badResponseProduct B) i ω =
        notGoodIndicator t (Sq i) ((Sq i).sampleOf rule ω) * |sampleFamily rule Sq p (responseProduct B) i ω| :=
      fun i ω => (Sq i).badResponseProduct_eq (h.lastSeparated_eq i) B _
    refine ⟨fun i => ?_, fun q => ?_⟩
    · have e' : sampleFamily rule Sq p (badResponseProduct B) i = fun ω =>
          notGoodIndicator t (Sq i) ((Sq i).sampleOf rule ω) * |sampleFamily rule Sq p (responseProduct B) i ω| :=
        funext (e i)
      rw [e']
      have hu : t ≤ (Sq i).data.windowLevel := by have := h.window_le_windowLevel i (a := 0) (by omega); omega
      exact ((((Sq i).measurable_notGoodIndicator (h.bounds i) hu).comp (h.sample i).1).aemeasurable).mul
        (continuous_abs.measurable.comp_aemeasurable ((h.responses B).aemeasurable i))
    · obtain ⟨C, hC⟩ := (h.responses B).moment_bound q
      refine ⟨C, fun i => (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_).trans (hC i)⟩
      rw [e i ω]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
      rw [abs_mul, abs_abs]
      exact mul_le_of_le_one_left (abs_nonneg _) ((Sq i).abs_notGoodIndicator_le _ _)
  | (7, _, _) => by
    show TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (meanScoreProduct (MomentPoint.scoreList B)))
    refine ⟨fun i => h.aemeasurable_sampleFamily i ((Sq i).measurable_meanScoreProduct (h.bounds i) _).aemeasurable,
      fun q => ⟨Cs ^ (q * (MomentPoint.scoreList B).length + 1) *
        ((q * (MomentPoint.scoreList B).length + 1).factorial : ℝ) ^ 6, fun i => ?_⟩⟩
    have hm := ((Sq i).measurable_meanScoreProduct (h.bounds i) (MomentPoint.scoreList B))
    have k := h.meanScores i q (MomentPoint.scoreList B)
    have hf : Measurable fun w => ENNReal.ofReal (|meanScoreProduct (MomentPoint.scoreList B) (Sq i) w| ^ q) :=
      ((continuous_abs.measurable.comp hm).pow_const q).ennreal_ofReal
    rw [← (h.sample i).2, lintegral_map hf (h.sample i).1] at k
    exact k
  | (_ + 8, _, _) => h.hasBoundedMoments_one
end SequenceBounds
end Field
section Main
variable {Λ : MomentParameters}
private theorem windowObs_forms {t N a b : ℕ} (B : Finset (Fin Λ.k)) (ha : a ≤ N) :
    windowObs t N B (1, a, b) = formMeanObs t a B := if_pos ha
private theorem windowObs_lift {t N a b : ℕ} (B : Finset (Fin Λ.k)) (ha : a < N) :
    windowObs t N B (2, a, b) = liftObs t a B := if_pos ha
private theorem windowObs_mean {t N a b : ℕ} (B : Finset (Fin Λ.k)) (ha : a < N) :
    windowObs t N B (3, a, b) = caseMeanObs t a B := if_pos ha
private theorem windowObs_bad {t N a b : ℕ} (B : Finset (Fin Λ.k)) (ha : a ≤ N) :
    windowObs t N B (4, a, b) = notGoodIndicator (t + a) := if_pos ha
private theorem windowObs_curv {t N a b : ℕ} (B : Finset (Fin Λ.k)) (ha : a ≤ N) :
    windowObs t N B (5, a, b) = goodCurvaturePower (t + a) b := if_pos ha
private def MomentPoint.windowBound (S : MomentPoint Λ) (CG : ℕ → ℝ) (Cq CO CM CM1 C₀ : ℝ) (B : Finset (Fin Λ.k)) : ℝ :=
      (S.range : ℝ) ^ 3 * (S.scaleCoupling ^ ((1 : ℝ) / 2))⁻¹ * (2 * (3 * C₀ + 1) * (S.range : ℝ) ^ 4) ^ B.card *
          (CG (6 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 4000) +
            Cq ^ (2 * B.card + 1) * ((2 * B.card + 1).factorial : ℝ) ^ 6) +
        S.scaleCoupling ^ B.card * (CG (B.card + 1) * S.scaleCoupling ^ (-((B.card + 1 : ℕ) : ℝ))) +
        S.logIndex * (|CO * (S.range : ℝ) ^ (4 * B.card + 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ)| *
            (|CG (2 * B.card + 1)| * S.scaleCoupling ^ ((1 : ℝ) / 4000)) +
          |CM * (S.range : ℝ) ^ (4 * B.card)| * (121 ^ 16 * S.scaleCoupling ^ 4) *
            (|CG 5| * S.scaleCoupling ^ (-((5 : ℕ) : ℝ)))) +
        (|CM * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4)| * 120 ^ 16 *
            (CG (2 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 4000)) +
          |CM * (S.range : ℝ) ^ (4 * B.card)| * (CG 1 * S.scaleCoupling ^ (-((1 : ℕ) : ℝ))) +
          (|CM1| + 1) * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4))
private theorem ae_bound_in_window_law (hMn : jointLimitPropertiesStatement)
    {CM CM1 CO C₀ cE Cs Cq X₀ : ℝ} {CG : ℕ → ℝ}
    (hGS : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S), X₀ ≤ S.scaleCoupling →
      (∀ u : ℕ, (∀ i, (F.points i).lastSeparated ≤ u ∧ u ≤ (F.points i).lastSeparated + S.logIndex + 1) →
        (∀ (N : ℕ) (j : F.Index), F.observables j = notGoodIndicator u →
          ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ CG N * S.scaleCoupling ^ (-(N : ℝ))) ∧
        ∀ (k : ℕ) (j : F.Index), F.observables j = goodCurvaturePower u k →
          ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ CG k * S.scaleCoupling ^ ((1 : ℝ) / 4000)) ∧
      ∀ (B : Finset (Fin Λ.k)) (N : ℕ) (j : F.Index), F.observables j = badResponseProduct B →
        ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ CG N * S.scaleCoupling ^ (-(N : ℝ)))
    (hMS : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (p : ℕ), 1 ≤ p →
      ∀ (J : List (Fin Λ.k)) (j : F.Index), J.length = p → F.observables j = meanScoreProduct J →
        ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ Cq ^ p * (p.factorial : ℝ) ^ 6)
    (hFar : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (u : ℕ) (hu : ∀ i, u + 1 ≤ (F.points i).data.windowLevel)
      (Φ : ∀ i, TorusField ((F.points i).sideAtLevel (u + 1)) →
        CaseFunction ((F.points i).tower.stage u).toStepSetup ((F.points i).sideAtLevel (u + 1)))
      (Rr a : ℕ) (Sz : ℝ) (A : ∀ i, Finset (TorusSite ((F.points i).sideAtLevel (u + 1) * Λ.stepParams.side)))
      (o : ∀ i, TorusSite ((F.points i).sideAtLevel (u + 1) * Λ.stepParams.side))
      (sz : ∀ i, ((F.points i).tower.stage u).toStepSetup.labels.Ω → ℝ) (jX jE jR : F.Index),
      (∀ i V, IsQuasiLocalCaseFunction ((F.points i).tower.stage u).toStepSetup (o i) Rr a Sz (A i) (sz i) (Φ i V)) →
      (∀ i, Measurable (FreeEnergies.caseLift (F.points i).tower u _ (Φ i))) →
      (∀ i, ∀ᵐ x ∂(markedSampleLaw (F.points i).tower (F.points i).β (u + 1) ((F.points i).sideAtLevel (u + 1))),
        FreeEnergies.CaseIntegrableAtSample (F.points i).tower u _ (Φ i) x) →
      (∃ C : ℝ, ∀ i, ∫⁻ x, ENNReal.ofReal (supportWeightOfSample (F.points i).tower u _ (A i) (sz i) x)
        ∂(markedSampleLaw (F.points i).tower (F.points i).β (u + 1) ((F.points i).sideAtLevel (u + 1))) ≤
          ENNReal.ofReal C) →
      (∀ i w, F.observables jX (F.points i) w =
        FreeEnergies.caseLift (F.points i).tower u _ (Φ i) ((F.points i).sampleAtLevel (u + 1) (hu i) w)) →
      (∀ i w, F.observables jE (F.points i) w =
        FreeEnergies.caseMeanAtSample (F.points i).tower u _ (Φ i) ((F.points i).sampleAtLevel (u + 1) (hu i) w)) →
      (∃ C : ℝ, ∀ i w, |F.observables jR (F.points i) w| ≤ C) →
      (∀ i, IsMeasurableAbove (F.points i) (u + 1) (F.observables jR (F.points i))) →
      F.condMean (fun v => v (jR, 0) * v (jX, 0)) =ᵐ[F.law] F.condMean (fun v => v (jR, 0) * v (jE, 0)))
    (hFC : ∀ S : MomentPoint Λ, X₀ ≤ S.scaleCoupling → ∀ (u d n : ℕ) [NeZero n], n = S.levelSide (u + 1) →
      u + 1 ≤ S.data.windowLevel → u = S.lastSeparated + d → d ≤ S.logIndex →
      ∀ (B : Finset (Fin Λ.k)) (Sz : ℝ), (∀ W Yt ωt bad b, |S.goodCaseForms u d n B W Yt ωt bad b| ≤ Sz) →
        IsQuasiLocalCaseFunction (S.tower.stage u).toStepSetup (S.originSite u (n * Λ.stepParams.side))
          (8 * S.rangeSq + 2) 0 Sz ∅ (fun _ => 0) (S.goodCaseForms u d n B) ∧
          ∀ᵐ x ∂(markedSampleLaw S.tower S.β (u + 1) n),
            FreeEnergies.CaseIntegrableAtSample S.tower u n (fun _ => S.goodCaseForms u d n B) x)
    (hC₀ : 0 ≤ C₀)
    (hfl : ∀ S : MomentPoint Λ, X₀ ≤ S.scaleCoupling → (S.range : ℝ) ^ 3 * (S.scaleCoupling ^ ((1 : ℝ) / 2))⁻¹ ≤ 1 ∧
      (S.scaleCoupling ^ ((1 : ℝ) / 2)) ^ 3 * Real.exp (-(cE * (S.range : ℝ) ^ 2)) ≤ 1)
    (S : MomentPoint Λ) (hx : X₀ ≤ S.scaleCoupling) (F : LimitLawAtPoint S) {t : ℕ}
    (hq : SequenceBounds F.rule F.points F.period t S.logIndex S.scaleCoupling S.range CM CM1 CO C₀ cE Cs)
    (B : Finset (Fin Λ.k))
    (ι : ℕ × ℕ × ℕ → F.Index) (hι : ∀ c, F.observables (ι c) = windowObs t S.logIndex B c) (jr : F.Index)
    (hjr : F.observables jr = responseProduct B)
    (d : ℕ → ℕ)
    (μ : ∀ m, Measure (LevelChain Λ.stepParams.side ((F.points m).lastSeparated + d m)
      ((F.points m).data.period Λ.stepParams.side)))
    (hd : ∀ m, (F.points m).lastSeparated + d m = (F.points m).data.windowLevel)
    (hμ : ∀ m, IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling ((F.points m).lastSeparated + d m)
      ((F.points m).data.period Λ.stepParams.side)) (μ m)) {e : ℝ}
    (he : Tendsto (fun m => ∫ X, ∏ i ∈ B, (F.points m).halfForm (d m) ((F.points m).data.period Λ.stepParams.side) i X
      ∂(μ m)) atTop (𝓝 e))
    (hk : ∀ m, (F.points m).rangeSq = S.rangeSq) :
    ∀ᵐ v ∂F.law, |S.scaleCoupling ^ B.card * F.condMeanAt jr v - e| ≤
      S.windowBound CG Cq CO CM CM1 C₀ B := by
  classical
  have hF := F.isJointLimitLaw
  have hprob : IsProbabilityMeasure F.law := hF.isProbability
  have hcount := F.countable_index
  have hmom := fun j => F.hasBoundedMoments j
  have hMean := hMn (translatedTori F.points F.period) F.Index
    (fun j => sampleFamily F.rule F.points F.period (F.observables j)) F.law hq.isPreserving hmom hF
  have hint : ∀ c, Integrable (evalAtZero c) F.law := by
    intro c
    have h1 := (hMean.2.1 1 (fun _ => (c, 0))).1
    have e1 : (fun v : TranslateValues F.Index => ∏ _c : Fin 1, v (c, 0)) = evalAtZero c := by
      funext v
      simp [evalAtZero]
    rwa [e1] at h1
  have hfam : ∀ (c : F.Index) (g : SampleObservable Λ), F.observables c = g → ∀ i ω,
      sampleFamily F.rule F.points F.period (F.observables c) i ω = g (F.points i) ((F.points i).sampleOf F.rule ω) := by
    intro c g hg i ω
    rw [hg]
    rfl
  have hw : ∀ (c : ℕ × ℕ × ℕ) (g : SampleObservable Λ), windowObs t S.logIndex B c = g → ∀ i ω,
      sampleFamily F.rule F.points F.period (F.observables (ι c)) i ω =
        g (F.points i) ((F.points i).sampleOf F.rule ω) :=
    fun c g hg => hfam (ι c) g ((hι c).trans hg)
  have hxi : ∀ i, X₀ ≤ (F.points i).scaleCoupling := fun i => by rw [hq.coupling_eq i]; exact hx
  have hx1 : 1 ≤ S.scaleCoupling := by
    have := (hq.bounds 0).one_le_coupling
    rwa [hq.coupling_eq 0] at this
  have hx0 : 0 < S.scaleCoupling := by linarith
  have hxe : 0 ≤ S.scaleCoupling ^ ((1 : ℝ) / 4000) := Real.rpow_nonneg hx0.le _
  have hr1 : (1 : ℝ) ≤ S.range := by
    have h1 : (1 : ℝ) ≤ S.scaleCoupling ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx1 (by norm_num)
    have h2 : S.scaleCoupling ^ ((1 : ℝ) / 100) ≤ (S.range : ℝ) := Nat.le_ceil _
    linarith
  have hL : (0 : ℝ) < Λ.stepParams.side := by
    have := (hq.bounds 0).admissible.L_ge
    have h2 : 0 < Λ.stepParams.side := by omega
    exact_mod_cast h2
  have hLq : 0 < (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) := Real.rpow_pos_of_pos hL _
  have hs0 : 0 ≤ (S.scaleCoupling ^ ((1 : ℝ) / 2))⁻¹ := by positivity
  have hLead : ∀ᵐ v ∂F.law, |S.scaleCoupling ^ B.card * evalAtZero jr v - evalAtZero (ι (1, 0, 0)) v| ≤
      (S.range : ℝ) ^ 3 * (S.scaleCoupling ^ ((1 : ℝ) / 2))⁻¹ * (2 * (3 * C₀ + 1) * (S.range : ℝ) ^ 4) ^ B.card *
        (evalAtZero (ι (5, 0, 6 * B.card)) v + evalAtZero (ι (7, 0, 0)) v) +
        S.scaleCoupling ^ B.card * evalAtZero (ι (6, 0, 0)) v := by
    have h1 := ae_le_of_limit hF ![jr, ι (1, 0, 0), ι (5, 0, 6 * B.card), ι (7, 0, 0), ι (6, 0, 0)]
      (fun w => |S.scaleCoupling ^ B.card * w 0 - w 1|)
      (fun w => (S.range : ℝ) ^ 3 * (S.scaleCoupling ^ ((1 : ℝ) / 2))⁻¹ *
        (2 * (3 * C₀ + 1) * (S.range : ℝ) ^ 4) ^ B.card * (w 2 + w 3) + S.scaleCoupling ^ B.card * w 4)
      (by fun_prop) (by fun_prop) (Eventually.of_forall fun i => by
        have hl := (F.points i).lead_relation (hq.bounds i) hC₀ (hfl _ (hxi i)).1 (hfl _ (hxi i)).2
          (hq.lastSeparated_eq i) B
        rw [hq.coupling_eq i, hq.range_eq i] at hl
        filter_upwards [hq.ae_sampleOf i hl] with ω hω
        show |S.scaleCoupling ^ B.card * sampleFamily F.rule F.points F.period (F.observables jr) i ω -
            sampleFamily F.rule F.points F.period (F.observables (ι (1, 0, 0))) i ω| ≤
          (S.range : ℝ) ^ 3 * (S.scaleCoupling ^ ((1 : ℝ) / 2))⁻¹ * (2 * (3 * C₀ + 1) * (S.range : ℝ) ^ 4) ^ B.card *
            (sampleFamily F.rule F.points F.period (F.observables (ι (5, 0, 6 * B.card))) i ω +
              sampleFamily F.rule F.points F.period (F.observables (ι (7, 0, 0))) i ω) +
            S.scaleCoupling ^ B.card * sampleFamily F.rule F.points F.period (F.observables (ι (6, 0, 0))) i ω
        rw [hfam jr _ hjr, hw _ _ (windowObs_forms B (Nat.zero_le _)), hw _ _ (windowObs_curv B (Nat.zero_le _)),
          hw (7, 0, 0) _ rfl, hw (6, 0, 0) _ rfl]
        exact hω)
    exact h1
  have hStep : ∀ a, a < S.logIndex → ∀ᵐ v ∂F.law,
      |evalAtZero (ι (3, a, 0)) v - evalAtZero (ι (1, a + 1, 0)) v| ≤
      |CO * (S.range : ℝ) ^ (4 * B.card + 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ)| *
          evalAtZero (ι (5, a + 1, 2 * B.card + 1)) v +
        |CM * (S.range : ℝ) ^ (4 * B.card)| * (121 ^ 16 * S.scaleCoupling ^ 4) * evalAtZero (ι (4, a + 1, 0)) v := by
    intro a ha
    have h1 := ae_le_of_limit hF ![ι (3, a, 0), ι (1, a + 1, 0), ι (5, a + 1, 2 * B.card + 1), ι (4, a + 1, 0)]
      (fun w => |w 0 - w 1|)
      (fun w => |CO * (S.range : ℝ) ^ (4 * B.card + 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ)| * w 2 +
        |CM * (S.range : ℝ) ^ (4 * B.card)| * (121 ^ 16 * S.scaleCoupling ^ 4) * w 3)
      (by fun_prop) (by fun_prop) (Eventually.of_forall fun i => by
        have hl := ((F.points i).caseMeanObs_step (hq.bounds i) (hq.lastSeparated_eq i) (d := a)
          (by rw [hq.logIndex_eq i]; exact ha) B).2.2
        rw [hq.goodBound_eq i B, hq.coupling_eq i, hq.range_eq i] at hl
        filter_upwards [hq.ae_sampleOf i hl] with ω hω
        show |sampleFamily F.rule F.points F.period (F.observables (ι (3, a, 0))) i ω -
            sampleFamily F.rule F.points F.period (F.observables (ι (1, a + 1, 0))) i ω| ≤
          |CO * (S.range : ℝ) ^ (4 * B.card + 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ)| *
              sampleFamily F.rule F.points F.period (F.observables (ι (5, a + 1, 2 * B.card + 1))) i ω +
            |CM * (S.range : ℝ) ^ (4 * B.card)| * (121 ^ 16 * S.scaleCoupling ^ 4) *
              sampleFamily F.rule F.points F.period (F.observables (ι (4, a + 1, 0))) i ω
        rw [hw _ _ (windowObs_mean B ha), hw _ _ (windowObs_forms B ha), hw _ _ (windowObs_curv B ha),
          hw _ _ (windowObs_bad B ha)]
        exact hω)
    exact h1
  have hTop : ∀ᵐ v ∂F.law, |evalAtZero (ι (1, S.logIndex, 0)) v - e| ≤
      |CM * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4)| * 120 ^ 16 *
          evalAtZero (ι (5, S.logIndex, 2 * B.card)) v +
        |CM * (S.range : ℝ) ^ (4 * B.card)| * evalAtZero (ι (4, S.logIndex, 0)) v +
        (|CM1| + 1) * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) := by
    have hδ : 0 < (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) := by positivity
    have hev := he.eventually (Metric.closedBall_mem_nhds e hδ)
    have h1 := ae_le_of_limit hF ![ι (1, S.logIndex, 0), ι (5, S.logIndex, 2 * B.card), ι (4, S.logIndex, 0)]
      (fun w => |w 0 - e|)
      (fun w => |CM * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4)| * 120 ^ 16 *
          w 1 + |CM * (S.range : ℝ) ^ (4 * B.card)| * w 2 +
        (|CM1| + 1) * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4))
      (by fun_prop) (by fun_prop) (by
        filter_upwards [hev] with i hi
        obtain ⟨p₀, -, hc, hrel⟩ := (F.points i).formMeanObs_top (hq.bounds i) (hq.lastSeparated_eq i) B
        have hc' := hc (d i) (hd i) (μ i) (hμ i)
        rw [hq.logIndex_eq i, hq.range_eq i] at hc'
        rw [hq.logIndex_eq i, hq.range_eq i] at hrel
        refine ae_of_all _ fun ω => ?_
        have h2 := hrel ((F.points i).sampleOf F.rule ω)
        show |sampleFamily F.rule F.points F.period (F.observables (ι (1, S.logIndex, 0))) i ω - e| ≤
          |CM * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4)| * 120 ^ 16 *
              sampleFamily F.rule F.points F.period (F.observables (ι (5, S.logIndex, 2 * B.card))) i ω +
            |CM * (S.range : ℝ) ^ (4 * B.card)| *
              sampleFamily F.rule F.points F.period (F.observables (ι (4, S.logIndex, 0))) i ω +
            (|CM1| + 1) * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4)
        rw [hw _ _ (windowObs_forms B le_rfl), hw _ _ (windowObs_curv B le_rfl), hw _ _ (windowObs_bad B le_rfl)]
        have hi' : |(∫ X, ∏ l ∈ B, (F.points i).halfForm (d i) ((F.points i).data.period Λ.stepParams.side) l X
            ∂(μ i)) - e| ≤ (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) := by
          have := Metric.mem_closedBall.1 hi
          rwa [Real.dist_eq] at this
        have h3 := abs_sub_le (formMeanObs t S.logIndex B (F.points i) ((F.points i).sampleOf F.rule ω)) p₀ e
        have h4 := abs_sub_le p₀ (∫ X, ∏ l ∈ B, (F.points i).halfForm (d i)
          ((F.points i).data.period Λ.stepParams.side) l X ∂(μ i)) e
        have h5 : CM1 * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) ≤
            |CM1| * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) := by
          gcongr
          exact le_abs_self _
        have h6 : (|CM1| + 1) * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) =
            |CM1| * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) +
              (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) := by ring
        rw [h6]
        linarith)
    exact h1
  have hOne : evalAtZero (ι (0, 0, 0)) =ᵐ[F.law] fun _ => (1 : ℝ) := by
    have h1 := ae_eq_zero_of_limit hF ![ι (0, 0, 0)] (fun w => |w 0 - 1|) (by fun_prop) (fun _ => abs_nonneg _)
      (Eventually.of_forall fun i => ae_of_all _ fun ω => by
        show |sampleFamily F.rule F.points F.period (F.observables (ι (0, 0, 0))) i ω - 1| = 0
        rw [hw (0, 0, 0) oneObs rfl]
        simp [oneObs])
    filter_upwards [h1] with v hv
    have hv' : |v (ι (0, 0, 0), 0) - 1| = 0 := hv
    have := abs_eq_zero.1 hv'
    show v (ι (0, 0, 0), 0) = 1
    linarith
  have hStar : ∀ a, a < S.logIndex → F.law[evalAtZero (ι (1, a, 0))|shiftInvariantSigma F.Index] =ᵐ[F.law]
      F.law[evalAtZero (ι (3, a, 0))|shiftInvariantSigma F.Index] := by
    intro a ha
    have hu : ∀ i, t + a + 1 ≤ (F.points i).data.windowLevel := fun i => hq.window_le_windowLevel i (by omega)
    have hfar := hFar S F (t + a) hu
      (fun i _ => (F.points i).goodCaseForms (t + a) a ((F.points i).sideAtLevel (t + a + 1)) B) (8 * S.rangeSq + 2) 0
      (|CM * (S.range : ℝ) ^ (4 * B.card)| * (121 ^ 16 * S.scaleCoupling ^ 4)) (fun _ => ∅)
      (fun i => (F.points i).originSite (t + a) _) (fun _ _ => 0)
      (ι (2, a, 0)) (ι (3, a, 0)) (ι (0, 0, 0))
      (fun i V => by
        have := (hFC (F.points i) (hxi i) (t + a) a ((F.points i).sideAtLevel (t + a + 1))
          ((F.points i).sideAtLevel_eq _) (hu i) (by rw [hq.lastSeparated_eq i]) (by rw [hq.logIndex_eq i]; exact ha.le)
          B _ (hq.abs_goodCaseForms_le_bound B ha.le i)).1
        rwa [hk i] at this)
      (fun i => (F.points i).measurable_caseLift_goodCaseForms (hq.bounds i) _ _ _ B)
      (fun i => (hFC (F.points i) (hxi i) (t + a) a ((F.points i).sideAtLevel (t + a + 1))
        ((F.points i).sideAtLevel_eq _) (hu i) (by rw [hq.lastSeparated_eq i]) (by rw [hq.logIndex_eq i]; exact ha.le)
        B _ (hq.abs_goodCaseForms_le_bound B ha.le i)).2)
      ⟨1, fun i => by
        have hP := (hq.bounds i).isProbability (t + a + 1) ((F.points i).sideAtLevel (t + a + 1))
        have hP' : IsProbabilityMeasure (markedSampleLaw (F.points i).tower (F.points i).β (t + a + 1)
          ((F.points i).sideAtLevel (t + a + 1))) := hP
        simp [supportWeightOfSample]⟩
      (fun i w => by
        rw [hι, windowObs_lift B ha]
        exact dif_pos (hu i))
      (fun i w => by
        rw [hι, windowObs_mean B ha]
        exact dif_pos (hu i))
      ⟨1, fun i w => by
        rw [hι]
        show |(1 : ℝ)| ≤ 1
        simp⟩
      (fun i d' h => by
        have e1 : F.observables (ι (0, 0, 0)) (F.points i) = fun _ => 1 := by
          rw [hι]
          rfl
        rw [e1]
        exact measurable_const)
    have hL1 : evalAtZero (ι (2, a, 0)) =ᵐ[F.law] evalAtZero (ι (1, a, 0)) := by
      have h1 := ae_eq_zero_of_limit hF ![ι (2, a, 0), ι (1, a, 0)] (fun w => |w 0 - w 1|) (by fun_prop)
        (fun _ => abs_nonneg _)
        (Eventually.of_forall fun i => ae_of_all _ fun ω => by
          show |sampleFamily F.rule F.points F.period (F.observables (ι (2, a, 0))) i ω -
            sampleFamily F.rule F.points F.period (F.observables (ι (1, a, 0))) i ω| = 0
          rw [hw _ _ (windowObs_lift B ha), hw _ _ (windowObs_forms B ha.le),
            (F.points i).liftObs_eq (hq.bounds i) B (hu i), sub_self, abs_zero])
      filter_upwards [h1] with v hv
      have hv' : |v (ι (2, a, 0), 0) - v (ι (1, a, 0), 0)| = 0 := hv
      have := abs_eq_zero.1 hv'
      show v (ι (2, a, 0), 0) = v (ι (1, a, 0), 0)
      linarith
    have e1 : evalAtZero (ι (1, a, 0)) =ᵐ[F.law] fun v => v (ι (0, 0, 0), 0) * v (ι (2, a, 0), 0) := by
      filter_upwards [hOne, hL1] with v h1 h2
      have h1' : v (ι (0, 0, 0), 0) = 1 := h1
      have h2' : v (ι (2, a, 0), 0) = v (ι (1, a, 0), 0) := h2
      rw [h1', h2', one_mul]
      rfl
    have e2 : (fun v : TranslateValues F.Index => v (ι (0, 0, 0), 0) * v (ι (3, a, 0), 0)) =ᵐ[F.law]
        evalAtZero (ι (3, a, 0)) := by
      filter_upwards [hOne] with v h1
      have h1' : v (ι (0, 0, 0), 0) = 1 := h1
      show v (ι (0, 0, 0), 0) * v (ι (3, a, 0), 0) = v (ι (3, a, 0), 0)
      rw [h1', one_mul]
    exact (condExp_congr_ae e1).trans (hfar.trans (condExp_congr_ae e2))
  have hG := hGS S F hx
  have hrange : ∀ a, a ≤ S.logIndex → ∀ i, (F.points i).lastSeparated ≤ t + a ∧
      t + a ≤ (F.points i).lastSeparated + S.logIndex + 1 := fun a ha i => by
    rw [hq.lastSeparated_eq i]
    omega
  have bBad : ∀ a (N' : ℕ), a ≤ S.logIndex → ∀ᵐ v ∂F.law,
      F.condMeanAt (ι (4, a, 0)) v ≤ CG N' * S.scaleCoupling ^ (-(N' : ℝ)) := fun a N' ha =>
    (hG.1 (t + a) (hrange a ha)).1 N' _ ((hι _).trans (windowObs_bad B ha))
  have bCurv : ∀ a k, a ≤ S.logIndex → ∀ᵐ v ∂F.law,
      F.condMeanAt (ι (5, a, k)) v ≤ CG k * S.scaleCoupling ^ ((1 : ℝ) / 4000) := fun a k ha =>
    (hG.1 (t + a) (hrange a ha)).2 k _ ((hι _).trans (windowObs_curv B ha))
  have hlen : (MomentPoint.scoreList B).length = 2 * B.card + 1 := by
    simp [MomentPoint.scoreList]
    omega
  have hmain := condExp_window_chain (m := shiftInvariantSigma F.Index) (P := F.law) (N := S.logIndex)
    (R := evalAtZero jr) (T₂ := evalAtZero (ι (6, 0, 0)))
    (Ya := evalAtZero (ι (5, 0, 6 * B.card))) (Yb := evalAtZero (ι (7, 0, 0)))
    (Yt := evalAtZero (ι (5, S.logIndex, 2 * B.card)))
    (Gt := evalAtZero (ι (4, S.logIndex, 0))) (H := fun a => evalAtZero (ι (1, a, 0)))
    (E := fun a => evalAtZero (ι (3, a, 0)))
    (Yc := fun a => evalAtZero (ι (5, a + 1, 2 * B.card + 1))) (G := fun a => evalAtZero (ι (4, a + 1, 0)))
    (A₁ := CG (6 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 4000))
    (A₂ := Cq ^ (2 * B.card + 1) * ((2 * B.card + 1).factorial : ℝ) ^ 6)
    (A₃ := CG (B.card + 1) * S.scaleCoupling ^ (-((B.card + 1 : ℕ) : ℝ)))
    (A₄ := |CG (2 * B.card + 1)| * S.scaleCoupling ^ ((1 : ℝ) / 4000))
    (A₅ := |CG 5| * S.scaleCoupling ^ (-((5 : ℕ) : ℝ))) (A₆ := CG (2 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 4000))
    (A₇ := CG 1 * S.scaleCoupling ^ (-((1 : ℕ) : ℝ)))
    inf_le_right (hint _) (hint _) (hint _) (hint _) (hint _) (hint _) (fun _ _ => hint _) (fun _ _ => hint _)
    (fun _ _ => hint _) (fun _ _ => hint _)
    (by have : 0 ≤ 3 * C₀ + 1 := by linarith
        positivity) (by positivity) (abs_nonneg _) (by positivity) (by positivity) (abs_nonneg _)
    hLead hStep hTop hStar (bCurv 0 _ (Nat.zero_le _)) (hMS S F _ (by omega) _ _ hlen (hι (7, 0, 0)))
    (hG.2 B _ _ (hι (6, 0, 0)))
    (fun a ha => by
      filter_upwards [bCurv (a + 1) (2 * B.card + 1) ha] with v hv
      exact hv.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hxe))
    (fun a ha => by
      filter_upwards [bBad (a + 1) 5 ha] with v hv
      exact hv.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hx0.le _)))
    (bCurv S.logIndex _ le_rfl) (bBad S.logIndex 1 le_rfl) (by positivity)
  exact hmain
private theorem points_params_eq (S : MomentPoint Λ) (F : LimitLawAtPoint S) (i : ℕ) :
    (F.points i).scaleCoupling = S.scaleCoupling ∧ (F.points i).range = S.range ∧
      (F.points i).logIndex = S.logIndex ∧ (F.points i).rangeSq = S.rangeSq := by
  obtain ⟨a, b, e⟩ := F.points_eq i
  rw [e]
  exact ⟨rfl, rfl, rfl, rfl⟩
private theorem exists_subseq_const_lastSeparated (S : MomentPoint Λ) (F : LimitLawAtPoint S) :
    ∃ (t : ℕ) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ i, (F.points (φ i)).lastSeparated = t := by apply _root_.YangMills.SharedProofs.p85868 <;> assumption
private theorem ae_bound_in_limit_law (hExt : jointLimitExtendStatement) (hMn : jointLimitPropertiesStatement)
    {CM CM1 CO C₀ cE Cs Cq X₀ : ℝ} {CG : ℕ → ℝ}
    (hGS : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S), X₀ ≤ S.scaleCoupling →
      (∀ u : ℕ, (∀ i, (F.points i).lastSeparated ≤ u ∧ u ≤ (F.points i).lastSeparated + S.logIndex + 1) →
        (∀ (N : ℕ) (j : F.Index), F.observables j = notGoodIndicator u →
          ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ CG N * S.scaleCoupling ^ (-(N : ℝ))) ∧
        ∀ (k : ℕ) (j : F.Index), F.observables j = goodCurvaturePower u k →
          ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ CG k * S.scaleCoupling ^ ((1 : ℝ) / 4000)) ∧
      ∀ (B : Finset (Fin Λ.k)) (N : ℕ) (j : F.Index), F.observables j = badResponseProduct B →
        ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ CG N * S.scaleCoupling ^ (-(N : ℝ)))
    (hMS : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (p : ℕ), 1 ≤ p →
      ∀ (J : List (Fin Λ.k)) (j : F.Index), J.length = p → F.observables j = meanScoreProduct J →
        ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ Cq ^ p * (p.factorial : ℝ) ^ 6)
    (hFar : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (u : ℕ) (hu : ∀ i, u + 1 ≤ (F.points i).data.windowLevel)
      (Φ : ∀ i, TorusField ((F.points i).sideAtLevel (u + 1)) →
        CaseFunction ((F.points i).tower.stage u).toStepSetup ((F.points i).sideAtLevel (u + 1)))
      (Rr a : ℕ) (Sz : ℝ) (A : ∀ i, Finset (TorusSite ((F.points i).sideAtLevel (u + 1) * Λ.stepParams.side)))
      (o : ∀ i, TorusSite ((F.points i).sideAtLevel (u + 1) * Λ.stepParams.side))
      (sz : ∀ i, ((F.points i).tower.stage u).toStepSetup.labels.Ω → ℝ) (jX jE jR : F.Index),
      (∀ i V, IsQuasiLocalCaseFunction ((F.points i).tower.stage u).toStepSetup (o i) Rr a Sz (A i) (sz i) (Φ i V)) →
      (∀ i, Measurable (FreeEnergies.caseLift (F.points i).tower u _ (Φ i))) →
      (∀ i, ∀ᵐ x ∂(markedSampleLaw (F.points i).tower (F.points i).β (u + 1) ((F.points i).sideAtLevel (u + 1))),
        FreeEnergies.CaseIntegrableAtSample (F.points i).tower u _ (Φ i) x) →
      (∃ C : ℝ, ∀ i, ∫⁻ x, ENNReal.ofReal (supportWeightOfSample (F.points i).tower u _ (A i) (sz i) x)
        ∂(markedSampleLaw (F.points i).tower (F.points i).β (u + 1) ((F.points i).sideAtLevel (u + 1))) ≤
          ENNReal.ofReal C) →
      (∀ i w, F.observables jX (F.points i) w =
        FreeEnergies.caseLift (F.points i).tower u _ (Φ i) ((F.points i).sampleAtLevel (u + 1) (hu i) w)) →
      (∀ i w, F.observables jE (F.points i) w =
        FreeEnergies.caseMeanAtSample (F.points i).tower u _ (Φ i) ((F.points i).sampleAtLevel (u + 1) (hu i) w)) →
      (∃ C : ℝ, ∀ i w, |F.observables jR (F.points i) w| ≤ C) →
      (∀ i, IsMeasurableAbove (F.points i) (u + 1) (F.observables jR (F.points i))) →
      F.condMean (fun v => v (jR, 0) * v (jX, 0)) =ᵐ[F.law] F.condMean (fun v => v (jR, 0) * v (jE, 0)))
    (hFC : ∀ S : MomentPoint Λ, X₀ ≤ S.scaleCoupling → ∀ (u d n : ℕ) [NeZero n], n = S.levelSide (u + 1) →
      u + 1 ≤ S.data.windowLevel → u = S.lastSeparated + d → d ≤ S.logIndex →
      ∀ (B : Finset (Fin Λ.k)) (Sz : ℝ), (∀ W Yt ωt bad b, |S.goodCaseForms u d n B W Yt ωt bad b| ≤ Sz) →
        IsQuasiLocalCaseFunction (S.tower.stage u).toStepSetup (S.originSite u (n * Λ.stepParams.side))
          (8 * S.rangeSq + 2) 0 Sz ∅ (fun _ => 0) (S.goodCaseForms u d n B) ∧
          ∀ᵐ x ∂(markedSampleLaw S.tower S.β (u + 1) n),
            FreeEnergies.CaseIntegrableAtSample S.tower u n (fun _ => S.goodCaseForms u d n B) x)
    (hC₀ : 0 ≤ C₀)
    (hfl : ∀ S : MomentPoint Λ, X₀ ≤ S.scaleCoupling → (S.range : ℝ) ^ 3 * (S.scaleCoupling ^ ((1 : ℝ) / 2))⁻¹ ≤ 1 ∧
      (S.scaleCoupling ^ ((1 : ℝ) / 2)) ^ 3 * Real.exp (-(cE * (S.range : ℝ) ^ 2)) ≤ 1)
    (hSeq : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S), X₀ ≤ S.scaleCoupling → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ t : ℕ, (∀ i, (F.points (φ i)).lastSeparated = t) →
      SequenceBounds F.rule (fun i => F.points (φ i)) F.period t S.logIndex S.scaleCoupling S.range CM CM1 CO C₀ cE Cs)
    (S : MomentPoint Λ) (hx : X₀ ≤ S.scaleCoupling) (F : LimitLawAtPoint S) (d : ℕ → ℕ)
    (μ : ∀ m, Measure (LevelChain Λ.stepParams.side ((F.points m).lastSeparated + d m)
      ((F.points m).data.period Λ.stepParams.side)))
    (hd : ∀ m, (F.points m).lastSeparated + d m = (F.points m).data.windowLevel)
    (hμ : ∀ m, IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling ((F.points m).lastSeparated + d m)
      ((F.points m).data.period Λ.stepParams.side)) (μ m)) (B : Finset (Fin Λ.k)) {e : ℝ}
    (he : Tendsto (fun m => ∫ X, ∏ i ∈ B, (F.points m).halfForm (d m) ((F.points m).data.period Λ.stepParams.side) i X
      ∂(μ m)) atTop (𝓝 e))
    (j : F.Index) (hj : F.observables j = responseProduct B) :
    ∀ᵐ v ∂F.law, |S.scaleCoupling ^ B.card * F.condMeanAt j v - e| ≤ S.windowBound CG Cq CO CM CM1 C₀ B := by
  classical
  obtain ⟨t, φ, hφ, ht⟩ := exists_subseq_const_lastSeparated S F
  have hcount := F.countable_index
  have hq₀ := hSeq S F hx φ hφ t ht
  have hXf : ∀ j, TranslatedLaws.HasBoundedMoments
      (sampleFamily F.rule (fun i => F.points (φ i)) F.period (F.observables j)) := fun j =>
    ⟨fun i => (F.hasBoundedMoments j).aemeasurable (φ i), fun q => by
      obtain ⟨C, hC⟩ := (F.hasBoundedMoments j).moment_bound q
      exact ⟨C, fun i => hC (φ i)⟩⟩
  have hlim₀ : IsJointLimitLaw (translatedTori (fun i => F.points (φ i)) F.period)
      (fun j => sampleFamily F.rule (fun i => F.points (φ i)) F.period (F.observables j)) F.law :=
    ⟨F.isJointLimitLaw.isProbability, fun l a G hG hb => (F.isJointLimitLaw.tendsto l a G hG hb).comp hφ.tendsto_atTop⟩
  obtain ⟨sub, P', hsub, hlim, -, htr⟩ := hExt (translatedTori (fun i => F.points (φ i)) F.period) F.Index (ℕ × ℕ × ℕ)
    (fun j => sampleFamily F.rule (fun i => F.points (φ i)) F.period (F.observables j))
    (fun c => sampleFamily F.rule (fun i => F.points (φ i)) F.period (windowObs t S.logIndex B c)) F.law hq₀.isPreserving
    hXf (hq₀.hasBoundedMoments_window B) hlim₀
  have hφs : StrictMono fun i => φ (sub i) := hφ.comp hsub
  have hq := hSeq S F hx _ hφs t fun i => ht (sub i)
  have hlim' : IsJointLimitLaw (translatedTori (fun i => F.points (φ (sub i))) F.period)
      (fun c => sampleFamily F.rule (fun i => F.points (φ (sub i))) F.period
        (Sum.elim F.observables (windowObs t S.logIndex B) c)) P' := by
    have e1 : (fun c => sampleFamily F.rule (fun i => F.points (φ (sub i))) F.period
          (Sum.elim F.observables (windowObs t S.logIndex B) c)) =
        fun c i => Sum.elim (fun j => sampleFamily F.rule (fun i => F.points (φ i)) F.period (F.observables j))
          (fun c => sampleFamily F.rule (fun i => F.points (φ i)) F.period (windowObs t S.logIndex B c)) c (sub i) := by
      funext c
      rcases c with c | c <;> rfl
    rw [e1]
    exact hlim
  let F' : LimitLawAtPoint S :=
    { rule := F.rule, rule_admissible := F.rule_admissible, period := F.period, one_le_period := F.one_le_period,
      exponents := fun i => F.exponents (φ (sub i)), strictMono_exponents := fun _ _ h => F.strictMono_exponents (hφs h),
      points := fun i => F.points (φ (sub i)), points_eq := fun i => F.points_eq _, Index := F.Index ⊕ (ℕ × ℕ × ℕ),
      countable_index := inferInstance,
      observables := Sum.elim F.observables (windowObs t S.logIndex B),
      hasBoundedMoments := by
        rintro (j | c)
        · exact ⟨fun i => (hXf j).aemeasurable (sub i), fun q => by
            obtain ⟨C, hC⟩ := (hXf j).moment_bound q
            exact ⟨C, fun i => hC (sub i)⟩⟩
        · exact hq.hasBoundedMoments_window B c
      law := P', isJointLimitLaw := hlim' }
  have hb : ∀ᵐ v ∂P', |S.scaleCoupling ^ B.card * invariantCondExp P' (evalAtZero (Sum.inl j)) v - e| ≤
      S.windowBound CG Cq CO CM CM1 C₀ B :=
    ae_bound_in_window_law hMn hGS hMS hFar hFC hC₀ hfl S hx F' (t := t) hq B Sum.inr (fun _ => rfl) (Sum.inl j) hj
      (fun m => d (φ (sub m))) (fun m => μ (φ (sub m))) (fun m => hd _) (fun m => hμ _) (he.comp hφs.tendsto_atTop)
      (fun m => (points_params_eq S F _).2.2.2)
  have hx1 : 1 ≤ S.scaleCoupling := by
    have := (hq.bounds 0).one_le_coupling
    rwa [hq.coupling_eq 0] at this
  have hxb : 0 < S.scaleCoupling ^ B.card := pow_pos (by linarith) _
  have hMean := hMn (translatedTori (fun i => F.points (φ i)) F.period) F.Index
    (fun j => sampleFamily F.rule (fun i => F.points (φ i)) F.period (F.observables j)) F.law
    hq₀.isPreserving hXf hlim₀
  have hY : Integrable (evalAtZero j) F.law := by
    have h1 := (hMean.2.1 1 (fun _ => (j, 0))).1
    have e1 : (fun v : TranslateValues F.Index => ∏ _c : Fin 1, v (j, 0)) = evalAtZero j := by
      funext v
      simp [evalAtZero]
    rwa [e1] at h1
  obtain ⟨Bd, hBd⟩ : ∃ Bd, Bd = S.windowBound CG Cq CO CM CM1 C₀ B := ⟨_, rfl⟩
  rw [← hBd] at hb ⊢
  have h2 := htr (evalAtZero j) ((e - Bd) / S.scaleCoupling ^ B.card) ((e + Bd) / S.scaleCoupling ^ B.card) hY (by
    filter_upwards [hb] with v hv
    have e1 : invariantCondExp P' (evalAtZero j ∘ leftValues) v = invariantCondExp P' (evalAtZero (Sum.inl j)) v := rfl
    rw [e1, div_le_iff₀ hxb, le_div_iff₀ hxb]
    obtain ⟨a1, a2⟩ := abs_le.1 hv
    constructor <;> nlinarith)
  filter_upwards [h2] with v hv
  obtain ⟨a1, a2⟩ := hv
  rw [div_le_iff₀ hxb] at a1
  rw [le_div_iff₀ hxb] at a2
  have e1 : F.condMeanAt j v = invariantCondExp F.law (evalAtZero j) v := rfl
  rw [e1]
  refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith
end Main
section Final
private theorem top_bound_numeric {x r Lq cM g : ℝ} {b : ℕ} (hx : 1 ≤ x) (hr : 1 ≤ r) (hL0 : 0 ≤ Lq) (hL : Lq ≤ x⁻¹)
    (hcM : 0 ≤ cM) (hg : 0 ≤ g) :
    cM * r ^ (4 * b) * Lq * 120 ^ 16 * (g * x ^ ((1 : ℝ) / 4000)) ≤
      cM * 120 ^ 16 * g * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have h1 : Lq * x ^ ((1 : ℝ) / 4000) ≤ x ^ (-(1 / 2) + 1 / 1000 : ℝ) := by
    calc Lq * x ^ ((1 : ℝ) / 4000) ≤ x ^ (-1 : ℝ) * x ^ ((1 : ℝ) / 4000) :=
          mul_le_mul_of_nonneg_right (by rw [Real.rpow_neg_one]; exact hL) (by positivity)
      _ = x ^ ((-1 : ℝ) + 1 / 4000) := by rw [← Real.rpow_add hx0]
      _ ≤ x ^ (-(1 / 2) + 1 / 1000 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have h2 : r ^ (4 * b) * (Lq * x ^ ((1 : ℝ) / 4000)) ≤ r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ) :=
    mul_le_mul (pow_le_pow_right₀ hr (by omega)) h1 (by positivity) (by positivity)
  calc cM * r ^ (4 * b) * Lq * 120 ^ 16 * (g * x ^ ((1 : ℝ) / 4000))
      = cM * 120 ^ 16 * g * (r ^ (4 * b) * (Lq * x ^ ((1 : ℝ) / 4000))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
private theorem add_le_of_bounds {A N C3 C5 c4 Z C5' ET GT HT : ℝ} (h1 : A ≤ ET) (h2 : N + (Z + C5') + c4 ≤ GT)
    (h3 : C3 ≤ HT) (h4 : C5 ≤ C5') (h5 : 0 ≤ Z) : A + N + (C3 + C5 + c4) ≤ ET + GT + HT := by linarith
private theorem window_bound_numeric {x s r Lq N K cq c6 cb c21 c5 c2b c1 cO cM cM1 A₂ : ℝ} {b : ℕ} (hb : b ≤ 8)
    (hs : 1 ≤ s) (hxs : x = s ^ 2)
    (hsi : x ^ (-(1 / 2) : ℝ) = s⁻¹) (hr : 1 ≤ r) (hK : 0 ≤ K) (hL0 : 0 ≤ Lq) (hL : Lq ≤ x⁻¹) (hN0 : 0 ≤ N)
    (hN : N ≤ 6000 * x ^ ((3 : ℝ) / 4000)) (hq : cq ≤ A₂) (hA₂ : 0 ≤ A₂) :
    r ^ 3 * s⁻¹ * (2 * K * r ^ 4) ^ b * (c6 * x ^ ((1 : ℝ) / 4000) + cq) + x ^ b * (cb * x ^ (-((b + 1 : ℕ) : ℝ))) +
        N * (|cO * r ^ (4 * b + 2) * x ^ (-(1 / 2) : ℝ)| * (|c21| * x ^ ((1 : ℝ) / 4000)) +
          |cM * r ^ (4 * b)| * (121 ^ 16 * x ^ 4) * (|c5| * x ^ (-((5 : ℕ) : ℝ)))) +
        (|cM * r ^ (4 * b) * Lq| * 120 ^ 16 * (c2b * x ^ ((1 : ℝ) / 4000)) +
          |cM * r ^ (4 * b)| * (c1 * x ^ (-((1 : ℕ) : ℝ))) +
          (|cM1| + 1) * r ^ (4 * b) * Lq) ≤
      (((2 * K) ^ b * (|c6| + A₂) + |cb|) + (6000 * |cO| * |c21| + 6000 * |cM| * 121 ^ 16 * |c5| +
          |cM| * (121 + 120 * 0) ^ 16 + |cM| * |c1| + (|cM1| + 1)) +
        |cM| * 120 ^ 16 * |c2b|) * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) := by
  have hx1 : 1 ≤ x := by rw [hxs]; exact one_le_pow₀ hs
  have hx0 : 0 < x := by linarith
  have hxe : 0 ≤ x ^ ((1 : ℝ) / 4000) := by positivity
  have hxp : ∀ y : ℝ, 0 ≤ x ^ y := fun y => by positivity
  have e₁ : x ^ (-(1 / 2) + 1 / 1000 : ℝ) = s⁻¹ * x ^ ((1 : ℝ) / 1000) := by
    rw [Real.rpow_add hx0, hsi]
  have hp : x ^ (-((b + 1 : ℕ) : ℝ)) = (x ^ (b + 1))⁻¹ := by
    rw [Real.rpow_neg hx0.le, Real.rpow_natCast]
  have t1 := lead_bound_numeric (x := x) (s := s) (Yv := x ^ ((1 : ℝ) / 1000)) (rr := r) (K := K) (A₂ := A₂)
    (c₁ := c6) (c₂ := cb) (z := x ^ ((1 : ℝ) / 4000)) (p := x ^ (-((b + 1 : ℕ) : ℝ))) (b := b)
    (Cf := (2 * K) ^ b * (|c6| + A₂) + |cb|) hs hxs
    (Real.one_le_rpow hx1 (by norm_num)) hr hA₂ hK (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) hxe le_rfl hp
  rw [← e₁] at t1
  have t1' : r ^ 3 * s⁻¹ * (2 * K * r ^ 4) ^ b * (c6 * x ^ ((1 : ℝ) / 4000) + cq) +
        x ^ b * (cb * x ^ (-((b + 1 : ℕ) : ℝ))) ≤
      r ^ 3 * s⁻¹ * (2 * K * r ^ 4) ^ b * (|c6| * x ^ ((1 : ℝ) / 4000) + A₂) +
        x ^ b * (|cb| * x ^ (-((b + 1 : ℕ) : ℝ))) := by
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by positivity)) (mul_le_mul_of_nonneg_left ?_ (by positivity))
    · exact add_le_add (mul_le_mul_of_nonneg_right (le_abs_self _) hxe) hq
    · exact mul_le_mul_of_nonneg_right (le_abs_self _) (hxp _)
  have t2 := chain_bound_numeric (x := x) (r := r) (N := N) (Lq := Lq) (cO := |cO|) (cM := |cM|) (cM1 := |cM1| + 1)
    (g1 := |c21|) (g5 := |c5|) (g := 0)
    (g' := |c1|) hb hx1 hr hN0 hN hL0 hL (abs_nonneg _) (abs_nonneg _) (by positivity) (abs_nonneg _) (abs_nonneg _)
    le_rfl (abs_nonneg _)
  have hm1 : |cM * r ^ (4 * b)| = |cM| * r ^ (4 * b) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ r ^ (4 * b))]
  have hm2 : |cM * r ^ (4 * b) * Lq| = |cM| * r ^ (4 * b) * Lq := by rw [abs_mul, hm1, abs_of_nonneg hL0]
  have hm3 : |cO * r ^ (4 * b + 2) * x ^ (-(1 / 2) : ℝ)| = |cO| * r ^ (4 * b + 2) * x ^ (-(1 / 2) : ℝ) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ r ^ (4 * b + 2)), abs_of_nonneg (hxp _)]
  have t3 := top_bound_numeric (g := |c2b|) (b := b) hx1 hr hL0 hL (abs_nonneg cM) (abs_nonneg _)
  have t4 : |cM| * r ^ (4 * b) * Lq * 120 ^ 16 * (c2b * x ^ ((1 : ℝ) / 4000)) ≤
      |cM| * r ^ (4 * b) * Lq * 120 ^ 16 * (|c2b| * x ^ ((1 : ℝ) / 4000)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hxe) (by positivity)
  have t5 : |cM| * r ^ (4 * b) * (c1 * x ^ (-((1 : ℕ) : ℝ))) ≤ |cM| * r ^ (4 * b) * (|c1| * x ^ (-((1 : ℕ) : ℝ))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) (hxp _)) (by positivity)
  have t6 : 0 ≤ |cM| * r ^ (4 * b) * Lq * (1 + 120 * (1 + 0 * x ^ ((1 : ℝ) / 4000))) ^ (2 * b) := by positivity
  rw [hm1, hm2, hm3]
  have t1a : r ^ 3 * s⁻¹ * (2 * K * r ^ 4) ^ b * (|c6| * x ^ ((1 : ℝ) / 4000) + A₂) +
        x ^ b * (|cb| * x ^ (-((b + 1 : ℕ) : ℝ))) ≤
      ((2 * K) ^ b * (|c6| + A₂) + |cb|) * (r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ)) := by
    calc _ ≤ _ := t1
      _ = _ := by ring
  have t7 := t4.trans t3
  generalize r ^ (4 * b + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ) = T at *
  generalize ((2 * K) ^ b * (|c6| + A₂) + |cb|) = E₁ at *
  generalize (6000 * |cO| * |c21| + 6000 * |cM| * 121 ^ 16 * |c5| + |cM| * (121 + 120 * 0) ^ 16 + |cM| * |c1| +
    (|cM1| + 1)) = E₂ at *
  generalize |cM| * 120 ^ 16 * |c2b| = E₃ at *
  have e : (E₁ + E₂ + E₃) * T = E₁ * T + E₂ * T + E₃ * T := by ring
  rw [e]
  exact add_le_of_bounds (t1'.trans t1a) t2 t7 t5 t6
end Final
section Close
private def closingConstant (K Cq CO CM CM1 : ℝ) (CG : ℕ → ℝ) (b : ℕ) : ℝ :=
  ((2 * K) ^ b * (|CG (6 * b)| + |Cq| ^ (2 * b + 1) * ((2 * b + 1).factorial : ℝ) ^ 6) + |CG (b + 1)|) +
    (6000 * |CO| * |CG (2 * b + 1)| + 6000 * |CM| * 121 ^ 16 * |CG 5| + |CM| * (121 + 120 * 0) ^ 16 + |CM| * |CG 1| +
      (|CM1| + 1)) +
    |CM| * 120 ^ 16 * |CG (2 * b)|
private theorem closingConstant_nonneg {K Cq CO CM CM1 : ℝ} {CG : ℕ → ℝ} (hK : 0 ≤ K) (b : ℕ) :
    0 ≤ closingConstant K Cq CO CM CM1 CG b := by
  unfold closingConstant
  positivity
variable {Λ : MomentParameters}
private theorem windowBound_le {CG : ℕ → ℝ} {Cq CO CM CM1 C₀ : ℝ} (S : MomentPoint Λ) {CO' CM' CM1' C₀' cE : ℝ}
    (h : PointBounds S CM' CM1' CO' C₀' cE) (hC₀ : 0 ≤ C₀) (B : Finset (Fin Λ.k)) :
    S.windowBound CG Cq CO CM CM1 C₀ B ≤
      closingConstant (3 * C₀ + 1) Cq CO CM CM1 CG B.card *
        ((S.range : ℝ) ^ (4 * B.card + 3) * S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ)) := by
  have hx1 := h.one_le_coupling
  have hx0 : 0 < S.scaleCoupling := by linarith
  have hs : 1 ≤ S.scaleCoupling ^ ((1 : ℝ) / 2) := Real.one_le_rpow hx1 (by norm_num)
  have hxs : S.scaleCoupling = (S.scaleCoupling ^ ((1 : ℝ) / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hsinv : S.scaleCoupling ^ (-(1 / 2) : ℝ) = (S.scaleCoupling ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg hx0.le]
  have hr : (1 : ℝ) ≤ S.range := by
    have h1 : (1 : ℝ) ≤ S.scaleCoupling ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx1 (by norm_num)
    have h2 : S.scaleCoupling ^ ((1 : ℝ) / 100) ≤ (S.range : ℝ) := Nat.le_ceil _
    linarith
  have hq : Cq ^ (2 * B.card + 1) * ((2 * B.card + 1).factorial : ℝ) ^ 6 ≤
      |Cq| ^ (2 * B.card + 1) * ((2 * B.card + 1).factorial : ℝ) ^ 6 := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact (le_abs_self _).trans (abs_pow Cq _).le
  exact window_bound_numeric (S.card_le_eight h B) hs hxs hsinv hr (by linarith)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) h.decay_le (Nat.cast_nonneg _)
    (natCeil_four_log_le hx1) hq (by positivity)
private theorem side_dvd_period (S : MomentPoint Λ) (hfit : Λ.stepParams.Admissible) :
    Λ.stepParams.side ∣ S.data.period Λ.stepParams.side ∧ 64 ≤ S.data.period Λ.stepParams.side := by apply _root_.YangMills.SharedProofs.p32373 <;> assumption
end Close
theorem limitResponseMomentStatement_holds (hGS : goodStatesLimitStatement) (hMS : meanScoreLimitMomentStatement)
    (hFC : caseFormsQuasiLocalStatement) (hFar : farCopiesConditionalStatement) (hExt : jointLimitExtendStatement)
    (hMn : jointLimitPropertiesStatement) (hPL : largerToriStatement) (hNear : supportTotalNearQuadraticStatement)
    (hMF : formMeansAtWeightStatement) (hWR : formMeansStatement) (hOS : formProductMeanStepStatement)
    (hWS : scaleWindowStatement) (hCG : goodConfigCutoffStatement) (hLive : liveStatesStatement)
    (hCut : cutoffMeasurableStatement) (hBC : ResponseInTheExpansion.chainMeasurabilityStatement)
    (hSB : ResponseInTheExpansion.StageStatesMeasurableStatement)
    (hLD : ResponseInTheExpansion.sampleBelowLawStatement) (hMC : ResponseInTheExpansion.conditionalMeanIsCaseMeanStatement)
    (hRC : FreeEnergies.conditionalMeanReadsCasesStatement) (hFS : ResponseInTheExpansion.StagesAreWellPosed)
    (hRT : ResponseInTheExpansion.TowerAlongFlowStatement) (hAR : ChainNoise.ruleDrawsChainStatement)
    (hMT : meanScoreMomentBoundStatement) :
    limitResponseMomentStatement := by
  unfold caseFormsQuasiLocalStatement ForAllPoints at hFC
  unfold supportTotalNearQuadraticStatement ForAllPoints at hNear
  unfold formMeansAtWeightStatement ForAllPoints at hMF
  unfold formMeansStatement ForAllPoints at hWR
  unfold formProductMeanStepStatement ForAllPoints at hOS
  unfold scaleWindowStatement ForAllPoints at hWS
  unfold goodConfigCutoffStatement ForAllPoints at hCG
  unfold liveStatesStatement ForAllPoints at hLive
  unfold meanScoreMomentBoundStatement ForAllHullPoints at hMT
  unfold ResponseInTheExpansion.conditionalMeanIsCaseMeanStatement at hMC
  unfold FreeEnergies.conditionalMeanReadsCasesStatement at hRC
  unfold ResponseInTheExpansion.TowerAlongFlowStatement at hRT
  unfold ResponseInTheExpansion.StagesAreWellPosed at hFS
  unfold goodStatesLimitStatement at hGS
  unfold meanScoreLimitMomentStatement at hMS
  unfold farCopiesConditionalStatement at hFar
  unfold largerToriStatement at hPL
  unfold limitResponseMomentStatement
  refine forAllHullParameters_mono (forAllHullParameters_and hGS (forAllHullParameters_and hMS
    (forAllHullParameters_and hFar (forAllHullParameters_and (forAllHullParameters_of_forAllParameters hFC)
    (forAllHullParameters_and hPL (forAllHullParameters_and (forAllHullParameters_of_forAllParameters hNear)
    (forAllHullParameters_and (forAllHullParameters_of_forAllParameters hMF)
    (forAllHullParameters_and (forAllHullParameters_of_forAllParameters hWR)
    (forAllHullParameters_and (forAllHullParameters_of_forAllParameters hOS)
    (forAllHullParameters_and (forAllHullParameters_of_forAllParameters hWS)
    (forAllHullParameters_and (forAllHullParameters_of_forAllParameters hCG)
    (forAllHullParameters_and (forAllHullParameters_of_forAllParameters hLive) (forAllHullParameters_and hMT
    (forAllHullParameters_and (forAllHullParameters_of_admissibleParameters hMC)
    (forAllHullParameters_and (forAllHullParameters_of_admissibleParameters hRC)
      (forAllHullParameters_and (forAllHullParameters_of_admissible (P := fun T y =>
        ∀ (K : ResponseParameters) (β : ℝ)
        (hL : ∀ c : ChainStage (T.stepParameters y), ClusterExpansionOfAStep.CoarseLabelFacts c.toStepSetup)
        (z₀ : StageWithResponse (T.stepParameters y)),
        IsInitialStage T y β z₀ → ∀ s : ℕ, StagesOnFlowUpTo T K y β hL z₀ s → ∀ t ≤ s,
          (flowStages T y β hL z₀ t).1.toStepSetup.IsWellPosed) hFS)
        (forAllHullParameters_of_parameters hRT))))))))))))))))) ?_
  rintro Λ hk ⟨⟨CG, XG, hyG, hG⟩, ⟨Cq, hQ⟩, hFr, ⟨_, _, XF, _, _, hF⟩, hP, ⟨C₁, cE, X₁, hcE, _, hN₁⟩,
    ⟨CM, _, XM, _, _, hM⟩, ⟨_, _, _, _, _, hW⟩, ⟨CO, _, XO, _, _, hO⟩, ⟨_, _, XN, _, _, hN⟩, ⟨_, _, XC, _, _, hC⟩,
    ⟨_, _, _, _, _, hLv⟩, ⟨C₃, _, _, _, _, h₃⟩, hMC', hRC', hFS', hfit, hlam, -⟩
  obtain ⟨X₆, hX₆1, hX₆⟩ := exists_large_coupling_floor hcE
  obtain ⟨C₀, hC₀d⟩ : ∃ C₀, C₀ = max (C₁ 0) 0 := ⟨_, rfl⟩
  have hC₀ : 0 ≤ C₀ := hC₀d ▸ le_max_right _ _
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, X₀ = max Λ.floor (max XG (max XF (max X₁ (max XM (max XO (max XN (max XC X₆))))))) :=
    ⟨_, rfl⟩
  have hle : ∀ {a : ℝ} {S : MomentPoint Λ}, X₀ ≤ S.scaleCoupling → a ≤ X₀ → a ≤ S.scaleCoupling :=
    fun h1 h2 => h2.trans h1
  have eG : XG ≤ X₀ := by rw [hX₀]; simp
  have eF : XF ≤ X₀ := by rw [hX₀]; simp
  have e₁ : X₁ ≤ X₀ := by rw [hX₀]; simp
  have eM : XM ≤ X₀ := by rw [hX₀]; simp
  have eO : XO ≤ X₀ := by rw [hX₀]; simp
  have eN : XN ≤ X₀ := by rw [hX₀]; simp
  have eC : XC ≤ X₀ := by rw [hX₀]; simp
  have e₆ : X₆ ≤ X₀ := by rw [hX₀]; simp
  have hL1 : 1 ≤ Λ.stepParams.side := le_trans (by norm_num) hfit.L_ge
  have hPF : ∀ S : MomentPoint Λ, X₀ ≤ S.scaleCoupling → PointBounds S (CM 0) (CM 1) (CO 0) C₀ cE := by
    intro S hx
    have hxM := hle hx eM
    obtain ⟨hLq, -, -, -, -, hK, -⟩ := hN S (hle hx eN)
    have hforms : ∀ u, u ≤ S.data.windowLevel → (S.tower.stage u).toStepSetup.IsWellPosed := by
      intro u hu
      have h := hFS' Λ.response S.β S.labelFacts S.initial S.isInitial S.data.windowLevel S.onFlow u hu
      rw [← S.stage_eq u hu] at h
      exact h
    exact
      { admissible := hfit, k_le := hk, one_le_coupling := hX₆1.trans (hle hx e₆), window := hK, decay_le := hLq,
        log_measurable := hBC.2.1
        stage_measurable := fun u n _ => hSB Λ.stepParams hfit S.tower u n
        isProbability := fun u n _ =>
          (hBC.2.2 Λ.stepParams hfit hlam S.tower S.isCutoff S.marksMeasurable S.β u n).1
        sampleBelow_map := fun s d n _ =>
          (hLD Λ.stepParams hfit hlam S.tower S.isCutoff S.marksMeasurable S.β S.coeff).1 s d n
        cutoff_measurable := hCut
        means := fun d n _ hd hn B Ω _ μ _ A A' hA hA' => by
          have h := (hM S hxM).1 d n hd hn B Ω μ A A' hA hA'
          exact ⟨h.1, h.2.1⟩
        chain := (hM S hxM).2
        zero := (hW S).2.2.2.1
        one_step := hO S (hle hx eO)
        cutoff := fun u h1 h2 n _ hn W Y hg => (hC S (hle hx eC) u h1 h2 n hn W Y hg).2.1
        near := fun i q hl hg => by
          obtain ⟨p1, p2⟩ := hN₁ S (hle hx e₁) i q hl hg
          have htK : S.lastSeparated ≤ S.data.windowLevel := S.lastSeparated_le
          have hN1 := one_le_meanScore S S.lastSeparated (S.levelSide S.lastSeparated)
            (resp_isAdmissible S htK).price.nonneg i q
          have hv := S.localCurvature_nonneg S.lastSeparated (S.levelSide S.lastSeparated) q.1
          have hx1 : 1 ≤ S.scaleCoupling := hX₆1.trans (hle hx e₆)
          have hx0 : 0 ≤ S.scaleCoupling := by linarith
          have hC : C₁ 0 ≤ C₀ := hC₀d ▸ le_max_left _ _
          have hNn : 0 ≤ S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i q := by linarith
          refine ⟨p1.trans (mul_le_mul_of_nonneg_right hC (by positivity)), p2.trans ?_⟩
          gcongr
        live := hLv S
        condMean_eq := fun u hu F hm hb => hMC' S.tower S.β u (S.levelSide (u + 1))
          (S.isTowerOnParameters_of_le (by omega)) S.isCutoff S.marksMeasurable (hforms u (by omega))
          (S.isBlockTorusSide_levelSide hu hL1).1 (S.isBlockTorusSide_levelSide hu hL1).2 F hm hb
        weight_nonneg := fun u hu => (hRC' S.tower S.β u (S.levelSide (u + 1)) (S.isTowerOnParameters_of_le (by omega))
          S.isCutoff S.marksMeasurable (hforms u (by omega))
          (S.isBlockTorusSide_levelSide hu hL1).1 (S.isBlockTorusSide_levelSide hu hL1).2).1 }
  have hSeq : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S), X₀ ≤ S.scaleCoupling → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ t : ℕ, (∀ i, (F.points (φ i)).lastSeparated = t) →
      SequenceBounds F.rule (fun i => F.points (φ i)) F.period t S.logIndex S.scaleCoupling S.range (CM 0) (CM 1) (CO 0)
        C₀ cE (C₃ 0) := by
    intro S F hx φ hφ t ht
    have hmom := (hP S).2.2.2 F.rule (fun i => F.exponents (φ i)) (fun i => F.points (φ i)) F.period F.rule_admissible
      F.one_le_period (fun _ _ h => F.strictMono_exponents (hφ h)) (fun i => F.points_eq _)
    have hxi : ∀ i, X₀ ≤ (F.points (φ i)).scaleCoupling := fun i => by
      rw [(points_params_eq S F _).1]
      exact hx
    refine
      { isPreserving := hmom.1, bounds := fun i => hPF _ (hxi i), lastSeparated_eq := ht,
        logIndex_eq := fun i => (points_params_eq S F _).2.2.1, coupling_eq := fun i => (points_params_eq S F _).1,
        range_eq := fun i => (points_params_eq S F _).2.1, sample := fun i => ?_,
        responses := fun B => (hmom.2 (fun _ => 0) B).2, meanScores := fun i q J => ?_ }
    · obtain ⟨a, b, e⟩ := F.points_eq (φ i)
      have hr : F.rule.IsAdmissible (F.points (φ i)).tower := by
        rw [e]
        exact F.rule_admissible
      obtain ⟨d1, d2⟩ := side_dvd_period (F.points (φ i)) hfit
      exact hAR Λ.stepParams hfit (F.points (φ i)).tower F.rule (F.points (φ i)).β (F.points (φ i)).isCutoff
        (F.points (φ i)).marksMeasurable hr (F.points (φ i)).data.windowLevel _ d1 d2
    · exact (F.points (φ i)).lintegral_meanScoreProduct_pow_le (hPF _ (hxi i))
        (fun p hp J hJ => (h₃ _ p hp J hJ).2) J q
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, Cf = ∑ b ∈ Finset.range (Λ.k + 1),
      closingConstant (3 * C₀ + 1) Cq (CO 0) (CM 0) (CM 1) CG b := ⟨_, rfl⟩
  refine ⟨Cf, X₀, hX₀ ▸ le_max_left _ _, ?_⟩
  intro S F d μ hd hμ B e he j hj hx
  have hb := ae_bound_in_limit_law hExt hMn (CG := CG) (Cq := Cq) (X₀ := X₀) (CM := CM 0) (CM1 := CM 1) (CO := CO 0)
    (C₀ := C₀) (cE := cE) (Cs := C₃ 0)
    (fun S F hx => hG S F (eG.trans hx)) hQ hFr
    (fun S hx u d n _ hn hu hut hd B Sz hSz => hF S (eF.trans hx) u d n hn hu hut hd B Sz hSz) hC₀
    (fun S hx => hX₆ S.scaleCoupling (e₆.trans hx)) hSeq S hx F d μ hd hμ B he j hj
  have h1 := windowBound_le (CG := CG) (Cq := Cq) (CO := CO 0) (CM := CM 0) (CM1 := CM 1) S (hPF S hx) hC₀ B
  have hcard : B.card ∈ Finset.range (Λ.k + 1) := by
    have := Finset.card_le_univ B
    simp only [Fintype.card_fin] at this
    exact Finset.mem_range.2 (by omega)
  have hK : (0 : ℝ) ≤ 3 * C₀ + 1 := by linarith
  have h2 : closingConstant (3 * C₀ + 1) Cq (CO 0) (CM 0) (CM 1) CG B.card ≤ Cf := by
    rw [hCf]
    exact Finset.single_le_sum (f := fun b => closingConstant (3 * C₀ + 1) Cq (CO 0) (CM 0) (CM 1) CG b)
      (fun b _ => closingConstant_nonneg hK b) hcard
  have hx1 : 1 ≤ S.scaleCoupling := hX₆1.trans (e₆.trans hx)
  have hT : 0 ≤ (S.range : ℝ) ^ (4 * B.card + 3) * S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ) := by
    have : 0 ≤ S.scaleCoupling := by linarith
    positivity
  filter_upwards [hb] with v hv
  refine hv.trans (h1.trans ?_)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right h2 hT
end YangMills.Construction.MomentLaw
end
