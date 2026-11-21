import YangMills.Construction.LawByMomentsOfTheFlow.ChainCumulantIsTheFreeOneProof
import YangMills.Construction.LawByMomentsOfTheFlow.ContractionAtTheWeightsOfThePoint
import YangMills.Construction.LawByMomentsOfTheFlow.MeansOfFormsAtAWeight
import YangMills.Construction.LawByMomentsOfTheFlow.QuadraticFormsOnCurvature
import YangMills.Construction.LawByMomentsOfTheFlow.WhatTheMeansOfFormsRead
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses
namespace FormMeansAtWeight
section Holder
variable {Ω : Type} [MeasurableSpace Ω]
private theorem lintegral_prod_abs_le {ι : Type} (B : Finset ι) (P : Measure Ω)
    (f : ι → Ω → ℝ) (hf : ∀ i ∈ B, Measurable (f i)) [IsProbabilityMeasure P] :
    ∫⁻ w, ∏ i ∈ B, ENNReal.ofReal |f i w| ∂P ≤ ∏ i ∈ B, eLpNorm (f i) (B.card : ENNReal) P := by
  classical
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp
  have hb : 0 < B.card := Finset.card_pos.mpr hB
  have hb' : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast hb
  have hm : ∀ i ∈ B, AEMeasurable (fun w => ENNReal.ofReal |f i w| ^ (B.card : ℝ)) P := fun i hi =>
    (((hf i hi).abs.ennreal_ofReal).pow_const _).aemeasurable
  have key := ENNReal.lintegral_prod_norm_pow_le (μ := P) B hm
    (p := fun _ => (B.card : ℝ)⁻¹) (by simp [hb.ne']) (fun _ _ => by positivity)
  have e1 : ∀ i w, (ENNReal.ofReal |f i w| ^ (B.card : ℝ)) ^ (B.card : ℝ)⁻¹ = ENNReal.ofReal |f i w| := by
    intro i w
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hb'.ne', ENNReal.rpow_one]
  have e2 : ∀ i, eLpNorm (f i) (B.card : ENNReal) P =
      (∫⁻ w, ENNReal.ofReal |f i w| ^ (B.card : ℝ) ∂P) ^ (B.card : ℝ)⁻¹ := by
    intro i
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast hb.ne') (ENNReal.natCast_ne_top _)]
    simp [Real.enorm_eq_ofReal_abs]
  simp only [e1] at key
  simpa only [e2] using key
private theorem abs_prod_sub_prod_le {ι : Type} [DecidableEq ι] (B : Finset ι) (a b : ι → ℝ) :
    |∏ i ∈ B, a i - ∏ i ∈ B, b i| ≤ ∑ j ∈ B, |a j - b j| * ∏ i ∈ B.erase j, (|a i| + |b i|) := by
  induction B using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk, Finset.sum_insert hk, Finset.erase_insert hk]
    have hA : |∏ i ∈ S, a i| ≤ ∏ i ∈ S, (|a i| + |b i|) := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => by
        have := abs_nonneg (b i); linarith
    have hsplit : a k * ∏ i ∈ S, a i - b k * ∏ i ∈ S, b i =
        (a k - b k) * ∏ i ∈ S, a i + b k * (∏ i ∈ S, a i - ∏ i ∈ S, b i) := by ring
    have hrest : ∑ j ∈ S, |a j - b j| * ∏ i ∈ (insert k S).erase j, (|a i| + |b i|) =
        (|a k| + |b k|) * ∑ j ∈ S, |a j - b j| * ∏ i ∈ S.erase j, (|a i| + |b i|) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : j ≠ k := fun h => hk (h ▸ hj)
      rw [Finset.erase_insert_of_ne hjk.symm, Finset.prod_insert (by simp [hk])]
      ring
    rw [hrest, hsplit]
    have hnn : 0 ≤ ∑ j ∈ S, |a j - b j| * ∏ i ∈ S.erase j, (|a i| + |b i|) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _)
        (Finset.prod_nonneg fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
    calc |(a k - b k) * ∏ i ∈ S, a i + b k * (∏ i ∈ S, a i - ∏ i ∈ S, b i)|
        ≤ |a k - b k| * |∏ i ∈ S, a i| + |b k| * |∏ i ∈ S, a i - ∏ i ∈ S, b i| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ |a k - b k| * ∏ i ∈ S, (|a i| + |b i|) +
          (|a k| + |b k|) * ∑ j ∈ S, |a j - b j| * ∏ i ∈ S.erase j, (|a i| + |b i|) := by
          gcongr ?_ + ?_
          · exact mul_le_mul_of_nonneg_left hA (abs_nonneg _)
          · refine (mul_le_mul_of_nonneg_left ih (abs_nonneg _)).trans ?_
            exact mul_le_mul_of_nonneg_right (by have := abs_nonneg (a k); linarith) hnn
private theorem lintegral_abs_prod_le {ι : Type} (B : Finset ι) (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ι → Ω → ℝ) (ha : ∀ i ∈ B, Measurable (a i)) (U : ENNReal)
    (hU : ∀ i ∈ B, eLpNorm (a i) (B.card : ENNReal) P ≤ U) :
    ∫⁻ w, ENNReal.ofReal |∏ i ∈ B, a i w| ∂P ≤ U ^ B.card := by
  have e : ∀ w, ENNReal.ofReal |∏ i ∈ B, a i w| = ∏ i ∈ B, ENNReal.ofReal |a i w| := by
    intro w
    rw [Finset.abs_prod, ENNReal.ofReal_prod_of_nonneg fun _ _ => abs_nonneg _]
  simp only [e]
  refine (lintegral_prod_abs_le B P a ha).trans ?_
  calc ∏ i ∈ B, eLpNorm (a i) (B.card : ENNReal) P ≤ ∏ _i ∈ B, U := Finset.prod_le_prod' hU
    _ = U ^ B.card := by simp
private theorem lintegral_abs_prod_sub_le {ι : Type} (B : Finset ι) (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : ι → Ω → ℝ) (ha : ∀ i ∈ B, Measurable (a i)) (hb : ∀ i ∈ B, Measurable (b i)) (U V : ENNReal)
    (hU : ∀ i ∈ B, eLpNorm (a i) (B.card : ENNReal) P ≤ U) (hU' : ∀ i ∈ B, eLpNorm (b i) (B.card : ENNReal) P ≤ U)
    (hV : ∀ i ∈ B, eLpNorm (fun w => a i w - b i w) (B.card : ENNReal) P ≤ V) :
    ∫⁻ w, ENNReal.ofReal |∏ i ∈ B, a i w - ∏ i ∈ B, b i w| ∂P ≤
      (B.card : ENNReal) * (V * (2 * U) ^ (B.card - 1)) := by
  classical
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp
  have hc : 1 ≤ B.card := Finset.card_pos.mpr hB
  have hc' : (1 : ENNReal) ≤ (B.card : ENNReal) := by exact_mod_cast hc
  let g : ι → ι → Ω → ℝ := fun j i w => if i = j then a i w - b i w else |a i w| + |b i w|
  have hg : ∀ j, ∀ i ∈ B, Measurable (g j i) := by
    intro j i hi
    by_cases h : i = j
    · have e : g j i = fun w => a i w - b i w := by funext w; simp [g, h]
      rw [e]; exact (ha i hi).sub (hb i hi)
    · have e : g j i = fun w => |a i w| + |b i w| := by funext w; simp [g, h]
      rw [e]; exact (ha i hi).abs.add (hb i hi).abs
  have hterm : ∀ j ∈ B, ∫⁻ w, ENNReal.ofReal (|a j w - b j w| * ∏ i ∈ B.erase j, (|a i w| + |b i w|)) ∂P ≤
      V * (2 * U) ^ (B.card - 1) := by
    intro j hj
    have e : ∀ w, ENNReal.ofReal (|a j w - b j w| * ∏ i ∈ B.erase j, (|a i w| + |b i w|)) =
        ∏ i ∈ B, ENNReal.ofReal |g j i w| := by
      intro w
      rw [← Finset.mul_prod_erase B _ hj]
      have : ∀ i ∈ B.erase j, ENNReal.ofReal |g j i w| = ENNReal.ofReal (|a i w| + |b i w|) := by
        intro i hi
        have hne : i ≠ j := Finset.ne_of_mem_erase hi
        simp only [g, if_neg hne]
        rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
      rw [Finset.prod_congr rfl this, ENNReal.ofReal_mul (abs_nonneg _),
        ENNReal.ofReal_prod_of_nonneg fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)]
      simp [g]
    simp only [e]
    refine (lintegral_prod_abs_le B P (g j) (hg j)).trans ?_
    rw [← Finset.mul_prod_erase B _ hj]
    have h1 : eLpNorm (g j j) (B.card : ENNReal) P ≤ V := by simpa [g] using hV j hj
    have h2 : ∀ i ∈ B.erase j, eLpNorm (g j i) (B.card : ENNReal) P ≤ 2 * U := by
      intro i hi
      have hne : i ≠ j := Finset.ne_of_mem_erase hi
      have hiB := Finset.mem_of_mem_erase hi
      have e3 : g j i = (fun w => |a i w|) + fun w => |b i w| := by
        funext w; simp [g, hne]
      rw [e3]
      refine (eLpNorm_add_le (ha i hiB).abs.aestronglyMeasurable (hb i hiB).abs.aestronglyMeasurable hc').trans ?_
      have e4 : eLpNorm (fun w => |a i w|) (B.card : ENNReal) P = eLpNorm (a i) (B.card : ENNReal) P :=
        eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun w => by simp)
      have e5 : eLpNorm (fun w => |b i w|) (B.card : ENNReal) P = eLpNorm (b i) (B.card : ENNReal) P :=
        eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun w => by simp)
      rw [e4, e5, two_mul]
      exact add_le_add (hU i hiB) (hU' i hiB)
    calc eLpNorm (g j j) (B.card : ENNReal) P * ∏ i ∈ B.erase j, eLpNorm (g j i) (B.card : ENNReal) P
        ≤ V * ∏ _i ∈ B.erase j, (2 * U) := mul_le_mul' h1 (Finset.prod_le_prod' h2)
      _ = V * (2 * U) ^ (B.card - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem hj]
  calc ∫⁻ w, ENNReal.ofReal |∏ i ∈ B, a i w - ∏ i ∈ B, b i w| ∂P
      ≤ ∫⁻ w, ∑ j ∈ B, ENNReal.ofReal (|a j w - b j w| * ∏ i ∈ B.erase j, (|a i w| + |b i w|)) ∂P := by
        refine lintegral_mono fun w => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (abs_nonneg _)
          (Finset.prod_nonneg fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _))]
        exact ENNReal.ofReal_le_ofReal (abs_prod_sub_prod_le B _ _)
    _ = ∑ j ∈ B, ∫⁻ w, ENNReal.ofReal (|a j w - b j w| * ∏ i ∈ B.erase j, (|a i w| + |b i w|)) ∂P := by
        refine lintegral_finsetSum _ fun j hj => ?_
        refine ENNReal.measurable_ofReal.comp ?_
        exact ((ha j hj).sub (hb j hj)).abs.mul (Finset.measurable_prod _ fun i hi =>
          (ha i (Finset.mem_of_mem_erase hi)).abs.add (hb i (Finset.mem_of_mem_erase hi)).abs)
    _ ≤ ∑ _j ∈ B, V * (2 * U) ^ (B.card - 1) := Finset.sum_le_sum hterm
    _ = (B.card : ENNReal) * (V * (2 * U) ^ (B.card - 1)) := by simp
end Holder
section Forms
variable {n : ℕ} [NeZero n]
private theorem proj_measurable (e : Fin 3) (b : TorusBond n) : Measurable (fun X : ColourForm n => X e b) :=
  (measurable_pi_apply b).comp (measurable_pi_apply e)
private theorem curl_measurable (e : Fin 3) (p : TorusPlaquette n) :
    Measurable (fun X : ColourForm n => curl (X e) p) := by
  simp only [curl]
  exact (((proj_measurable e _).add (proj_measurable e _)).sub (proj_measurable e _)).sub (proj_measurable e _)
private theorem curlNorm_measurable (p : TorusPlaquette n) : Measurable (fun X : ColourForm n => curlNorm X p) := by
  simp only [curlNorm]
  exact (Finset.measurable_sum _ fun e _ => (curl_measurable e p).pow_const 2).sqrt
private theorem curlNorm_eq_norm (X : ColourForm n) (p : TorusPlaquette n) :
    curlNorm X p = ‖(WithLp.toLp 2 fun e => curl (X e) p : EuclideanSpace ℝ (Fin 3))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [curlNorm]
private theorem curlNorm_nonneg (X : ColourForm n) (p : TorusPlaquette n) : 0 ≤ curlNorm X p := Real.sqrt_nonneg _
private theorem curlNorm_add_le (X Y : ColourForm n) (p : TorusPlaquette n) :
    curlNorm (fun e b => X e b + Y e b) p ≤ curlNorm X p + curlNorm Y p := by
  rw [curlNorm_eq_norm, curlNorm_eq_norm, curlNorm_eq_norm]
  refine le_trans (le_of_eq ?_) (norm_add_le _ _)
  congr 1
  ext e
  simp [curl]
  ring
private theorem curlNorm_const_mul (c : ℝ) (X : ColourForm n) (p : TorusPlaquette n) :
    curlNorm (fun e b => c * X e b) p = |c| * curlNorm X p := by
  rw [curlNorm_eq_norm, curlNorm_eq_norm, ← Real.norm_eq_abs, ← norm_smul]
  congr 1
  ext e
  simp [curl]
  ring
private theorem colourEval_measurable (q : BondBilinear n) {Ω : Type} [MeasurableSpace Ω] {X X' : Ω → ColourForm n}
    (hX : Measurable X) (hX' : Measurable X') : Measurable (fun w => colourEval q (X w) (X' w)) := by
  simp only [colourEval, bilinearEval]
  exact Finset.measurable_sum _ fun e _ => Finset.measurable_sum _ fun b _ => Finset.measurable_sum _ fun b' _ =>
    (((proj_measurable e b).comp hX).mul_const _).mul ((proj_measurable e b').comp hX')
private theorem colourEval_sub (q : BondBilinear n) (Z Z' : ColourForm n) :
    colourEval q Z Z - colourEval q Z' Z' =
      colourEval q (fun e b => Z e b - Z' e b) Z + colourEval q Z' (fun e b => Z e b - Z' e b) := by
  simp only [colourEval, bilinearEval]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  ring
variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
private theorem curvNorm_add_le (μ : Measure Ω) (ω : TorusPlaquette n → ℝ) {q : ENNReal} (hq : 1 ≤ q)
    {X Y : Ω → ColourForm n} (hX : Measurable X) (hY : Measurable Y) :
    weightedCurvatureNorm μ ω q (fun w e b => X w e b + Y w e b) ≤
      weightedCurvatureNorm μ ω q X + weightedCurvatureNorm μ ω q Y := by
  unfold weightedCurvatureNorm
  refine iSup_le fun p => ?_
  have h1 : eLpNorm (fun w => curlNorm (fun e b => X w e b + Y w e b) p.1) q μ ≤
      eLpNorm (fun w => curlNorm (X w) p.1) q μ + eLpNorm (fun w => curlNorm (Y w) p.1) q μ := by
    refine le_trans (eLpNorm_mono_real (g := (fun w => curlNorm (X w) p.1) + fun w => curlNorm (Y w) p.1) fun w => ?_)
      (eLpNorm_add_le ((curlNorm_measurable p.1).comp hX).aestronglyMeasurable
        ((curlNorm_measurable p.1).comp hY).aestronglyMeasurable hq)
    rw [Real.norm_of_nonneg (curlNorm_nonneg _ _)]
    exact curlNorm_add_le _ _ _
  calc ENNReal.ofReal (ω p.1) * eLpNorm (fun w => curlNorm (fun e b => X w e b + Y w e b) p.1) q μ
      ≤ ENNReal.ofReal (ω p.1) * (eLpNorm (fun w => curlNorm (X w) p.1) q μ + eLpNorm (fun w => curlNorm (Y w) p.1) q μ) := by
        gcongr
    _ = ENNReal.ofReal (ω p.1) * eLpNorm (fun w => curlNorm (X w) p.1) q μ +
        ENNReal.ofReal (ω p.1) * eLpNorm (fun w => curlNorm (Y w) p.1) q μ := mul_add _ _ _
    _ ≤ _ := add_le_add
      (le_iSup (fun p : OrientedPlaquette n => ENNReal.ofReal (ω p.1) * eLpNorm (fun w => curlNorm (X w) p.1) q μ) p)
      (le_iSup (fun p : OrientedPlaquette n => ENNReal.ofReal (ω p.1) * eLpNorm (fun w => curlNorm (Y w) p.1) q μ) p)
private theorem curvNorm_const_mul_le (μ : Measure Ω) (ω : TorusPlaquette n → ℝ) (q : ENNReal) (c : ℝ)
    (X : Ω → ColourForm n) :
    weightedCurvatureNorm μ ω q (fun w e b => c * X w e b) ≤ ENNReal.ofReal |c| * weightedCurvatureNorm μ ω q X := by
  unfold weightedCurvatureNorm
  refine iSup_le fun p => ?_
  have e : (fun w => curlNorm (fun e b => c * X w e b) p.1) = |c| • fun w => curlNorm (X w) p.1 := by
    funext w
    simp [curlNorm_const_mul]
  rw [e, eLpNorm_const_smul, show ‖|c|‖ₑ = ENNReal.ofReal |c| by rw [Real.enorm_eq_ofReal_abs, abs_abs]]
  calc ENNReal.ofReal (ω p.1) * (ENNReal.ofReal |c| * eLpNorm (fun w => curlNorm (X w) p.1) q μ)
      = ENNReal.ofReal |c| * (ENNReal.ofReal (ω p.1) * eLpNorm (fun w => curlNorm (X w) p.1) q μ) := by ring
    _ ≤ _ := by
      gcongr
      exact le_iSup (fun p : OrientedPlaquette n => ENNReal.ofReal (ω p.1) * eLpNorm (fun w => curlNorm (X w) p.1) q μ) p
private theorem curvNorm_exponent_mono (μ : Measure Ω) [IsProbabilityMeasure μ] (ω : TorusPlaquette n → ℝ)
    {q q' : ENNReal} (h : q ≤ q') {X : Ω → ColourForm n} (hX : Measurable X) :
    weightedCurvatureNorm μ ω q X ≤ weightedCurvatureNorm μ ω q' X := by
  unfold weightedCurvatureNorm
  refine iSup_mono fun p => ?_
  gcongr
  exact eLpNorm_le_eLpNorm_of_exponent_le h ((curlNorm_measurable p.1).comp hX).aestronglyMeasurable
abbrev _root_.YangMills.SharedProofs.p123435 := @curvNorm_exponent_mono
private theorem curvNorm_weight_mono (μ : Measure Ω) {ω ω' : TorusPlaquette n → ℝ} (h : ∀ p, ω p ≤ ω' p)
    (q : ENNReal) (X : Ω → ColourForm n) :
    weightedCurvatureNorm μ ω q X ≤ weightedCurvatureNorm μ ω' q X := by
  unfold weightedCurvatureNorm
  refine iSup_mono fun p => ?_
  gcongr
  exact h _
private theorem curvNorm_comp (μ : Measure Ω) (μ' : Measure Ω') {f : Ω' → Ω} (hf : MeasurePreserving f μ' μ)
    (ω : TorusPlaquette n → ℝ) (q : ENNReal) {X : Ω → ColourForm n} (hX : Measurable X) :
    weightedCurvatureNorm μ' ω q (fun w => X (f w)) = weightedCurvatureNorm μ ω q X := by
  unfold weightedCurvatureNorm
  refine iSup_congr fun p => ?_
  congr 1
  exact eLpNorm_comp_measurePreserving ((curlNorm_measurable p.1).comp hX).aestronglyMeasurable hf
private theorem curvNorm_const_lt_top (μ : Measure Ω) [IsProbabilityMeasure μ] (ω : TorusPlaquette n → ℝ)
    {q : ENNReal} (X : ColourForm n) :
    weightedCurvatureNorm μ ω q (fun _ => X) < ⊤ := by
  unfold weightedCurvatureNorm
  have hs : (⨆ p : OrientedPlaquette n, ENNReal.ofReal (ω p.1) * eLpNorm (fun _ : Ω => curlNorm X p.1) q μ) ≤
      ∑ p : OrientedPlaquette n, ENNReal.ofReal (ω p.1) * eLpNorm (fun _ : Ω => curlNorm X p.1) q μ :=
    iSup_le fun p => Finset.single_le_sum
      (f := fun p : OrientedPlaquette n => ENNReal.ofReal (ω p.1) * eLpNorm (fun _ : Ω => curlNorm X p.1) q μ)
      (fun _ _ => zero_le) (Finset.mem_univ p)
  refine lt_of_le_of_lt hs (ENNReal.sum_lt_top.mpr fun p _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact (memLp_const (curlNorm X p.1)).eLpNorm_lt_top
end Forms
section Descent
variable {L : ℕ} [NeZero L] (a ρA : ℝ)
private theorem pushColours_add (u : ℕ) {n : ℕ} [NeZero n] (X Y : ColourForm n) :
    pushColours a ρA L u (fun e b => X e b + Y e b) =
      fun e b => pushColours a ρA L u X e b + pushColours a ρA L u Y e b := by
  funext e b
  simp [pushColours, responseMap, mul_add, Finset.sum_add_distrib]
private theorem pushColours_const_mul (u : ℕ) {n : ℕ} [NeZero n] (c : ℝ) (X : ColourForm n) :
    pushColours a ρA L u (fun e b => c * X e b) = fun e b => c * pushColours a ρA L u X e b := by
  funext e b
  simp only [pushColours, responseMap, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring
private theorem pushColours_measurable (u : ℕ) {n : ℕ} [NeZero n] :
    Measurable (pushColours a ρA L u : ColourForm n → ColourForm (n * L)) := by
  refine measurable_pi_lambda _ fun e => measurable_pi_lambda _ fun b => ?_
  simp only [pushColours, responseMap]
  exact Finset.measurable_sum _ fun c _ => (proj_measurable e c).const_mul _
private theorem descend_add (t : ℕ) : ∀ (d n : ℕ) [NeZero n] (X Y : ColourForm n),
    descend (L := L) a ρA t d n (fun e b => X e b + Y e b) =
      fun e b => descend (L := L) a ρA t d n X e b + descend (L := L) a ρA t d n Y e b
  | 0, _, _, _, _ => rfl
  | d + 1, n, _, X, Y => by
    simp only [descend]
    rw [pushColours_add]
    exact descend_add t d (n * L) _ _
private theorem descend_const_mul (t : ℕ) : ∀ (d n : ℕ) [NeZero n] (c : ℝ) (X : ColourForm n),
    descend (L := L) a ρA t d n (fun e b => c * X e b) =
      fun e b => c * descend (L := L) a ρA t d n X e b
  | 0, _, _, _, _ => rfl
  | d + 1, n, _, c, X => by
    simp only [descend]
    rw [pushColours_const_mul]
    exact descend_const_mul t d (n * L) _ _
private theorem descend_sub (t d n : ℕ) [NeZero n] (X Y : ColourForm n) :
    descend (L := L) a ρA t d n (fun e b => X e b - Y e b) =
      fun e b => descend (L := L) a ρA t d n X e b - descend (L := L) a ρA t d n Y e b := by
  have h := descend_add (L := L) a ρA t d n X (fun e b => (-1 : ℝ) * Y e b)
  rw [descend_const_mul] at h
  simpa [sub_eq_add_neg] using h
private theorem descend_measurable (t : ℕ) : ∀ (d n : ℕ) [NeZero n],
    Measurable (descend (L := L) a ρA t d n)
  | 0, _, _ => measurable_id
  | d + 1, n, _ => (descend_measurable t d (n * L)).comp (pushColours_measurable a ρA (t + d))
private theorem extendFluctuation_measurable {u n : ℕ} [NeZero n] :
    Measurable (extendFluctuation : StepFluctuation L u n → ColourForm (n * L)) := by
  refine measurable_pi_lambda _ fun e => measurable_pi_lambda _ fun c => ?_
  simp only [extendFluctuation, extendChart]
  refine Finset.measurable_sum _ fun b _ => ?_
  split_ifs
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (e, b)).continuous.measurable
  · exact measurable_const
private theorem descendWithNoise_eq (t : ℕ) : ∀ (d n : ℕ) [NeZero n] (c : ℝ) (A : ColourForm n)
    (w : FluctuationSample L t d n),
    descendWithNoise a ρA t c d n A w =
      fun e b => descend (L := L) a ρA t d n A e b + c * descendWithNoise a ρA t 1 d n 0 w e b
  | 0, _, _, c, A, w => by
    funext e b
    show A e b = A e b + c * (0 : ℝ)
    simp
  | d + 1, n, _, c, A, w => by
    have h1 := descendWithNoise_eq t d (n * L) c
      (fun e b => pushColours a ρA L (t + d) A e b + c * extendFluctuation w.1 e b) w.2
    have h2 := descendWithNoise_eq t d (n * L) 1
      (fun e b => pushColours a ρA L (t + d) 0 e b + 1 * extendFluctuation w.1 e b) w.2
    have e0 : (fun e b => pushColours a ρA L (t + d) (0 : ColourForm n) e b + 1 * extendFluctuation w.1 e b) =
        extendFluctuation w.1 := by
      funext e b
      simp [pushColours, responseMap]
    rw [e0] at h2
    show descendWithNoise a ρA t c d (n * L)
        (fun e b => pushColours a ρA L (t + d) A e b + c * extendFluctuation w.1 e b) w.2 =
      fun e b => descend (L := L) a ρA t d (n * L) (pushColours a ρA L (t + d) A) e b +
        c * descendWithNoise a ρA t 1 d (n * L)
          (fun e b => pushColours a ρA L (t + d) 0 e b + 1 * extendFluctuation w.1 e b) w.2 e b
    rw [h1, e0, h2, descend_add, descend_const_mul]
    funext e b
    ring
private theorem sample_fst (t d n : ℕ) : Measurable (fun w : FluctuationSample L t (d + 1) n => w.1) :=
  @measurable_fst _ _ _ (instMeasurableSpaceFluctuationSample L t d (n * L))
private theorem sample_snd (t d n : ℕ) : Measurable (fun w : FluctuationSample L t (d + 1) n => w.2) :=
  @measurable_snd _ _ _ (instMeasurableSpaceFluctuationSample L t d (n * L))
private theorem descendWithNoise_measurable (t : ℕ) (c : ℝ) : ∀ (d n : ℕ) [NeZero n],
    Measurable (fun z : ColourForm n × FluctuationSample L t d n => descendWithNoise a ρA t c d n z.1 z.2)
  | 0, _, _ => measurable_fst
  | d + 1, n, _ => by
    have h := descendWithNoise_measurable t c d (n * L)
    refine h.comp (Measurable.prodMk ?_ ((sample_snd t d n).comp measurable_snd))
    refine measurable_pi_lambda _ fun e => measurable_pi_lambda _ fun b => ?_
    exact (((proj_measurable e b).comp (pushColours_measurable a ρA (t + d))).comp measurable_fst).add
      ((((proj_measurable e b).comp extendFluctuation_measurable).comp ((sample_fst t d n).comp measurable_snd)).const_mul c)
private theorem fluctuationGaussian_isProb (u n : ℕ) : IsProbabilityMeasure (fluctuationGaussian a L 1 u n) := by
  unfold fluctuationGaussian
  infer_instance
private theorem sampleLaw_isProb (t : ℕ) : ∀ d n : ℕ, IsProbabilityMeasure (fluctuationSampleLaw a L t d n)
  | 0, _ => by
    show IsProbabilityMeasure (Measure.dirac ())
    infer_instance
  | d + 1, n => by
    have := sampleLaw_isProb t d (n * L)
    have := fluctuationGaussian_isProb (L := L) a (t + d) n
    let := instMeasurableSpaceFluctuationSample L t d (n * L)
    show IsProbabilityMeasure ((fluctuationGaussian a L 1 (t + d) n).prod (fluctuationSampleLaw a L t d (n * L)))
    infer_instance
end Descent
section Core
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem root_mul_root (hx : 0 < S.scaleCoupling) :
    ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) * ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) =
      ENNReal.ofReal S.scaleCoupling := by
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hx]
  norm_num
private theorem root_mul_inverse (hx : 0 < S.scaleCoupling) :
    ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) * ENNReal.ofReal |S.scaleCoupling ^ (-(1 / 2) : ℝ)| = 1 := by
  rw [abs_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hx]
  norm_num
private theorem half_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (hx : 0 < S.scaleCoupling) (f : Ω → ℝ)
    (p : ENNReal) :
    eLpNorm (fun w => S.scaleCoupling / 2 * f w) p P ≤
      ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) * ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
        eLpNorm f p P := by
  have e : (fun w => S.scaleCoupling / 2 * f w) = (S.scaleCoupling / 2) • f := by
    funext w
    simp
  rw [e, eLpNorm_const_smul, root_mul_root S hx, Real.enorm_eq_ofReal_abs, abs_of_pos (by positivity)]
  gcongr
  linarith
private theorem formProduct_measurable {m : ℕ} [NeZero m] (B : Finset (Fin Λ.k)) {Ω : Type} [MeasurableSpace Ω]
    {Z : Ω → ColourForm m} (hZ : Measurable Z) :
    Measurable (fun w => S.formProduct S.lastSeparated m B (Z w)) := by
  simp only [MomentPoint.formProduct]
  exact Finset.measurable_prod _ fun i _ => (colourEval_measurable _ hZ hZ).const_mul _
private theorem mean_formProduct_le {m : ℕ} [NeZero m] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hx : 0 < S.scaleCoupling) (B : Finset (Fin Λ.k)) (κ : ENNReal)
    (Nr : (Ω → ColourForm m) → ENNReal)
    (hQ : ∀ i ∈ B, ∀ X X' : Ω → ColourForm m, Measurable X → Measurable X' →
      eLpNorm (fun w => colourEval (S.supportForm S.lastSeparated m i) (X w) (X' w)) (B.card : ENNReal) P ≤
        κ * Nr X * Nr X')
    {Z : Ω → ColourForm m} (hZ : Measurable Z) {Y : ENNReal}
    (hY : ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) * Nr Z ≤ Y) :
    ∫⁻ w, ENNReal.ofReal |S.formProduct S.lastSeparated m B (Z w)| ∂P ≤ (κ * Y * Y) ^ B.card := by
  simp only [MomentPoint.formProduct]
  refine lintegral_abs_prod_le B P
    (fun i w => S.scaleCoupling / 2 * colourEval (S.supportForm S.lastSeparated m i) (Z w) (Z w)) ?_ _ ?_
  · exact fun i _ => (colourEval_measurable _ hZ hZ).const_mul _
  · intro i hi
    refine (half_le S P hx _ _).trans ?_
    set s := ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2))
    calc s * s * eLpNorm (fun w => colourEval (S.supportForm S.lastSeparated m i) (Z w) (Z w)) (B.card : ENNReal) P
        ≤ s * s * (κ * Nr Z * Nr Z) := by
          gcongr
          exact hQ i hi Z Z hZ hZ
      _ = κ * (s * Nr Z) * (s * Nr Z) := by ring
      _ ≤ κ * Y * Y := by gcongr
private theorem mean_formProduct_sub_le {m : ℕ} [NeZero m] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hx : 0 < S.scaleCoupling) (B : Finset (Fin Λ.k)) (κ : ENNReal)
    (Nr : (Ω → ColourForm m) → ENNReal)
    (hQ : ∀ i ∈ B, ∀ X X' : Ω → ColourForm m, Measurable X → Measurable X' →
      eLpNorm (fun w => colourEval (S.supportForm S.lastSeparated m i) (X w) (X' w)) (B.card : ENNReal) P ≤
        κ * Nr X * Nr X')
    {Z Z' : Ω → ColourForm m} (hZ : Measurable Z) (hZ' : Measurable Z') {Y D : ENNReal}
    (hY : ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) * Nr Z ≤ Y)
    (hY' : ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) * Nr Z' ≤ Y)
    (hD : ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) * Nr (fun w e b => Z w e b - Z' w e b) ≤ D) :
    ∫⁻ w, ENNReal.ofReal |S.formProduct S.lastSeparated m B (Z w) - S.formProduct S.lastSeparated m B (Z' w)| ∂P ≤
      (B.card : ENNReal) * ((κ * D * Y + κ * Y * D) * (2 * (κ * Y * Y)) ^ (B.card - 1)) := by
  simp only [MomentPoint.formProduct]
  set s := ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) with hs
  have hU : ∀ (W : Ω → ColourForm m), Measurable W → s * Nr W ≤ Y → ∀ i ∈ B,
      eLpNorm (fun w => S.scaleCoupling / 2 * colourEval (S.supportForm S.lastSeparated m i) (W w) (W w))
        (B.card : ENNReal) P ≤ κ * Y * Y := by
    intro W hW hWY i hi
    refine (half_le S P hx _ _).trans ?_
    calc s * s * eLpNorm (fun w => colourEval (S.supportForm S.lastSeparated m i) (W w) (W w)) (B.card : ENNReal) P
        ≤ s * s * (κ * Nr W * Nr W) := by
          gcongr
          exact hQ i hi W W hW hW
      _ = κ * (s * Nr W) * (s * Nr W) := by ring
      _ ≤ κ * Y * Y := by gcongr
  refine lintegral_abs_prod_sub_le B P
    (fun i w => S.scaleCoupling / 2 * colourEval (S.supportForm S.lastSeparated m i) (Z w) (Z w))
    (fun i w => S.scaleCoupling / 2 * colourEval (S.supportForm S.lastSeparated m i) (Z' w) (Z' w))
    (fun i _ => (colourEval_measurable _ hZ hZ).const_mul _) (fun i _ => (colourEval_measurable _ hZ' hZ').const_mul _)
    _ _ (hU Z hZ hY) (hU Z' hZ' hY') ?_
  intro i hi
  have hD' : Measurable (fun w e b => Z w e b - Z' w e b : Ω → ColourForm m) :=
    measurable_pi_lambda _ fun e => measurable_pi_lambda _ fun b =>
      ((proj_measurable e b).comp hZ).sub ((proj_measurable e b).comp hZ')
  have e : (fun w => S.scaleCoupling / 2 * colourEval (S.supportForm S.lastSeparated m i) (Z w) (Z w) -
      S.scaleCoupling / 2 * colourEval (S.supportForm S.lastSeparated m i) (Z' w) (Z' w)) =
      fun w => S.scaleCoupling / 2 *
        (((fun w => colourEval (S.supportForm S.lastSeparated m i) (fun e b => Z w e b - Z' w e b) (Z w)) +
          fun w => colourEval (S.supportForm S.lastSeparated m i) (Z' w) (fun e b => Z w e b - Z' w e b)) w) := by
    funext w
    rw [Pi.add_apply, ← colourEval_sub, mul_sub]
  rw [e]
  refine (half_le S P hx _ _).trans ?_
  have hc : (1 : ENNReal) ≤ (B.card : ENNReal) := by
    exact_mod_cast Finset.card_pos.mpr ⟨i, hi⟩
  calc s * s * eLpNorm ((fun w => colourEval (S.supportForm S.lastSeparated m i) (fun e b => Z w e b - Z' w e b) (Z w)) +
        fun w => colourEval (S.supportForm S.lastSeparated m i) (Z' w) (fun e b => Z w e b - Z' w e b))
          (B.card : ENNReal) P
      ≤ s * s * (κ * Nr (fun w e b => Z w e b - Z' w e b) * Nr Z +
          κ * Nr Z' * Nr (fun w e b => Z w e b - Z' w e b)) := by
        gcongr
        exact (eLpNorm_add_le (colourEval_measurable _ hD' hZ).aestronglyMeasurable
          (colourEval_measurable _ hZ' hD').aestronglyMeasurable hc).trans
          (add_le_add (hQ i hi _ _ hD' hZ) (hQ i hi _ _ hZ' hD'))
    _ = κ * (s * Nr (fun w e b => Z w e b - Z' w e b)) * (s * Nr Z) +
        κ * (s * Nr Z') * (s * Nr (fun w e b => Z w e b - Z' w e b)) := by ring
    _ ≤ κ * D * Y + κ * Y * D := by gcongr
end Core
section Means
variable {Λ : MomentParameters} (S : MomentPoint Λ) (d n : ℕ) [NeZero n]
private theorem noisy_measurable (c : ℝ) {Ω : Type} [MeasurableSpace Ω] {A : Ω → ColourForm n} (hA : Measurable A) :
    Measurable (fun z : Ω × FluctuationSample Λ.stepParams.side S.lastSeparated d n =>
      descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated c d n (A z.1) z.2) :=
  (descendWithNoise_measurable Λ.stepParams.coupling Λ.table.ρA S.lastSeparated c d n).comp
    ((hA.comp measurable_fst).prodMk measurable_snd)
private theorem sample_measurable (c : ℝ) (A : ColourForm n) :
    Measurable (fun w : FluctuationSample Λ.stepParams.side S.lastSeparated d n =>
      descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated c d n A w) :=
  (descendWithNoise_measurable Λ.stepParams.coupling Λ.table.ρA S.lastSeparated c d n).comp
    (measurable_const.prodMk measurable_id)
private theorem mean_abs_le (B : Finset (Fin Λ.k)) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    {A : Ω → ColourForm n} (hA : Measurable A) :
    ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w)| ∂μ ≤
      ∫⁻ z, ENNReal.ofReal |S.formProduct S.lastSeparated (fineSide Λ.stepParams.side d n) B
          (descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated
            (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d n (A z.1) z.2)|
        ∂(μ.prod (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n)) := by
  have := sampleLaw_isProb Λ.stepParams.coupling (L := Λ.stepParams.side) S.lastSeparated d n
  rw [lintegral_prod _ ((formProduct_measurable S B (noisy_measurable S d n _ hA)).abs.ennreal_ofReal).aemeasurable]
  refine lintegral_mono fun w => ?_
  simp only [← Real.enorm_eq_ofReal_abs, MomentPoint.formProductMean]
  exact enorm_integral_le_lintegral_enorm _
private theorem mean_sub_le (B : Finset (Fin Λ.k))
    (hint : ∀ A₀ : ColourForm n, Integrable (fun w => S.formProduct S.lastSeparated (fineSide Λ.stepParams.side d n) B
      (descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d n A₀ w))
      (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n))
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {A A' : Ω → ColourForm n} (hA : Measurable A)
    (hA' : Measurable A') :
    ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w) - S.formProductMean d n B (A' w)| ∂μ ≤
      ∫⁻ z, ENNReal.ofReal |S.formProduct S.lastSeparated (fineSide Λ.stepParams.side d n) B
            (descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated
              (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d n (A z.1) z.2) -
          S.formProduct S.lastSeparated (fineSide Λ.stepParams.side d n) B
            (descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated
              (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d n (A' z.1) z.2)|
        ∂(μ.prod (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n)) := by
  have := sampleLaw_isProb Λ.stepParams.coupling (L := Λ.stepParams.side) S.lastSeparated d n
  refine le_of_le_of_eq ?_ (lintegral_prod _ (((formProduct_measurable S B (noisy_measurable S d n _ hA)).sub
    (formProduct_measurable S B (noisy_measurable S d n _ hA'))).abs.ennreal_ofReal).aemeasurable).symm
  refine lintegral_mono fun w => ?_
  simp only [← Real.enorm_eq_ofReal_abs, MomentPoint.formProductMean]
  rw [← integral_sub (hint _) (hint _)]
  exact enorm_integral_le_lintegral_enorm _
variable {d n}
private theorem curvNorm_noisy_le (hx : 0 < S.scaleCoupling) {q : ENNReal} (hq : 1 ≤ q)
    (ω₁ : TorusPlaquette (fineSide Λ.stepParams.side d n) → ℝ) (ω₂ : TorusPlaquette n → ℝ)
    {th cξ : ENNReal} {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hC : ∀ X : Ω → ColourForm n, Measurable X →
      weightedCurvatureNorm μ ω₁ q
        (fun w => descend (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n (X w)) ≤
        th * weightedCurvatureNorm μ ω₂ q X)
    (hξ : weightedCurvatureNorm (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n) ω₁ q
      (descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated 1 d n 0) ≤ cξ)
    {A : Ω → ColourForm n} (hA : Measurable A) :
    ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
        weightedCurvatureNorm (μ.prod (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n))
          ω₁ q (fun z => descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated
            (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d n (A z.1) z.2) ≤
      th * (ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) * weightedCurvatureNorm μ ω₂ q A) + cξ := by
  have := sampleLaw_isProb Λ.stepParams.coupling (L := Λ.stepParams.side) S.lastSeparated d n
  set c := S.scaleCoupling ^ (-(1 / 2) : ℝ)
  set s := ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2))
  set ξ := descendWithNoise (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated 1 d n
    (0 : ColourForm n)
  have e : (fun z : Ω × FluctuationSample Λ.stepParams.side S.lastSeparated d n =>
      descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated c d n (A z.1) z.2) =
      fun z e b => descend (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n (A z.1) e b +
        c * ξ z.2 e b :=
    funext fun z => descendWithNoise_eq Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n c (A z.1) z.2
  have hξm : Measurable ξ := sample_measurable S d n 1 0
  have hM : Measurable (fun w =>
      descend (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n (A w)) :=
    (descend_measurable Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n).comp hA
  have hX : Measurable (fun z : Ω × FluctuationSample Λ.stepParams.side S.lastSeparated d n =>
      descend (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n (A z.1)) :=
    hM.comp measurable_fst
  have hY : Measurable (fun (z : Ω × FluctuationSample Λ.stepParams.side S.lastSeparated d n) (e : Fin 3) b =>
      c * ξ z.2 e b) :=
    measurable_pi_lambda _ fun e => measurable_pi_lambda _ fun b =>
      (((proj_measurable e b).comp hξm).comp measurable_snd).const_mul c
  rw [e]
  have h1 := curvNorm_add_le
    (μ.prod (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n)) ω₁ hq hX hY
  have h2 : weightedCurvatureNorm
      (μ.prod (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n)) ω₁ q
      (fun z : Ω × FluctuationSample Λ.stepParams.side S.lastSeparated d n =>
        descend (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n (A z.1)) ≤
      th * weightedCurvatureNorm μ ω₂ q A := by
    rw [curvNorm_comp μ _ measurePreserving_fst ω₁ q hM]
    exact hC A hA
  have h3 : weightedCurvatureNorm
      (μ.prod (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n)) ω₁ q
      (fun (z : Ω × FluctuationSample Λ.stepParams.side S.lastSeparated d n) (e : Fin 3) b => c * ξ z.2 e b) ≤
        ENNReal.ofReal |c| * cξ := by
    refine (curvNorm_const_mul_le _ ω₁ q c _).trans ?_
    rw [curvNorm_comp (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n) _
      measurePreserving_snd ω₁ q hξm]
    gcongr
  calc s * _ ≤ s * (th * weightedCurvatureNorm μ ω₂ q A + ENNReal.ofReal |c| * cξ) := by
        gcongr
        exact h1.trans (add_le_add h2 h3)
    _ = th * (s * weightedCurvatureNorm μ ω₂ q A) + (s * ENNReal.ofReal |c|) * cξ := by ring
    _ = _ := by rw [root_mul_inverse S hx, one_mul]
private theorem curvNorm_noisy_sub_le {q : ENNReal} (ω₁ : TorusPlaquette (fineSide Λ.stepParams.side d n) → ℝ)
    (ω₂ : TorusPlaquette n → ℝ) {th : ENNReal} {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hC : ∀ X : Ω → ColourForm n, Measurable X →
      weightedCurvatureNorm μ ω₁ q
        (fun w => descend (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n (X w)) ≤
        th * weightedCurvatureNorm μ ω₂ q X)
    {A A' : Ω → ColourForm n} (hA : Measurable A) (hA' : Measurable A') :
    ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
        weightedCurvatureNorm (μ.prod (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n))
          ω₁ q
          (fun z e b => descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated
              (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d n (A z.1) z.2 e b -
            descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated
              (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d n (A' z.1) z.2 e b) ≤
      th * (ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
        weightedCurvatureNorm μ ω₂ q (fun w => A w - A' w)) := by
  have := sampleLaw_isProb Λ.stepParams.coupling (L := Λ.stepParams.side) S.lastSeparated d n
  have hD : Measurable (fun w => A w - A' w) := hA.sub hA'
  have hM : Measurable (fun w =>
      descend (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n (A w - A' w)) :=
    (descend_measurable Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n).comp hD
  have e : (fun (z : Ω × FluctuationSample Λ.stepParams.side S.lastSeparated d n) e b =>
      descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated
          (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d n (A z.1) z.2 e b -
        descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated
          (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d n (A' z.1) z.2 e b) =
      fun z => descend (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n
        (A z.1 - A' z.1) := by
    funext z e b
    rw [descendWithNoise_eq Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n _ (A z.1),
      descendWithNoise_eq Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n _ (A' z.1)]
    have h := congrFun (congrFun
      (descend_sub Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n (A z.1) (A' z.1)) e) b
    have e2 : (fun (e : Fin 3) b => A z.1 e b - A' z.1 e b) = A z.1 - A' z.1 := rfl
    rw [e2] at h
    rw [h]
    ring
  rw [e, curvNorm_comp μ _ measurePreserving_fst ω₁ q hM]
  calc _ ≤ ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
        (th * weightedCurvatureNorm μ ω₂ q (fun w => A w - A' w)) := by
        gcongr
        exact hC _ hD
    _ = _ := by ring
end Means
section Bounds
variable {Λ : MomentParameters} (S : MomentPoint Λ) {d n : ℕ} [NeZero n]
private theorem curvNorm_zero {m : ℕ} [NeZero m] {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (ω : TorusPlaquette m → ℝ) (q : ENNReal) :
    weightedCurvatureNorm μ ω q (fun _ : Ω => (0 : ColourForm m)) = 0 := by
  unfold weightedCurvatureNorm
  have e : ∀ p : TorusPlaquette m, curlNorm (0 : ColourForm m) p = 0 := by
    intro p
    simp [curlNorm, curl]
  simp [e]
private theorem formProduct_integrable (hx : 0 < S.scaleCoupling) (B : Finset (Fin Λ.k)) {q : ENNReal} (hq : 1 ≤ q)
    (ω₁ : TorusPlaquette (fineSide Λ.stepParams.side d n) → ℝ) {κ cξ : ENNReal} (hκ : κ < ⊤) (hcξ : cξ < ⊤)
    (hQ : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P], ∀ i ∈ B,
      ∀ X X' : Ω → ColourForm (fineSide Λ.stepParams.side d n), Measurable X → Measurable X' →
      eLpNorm (fun w => colourEval (S.supportForm S.lastSeparated (fineSide Λ.stepParams.side d n) i) (X w) (X' w))
          (B.card : ENNReal) P ≤
        κ * weightedCurvatureNorm P ω₁ q X * weightedCurvatureNorm P ω₁ q X')
    (hξ : weightedCurvatureNorm (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n) ω₁ q
      (descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated 1 d n 0) ≤ cξ)
    (A₀ : ColourForm n) :
    Integrable (fun w => S.formProduct S.lastSeparated (fineSide Λ.stepParams.side d n) B
      (descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d n A₀ w))
      (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n) := by
  have := sampleLaw_isProb Λ.stepParams.coupling (L := Λ.stepParams.side) S.lastSeparated d n
  set P := fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n
  set c := S.scaleCoupling ^ (-(1 / 2) : ℝ)
  have hZ := sample_measurable S d n c A₀
  refine ⟨(formProduct_measurable S B hZ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp only [Real.enorm_eq_ofReal_abs]
  refine lt_of_le_of_lt (mean_formProduct_le S P hx B κ (weightedCurvatureNorm P ω₁ q) (hQ _ P) hZ le_rfl) ?_
  set ξ := descendWithNoise (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated 1 d n
    (0 : ColourForm n)
  have hξm : Measurable ξ := sample_measurable S d n 1 0
  have e : (fun w => descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated c d n A₀ w) =
      fun w e b => (fun _ : FluctuationSample Λ.stepParams.side S.lastSeparated d n =>
        descend (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n A₀) w e b +
          c * ξ w e b :=
    funext fun w => descendWithNoise_eq Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n c A₀ w
  have hY : Measurable (fun (w : FluctuationSample Λ.stepParams.side S.lastSeparated d n) (e : Fin 3) b =>
      c * ξ w e b) :=
    measurable_pi_lambda _ fun e => measurable_pi_lambda _ fun b =>
      ((proj_measurable e b).comp hξm).const_mul c
  have hN : weightedCurvatureNorm P ω₁ q
      (fun w => descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated c d n A₀ w) < ⊤ := by
    rw [e]
    refine lt_of_le_of_lt (curvNorm_add_le P ω₁ hq measurable_const hY) ?_
    refine ENNReal.add_lt_top.mpr ⟨curvNorm_const_lt_top P ω₁ _,
      lt_of_le_of_lt (curvNorm_const_mul_le P ω₁ q c ξ) ?_⟩
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt hξ hcξ)
  have hy := ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := S.scaleCoupling ^ ((1 : ℝ) / 2))) hN
  exact ENNReal.pow_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top hκ hy) hy)
private theorem raw_bounds (hx : 0 < S.scaleCoupling) (B : Finset (Fin Λ.k)) {q : ENNReal} (hq : 1 ≤ q)
    (ω₁ : TorusPlaquette (fineSide Λ.stepParams.side d n) → ℝ) (ω₂ : TorusPlaquette n → ℝ) {κ th cξ K : ENNReal}
    (hκ : κ < ⊤) (hcξ : cξ < ⊤) (hth : th ≤ 1) (hK : 1 ≤ K) (hcK : cξ ≤ K)
    (hQ : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P], ∀ i ∈ B,
      ∀ X X' : Ω → ColourForm (fineSide Λ.stepParams.side d n), Measurable X → Measurable X' →
      eLpNorm (fun w => colourEval (S.supportForm S.lastSeparated (fineSide Λ.stepParams.side d n) i) (X w) (X' w))
          (B.card : ENNReal) P ≤
        κ * weightedCurvatureNorm P ω₁ q X * weightedCurvatureNorm P ω₁ q X')
    (hξ : weightedCurvatureNorm (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n) ω₁ q
      (descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated 1 d n 0) ≤ cξ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hC : ∀ X : Ω → ColourForm n, Measurable X →
      weightedCurvatureNorm μ ω₁ q
        (fun w => descend (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n (X w)) ≤
        th * weightedCurvatureNorm μ ω₂ q X)
    {A A' : Ω → ColourForm n} (hA : Measurable A) (hA' : Measurable A') {y : ENNReal}
    (hy : y = 1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
      (weightedCurvatureNorm μ ω₂ q A + weightedCurvatureNorm μ ω₂ q A')) :
    ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w)| ∂μ ≤ (κ * (K * y) * (K * y)) ^ B.card ∧
    ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w) - S.formProductMean d n B (A' w)| ∂μ ≤
      (B.card : ENNReal) * ((κ * (th * (ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          weightedCurvatureNorm μ ω₂ q (fun w => A w - A' w))) * (K * y) +
        κ * (K * y) * (th * (ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          weightedCurvatureNorm μ ω₂ q (fun w => A w - A' w)))) *
          (2 * (κ * (K * y) * (K * y))) ^ (B.card - 1)) := by
  have := sampleLaw_isProb Λ.stepParams.coupling (L := Λ.stepParams.side) S.lastSeparated d n
  set c := S.scaleCoupling ^ (-(1 / 2) : ℝ)
  set s := ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2))
  set P := μ.prod (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n)
  have hZ := noisy_measurable S d n c hA
  have hZ' := noisy_measurable S d n c hA'
  have hone : ∀ {u v : ENNReal}, u ≤ v → th * u + cξ ≤ K * (1 + v) := by
    intro u v huv
    calc th * u + cξ ≤ 1 * v + K * 1 := by
          gcongr
          simpa using hcK
      _ ≤ K * v + K * 1 := by gcongr
      _ = K * (1 + v) := by ring
  have hY : s * weightedCurvatureNorm P ω₁ q
      (fun z => descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated c d n (A z.1) z.2) ≤ K * y := by
    refine (curvNorm_noisy_le S hx hq ω₁ ω₂ μ hC hξ hA).trans ?_
    rw [hy]
    exact hone (by gcongr; exact le_self_add)
  have hY' : s * weightedCurvatureNorm P ω₁ q
      (fun z => descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated c d n (A' z.1) z.2) ≤ K * y := by
    refine (curvNorm_noisy_le S hx hq ω₁ ω₂ μ hC hξ hA').trans ?_
    rw [hy]
    exact hone (by gcongr; exact le_add_self)
  refine ⟨(mean_abs_le S d n B μ hA).trans
    (mean_formProduct_le S P hx B κ (weightedCurvatureNorm P ω₁ q) (hQ _ P) hZ hY), ?_⟩
  refine (mean_sub_le S d n B (formProduct_integrable S hx B hq ω₁ hκ hcξ hQ hξ) μ hA hA').trans ?_
  exact mean_formProduct_sub_le S P hx B κ (weightedCurvatureNorm P ω₁ q) (hQ _ P) hZ hZ' hY hY'
    (curvNorm_noisy_sub_le S ω₁ ω₂ μ hC hA hA')
end Bounds
section Constants
private theorem real_constants {k : ℕ} (hk : 1 ≤ k) {c k₁ : ℝ} (hc : 0 ≤ c) (hk₁ : 1 ≤ k₁) {b : ℕ} (hb : b ≤ k) :
    c ^ b * k₁ ^ (2 * b) ≤ k * (1 + 2 * c) ^ k * k₁ ^ (2 * k) ∧
    (b : ℝ) * (2 * c) ^ b * k₁ ^ (2 * b - 1) ≤ k * (1 + 2 * c) ^ k * k₁ ^ (2 * k) := by
  have h1 : (1 : ℝ) ≤ 1 + 2 * c := by linarith
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb' : (b : ℝ) ≤ k := by exact_mod_cast hb
  have hp : (1 + 2 * c) ^ b ≤ (1 + 2 * c) ^ k := pow_le_pow_right₀ h1 hb
  have hpos : 0 ≤ (1 + 2 * c) ^ k := by positivity
  have hq1 : k₁ ^ (2 * b) ≤ k₁ ^ (2 * k) := pow_le_pow_right₀ hk₁ (by omega)
  have hq2 : k₁ ^ (2 * b - 1) ≤ k₁ ^ (2 * k) := pow_le_pow_right₀ hk₁ (by omega)
  have hc1 : c ^ b ≤ (1 + 2 * c) ^ k := (pow_le_pow_left₀ hc (by linarith) b).trans hp
  have hc2 : (2 * c) ^ b ≤ (1 + 2 * c) ^ k := (pow_le_pow_left₀ (by positivity) (by linarith) b).trans hp
  constructor
  · calc c ^ b * k₁ ^ (2 * b) ≤ (1 + 2 * c) ^ k * k₁ ^ (2 * k) := mul_le_mul hc1 hq1 (by positivity) hpos
      _ = 1 * ((1 + 2 * c) ^ k * k₁ ^ (2 * k)) := by ring
      _ ≤ (k : ℝ) * ((1 + 2 * c) ^ k * k₁ ^ (2 * k)) := mul_le_mul_of_nonneg_right hk' (by positivity)
      _ = _ := by ring
  · exact mul_le_mul (mul_le_mul hb' hc2 (by positivity) (by positivity)) hq2 (by positivity) (by positivity)
private theorem first_bound {c k₁ R C₀ : ℝ} (hc : 0 ≤ c) (hk₁ : 1 ≤ k₁) (hR : 0 ≤ R) {b : ℕ}
    (hC : c ^ b * k₁ ^ (2 * b) ≤ C₀) (y : ENNReal) :
    (ENNReal.ofReal (c * R) * (ENNReal.ofReal k₁ * y) * (ENNReal.ofReal k₁ * y)) ^ b ≤
      ENNReal.ofReal (C₀ * R ^ b) * y ^ (2 * b) := by
  have hk : 0 ≤ k₁ := by linarith
  have e : (ENNReal.ofReal (c * R) * (ENNReal.ofReal k₁ * y) * (ENNReal.ofReal k₁ * y)) ^ b =
      ENNReal.ofReal ((c ^ b * k₁ ^ (2 * b)) * R ^ b) * y ^ (2 * b) := by
    have hr : ENNReal.ofReal ((c ^ b * k₁ ^ (2 * b)) * R ^ b) =
        ENNReal.ofReal c ^ b * ENNReal.ofReal k₁ ^ (2 * b) * ENNReal.ofReal R ^ b := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow hc, ENNReal.ofReal_pow hk, ENNReal.ofReal_pow hR]
    rw [ENNReal.ofReal_mul hc, hr]
    ring
  rw [e]
  gcongr
private theorem second_bound {c k₁ R C₀ : ℝ} (hc : 0 ≤ c) (hk₁ : 1 ≤ k₁) (hR : 0 ≤ R) {b : ℕ} (hb : 1 ≤ b)
    (hC : (b : ℝ) * (2 * c) ^ b * k₁ ^ (2 * b - 1) ≤ C₀) (y D : ENNReal) :
    (b : ENNReal) * ((ENNReal.ofReal (c * R) * D * (ENNReal.ofReal k₁ * y) +
        ENNReal.ofReal (c * R) * (ENNReal.ofReal k₁ * y) * D) *
      (2 * (ENNReal.ofReal (c * R) * (ENNReal.ofReal k₁ * y) * (ENNReal.ofReal k₁ * y))) ^ (b - 1)) ≤
      ENNReal.ofReal (C₀ * R ^ b) * D * y ^ (2 * b - 1) := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hk : 0 ≤ k₁ := by linarith
  have e2 : (2 : ENNReal) = ENNReal.ofReal 2 := by simp
  have e : (((b' + 1 : ℕ) : ENNReal)) * ((ENNReal.ofReal (c * R) * D * (ENNReal.ofReal k₁ * y) +
        ENNReal.ofReal (c * R) * (ENNReal.ofReal k₁ * y) * D) *
      (2 * (ENNReal.ofReal (c * R) * (ENNReal.ofReal k₁ * y) * (ENNReal.ofReal k₁ * y))) ^ (b' + 1 - 1)) =
      ENNReal.ofReal ((((b' + 1 : ℕ) : ℝ) * (2 * c) ^ (b' + 1) * k₁ ^ (2 * (b' + 1) - 1)) * R ^ (b' + 1)) * D *
        y ^ (2 * (b' + 1) - 1) := by
    have h1 : 2 * (b' + 1) - 1 = 2 * b' + 1 := by omega
    rw [h1, Nat.add_sub_cancel]
    have hr : ENNReal.ofReal ((((b' + 1 : ℕ) : ℝ) * (2 * c) ^ (b' + 1) * k₁ ^ (2 * b' + 1)) * R ^ (b' + 1)) =
        ((b' + 1 : ℕ) : ENNReal) * (2 * ENNReal.ofReal c) ^ (b' + 1) * ENNReal.ofReal k₁ ^ (2 * b' + 1) *
          ENNReal.ofReal R ^ (b' + 1) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow hk, ENNReal.ofReal_pow hR,
        ENNReal.ofReal_mul (by norm_num), ← e2]
    rw [ENNReal.ofReal_mul hc, hr]
    ring
  rw [e]
  gcongr
end Constants
section ThreeBounds
variable {Λ : MomentParameters} (S : MomentPoint Λ) {d n : ℕ} [NeZero n]
private theorem three_bounds (hx : 0 < S.scaleCoupling) (B : Finset (Fin Λ.k)) {q : ENNReal} (hq : 1 ≤ q)
    (ω₁ : TorusPlaquette (fineSide Λ.stepParams.side d n) → ℝ) (ω₂ : TorusPlaquette n → ℝ) {th cξ : ENNReal}
    {c k₁ C₀ : ℝ} (hc : 0 ≤ c) (hk₁ : 1 ≤ k₁)
    (hC₁ : c ^ B.card * k₁ ^ (2 * B.card) ≤ C₀)
    (hC₂ : (B.card : ℝ) * (2 * c) ^ B.card * k₁ ^ (2 * B.card - 1) ≤ C₀)
    (hC₀ : 0 ≤ C₀) (hth : th ≤ 1) (hthL : th ≤ ENNReal.ofReal ((Λ.stepParams.side : ℝ) ^ (-(d : ℝ) / 4)))
    (hcK : cξ ≤ ENNReal.ofReal k₁)
    (hQ : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P], ∀ i ∈ B,
      ∀ X X' : Ω → ColourForm (fineSide Λ.stepParams.side d n), Measurable X → Measurable X' →
      eLpNorm (fun w => colourEval (S.supportForm S.lastSeparated (fineSide Λ.stepParams.side d n) i) (X w) (X' w))
          (B.card : ENNReal) P ≤
        ENNReal.ofReal (c * (S.range : ℝ) ^ 4) * weightedCurvatureNorm P ω₁ q X * weightedCurvatureNorm P ω₁ q X')
    (hξ : weightedCurvatureNorm (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n) ω₁ q
      (descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated 1 d n 0) ≤ cξ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hCn : ∀ X : Ω → ColourForm n, Measurable X →
      weightedCurvatureNorm μ ω₁ q
        (fun w => descend (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n (X w)) ≤
        th * weightedCurvatureNorm μ ω₂ q X)
    {A A' : Ω → ColourForm n} (hA : Measurable A) (hA' : Measurable A') :
    ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w)| ∂μ ≤
        ENNReal.ofReal (C₀ * (S.range : ℝ) ^ (4 * B.card)) * (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm μ ω₂ q A + weightedCurvatureNorm μ ω₂ q A')) ^ (2 * B.card) ∧
    ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w) - S.formProductMean d n B 0| ∂μ ≤
        ENNReal.ofReal (C₀ * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(d : ℝ) / 4)) *
          (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm μ ω₂ q A + weightedCurvatureNorm μ ω₂ q A')) ^ (2 * B.card) ∧
    ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w) - S.formProductMean d n B (A' w)| ∂μ ≤
        ENNReal.ofReal (C₀ * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          weightedCurvatureNorm μ ω₂ q (fun w => A w - A' w) *
          (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
            (weightedCurvatureNorm μ ω₂ q A + weightedCurvatureNorm μ ω₂ q A')) ^ (2 * B.card - 1) := by
  set s := ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) with hs
  set y := 1 + s * (weightedCurvatureNorm μ ω₂ q A + weightedCurvatureNorm μ ω₂ q A') with hy
  set R : ℝ := (S.range : ℝ) ^ 4 with hRd
  have hR : 0 ≤ R := by positivity
  have hpow : (S.range : ℝ) ^ (4 * B.card) = R ^ B.card := by rw [hRd, pow_mul]
  have hk₁ : (1 : ENNReal) ≤ ENNReal.ofReal k₁ := by simpa using ENNReal.ofReal_le_ofReal hk₁
  have hcξ : cξ < ⊤ := lt_of_le_of_lt hcK ENNReal.ofReal_lt_top
  have hκ : ENNReal.ofReal (c * R) < ⊤ := ENNReal.ofReal_lt_top
  have raw := raw_bounds S hx B hq ω₁ ω₂ hκ hcξ hth hk₁ hcK hQ hξ μ hCn hA hA' hy
  have raw0 := raw_bounds S hx B hq ω₁ ω₂ hκ hcξ hth hk₁ hcK hQ hξ μ hCn hA
    (measurable_const (a := (0 : ColourForm n))) rfl
  have hk₁' : (1 : ℝ) ≤ k₁ := ‹_›
  rw [hpow]
  have hT : 0 ≤ C₀ * R ^ B.card := by positivity
  refine ⟨raw.1.trans (first_bound hc hk₁' hR hC₁ y), ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos B.card with h0 | hb
    · refine raw0.2.trans ?_
      simp [h0]
    · have hN0 := curvNorm_zero μ ω₂ q (Ω := Ω) (m := n)
      set y₀ := 1 + s * (weightedCurvatureNorm μ ω₂ q A +
        weightedCurvatureNorm μ ω₂ q (fun _ : Ω => (0 : ColourForm n))) with hy₀
      have hyy : y₀ ≤ y := by
        rw [hy₀, hy, hN0, add_zero]
        gcongr
        exact le_self_add
      have hsN : s * weightedCurvatureNorm μ ω₂ q A ≤ y := by
        rw [hy]
        refine le_trans ?_ le_add_self
        gcongr
        exact le_self_add
      have h2 := raw0.2
      simp only [sub_zero] at h2
      refine h2.trans ((second_bound hc hk₁' hR hb hC₂ y₀ _).trans ?_)
      have e2 : 2 * B.card = (2 * B.card - 1) + 1 := by omega
      calc ENNReal.ofReal (C₀ * R ^ B.card) * (th * (s * weightedCurvatureNorm μ ω₂ q fun w => A w)) *
            y₀ ^ (2 * B.card - 1)
          ≤ ENNReal.ofReal (C₀ * R ^ B.card) *
              (ENNReal.ofReal ((Λ.stepParams.side : ℝ) ^ (-(d : ℝ) / 4)) * y) * y ^ (2 * B.card - 1) := by
            gcongr
        _ = ENNReal.ofReal (C₀ * R ^ B.card * (Λ.stepParams.side : ℝ) ^ (-(d : ℝ) / 4)) * y ^ (2 * B.card) := by
            rw [ENNReal.ofReal_mul hT]
            conv_rhs => rw [e2, pow_succ]
            ring
  · rcases Nat.eq_zero_or_pos B.card with h0 | hb
    · refine raw.2.trans ?_
      simp [h0]
    · refine raw.2.trans ((second_bound hc hk₁' hR hb hC₂ y _).trans ?_)
      calc ENNReal.ofReal (C₀ * R ^ B.card) * (th * (s * weightedCurvatureNorm μ ω₂ q fun w => A w - A' w)) *
            y ^ (2 * B.card - 1)
          ≤ ENNReal.ofReal (C₀ * R ^ B.card) * (1 * (s * weightedCurvatureNorm μ ω₂ q fun w => A w - A' w)) *
              y ^ (2 * B.card - 1) := by
            gcongr
        _ = _ := by
            rw [ENNReal.ofReal_mul hT]
            ring
end ThreeBounds
section Sides
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem side_below {d : ℕ} (h : S.lastSeparated + d ≤ S.data.windowLevel) :
    fineSide Λ.stepParams.side d (S.levelSide (S.lastSeparated + d)) = S.levelSide S.lastSeparated := by
  rw [fineSide_eq]
  simp only [LevelTestFunctions.LevelData.sideAt]
  rw [mul_assoc, ← pow_add]
  congr 2
  omega
private theorem side_top {N e : ℕ} (h : S.lastSeparated + N + e = S.data.windowLevel) :
    S.levelSide (S.lastSeparated + N) = fineSide Λ.stepParams.side e (S.data.period Λ.stepParams.side) := by
  rw [fineSide_eq]
  simp only [LevelTestFunctions.LevelData.sideAt]
  congr 2
  omega
private theorem side_large (hD : Λ.table.Admissible) (u : ℕ) : 64 ≤ S.levelSide u := by
  have h1 := S.side_le
  have h2 : 4096 ≤ Λ.stepParams.n₀ := hD.n₀_ge
  have hL : 1 ≤ Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have h3 : S.data.period Λ.stepParams.side ≤ S.levelSide u := by
    simp only [LevelTestFunctions.LevelData.sideAt]
    exact Nat.le_mul_of_pos_right _ (pow_pos hL _)
  nlinarith
private theorem distanceWeight_le_one (hD : Λ.table.Admissible) (u n : ℕ) [NeZero n] (p : TorusPlaquette n) :
    S.distanceWeight u n p ≤ 1 := by
  unfold MomentPoint.distanceWeight
  rw [Real.exp_le_one_iff, neg_nonpos]
  have hr : 0 ≤ Λ.stepParams.weightRate := by
    have := hD.rt_pos
    show 0 ≤ Λ.table.rt / 2 ^ 10
    positivity
  exact mul_nonneg (by positivity) (le_max_left _ _)
end Sides
section Chain
variable {L : ℕ} [NeZero L]
private theorem chainLower_measurable {s n : ℕ} :
    Measurable (chainLower : LevelChain L (s + 1) n → LevelChain L s (n * L)) := by apply _root_.YangMills.SharedProofs.p17945 <;> assumption
private theorem chainTop_measurable : ∀ s n : ℕ, Measurable (chainTop s n : LevelChain L s n → ColourForm n)
  | 0, _ => measurable_id
  | s + 1, n => measurable_pi_lambda _ fun e => measurable_pi_lambda _ fun b =>
    (measurable_pi_apply (Sum.inr b : LevelBond L (s + 1) n)).comp (measurable_pi_apply e)
private theorem chainDescend_measurable (s : ℕ) : ∀ d n : ℕ,
    Measurable (chainDescend s d n : LevelChain L (s + d) n → LevelChain L s (fineSide L d n))
  | 0, _ => measurable_id
  | d + 1, n => (chainDescend_measurable s d (n * L)).comp chainLower_measurable
private theorem chainLower_heq {s₁ s₂ n : ℕ} (h : s₁ = s₂) (X₁ : LevelChain L (s₁ + 1) n)
    (X₂ : LevelChain L (s₂ + 1) n) (hX : HEq X₁ X₂) : HEq (chainLower X₁) (chainLower X₂) := by
  subst h
  rw [eq_of_heq hX]
private theorem chainDescend_assoc (s N : ℕ) : ∀ (e n : ℕ) (X₁ : LevelChain L (s + (N + e)) n)
    (X₂ : LevelChain L (s + N + e) n), HEq X₁ X₂ →
    HEq (chainDescend s (N + e) n X₁) (chainDescend s N (fineSide L e n) (chainDescend (s + N) e n X₂))
  | 0, n, X₁, X₂, h => by
    have : X₁ = X₂ := eq_of_heq h
    rw [this]
    rfl
  | e + 1, n, X₁, X₂, h =>
    chainDescend_assoc s N e (n * L) (chainLower X₁) (chainLower X₂)
      (chainLower_heq (s₁ := s + (N + e)) (s₂ := s + N + e) (by omega) X₁ X₂ h)
private theorem chain_transport {s₁ s₂ n : ℕ} [NeZero n] (a : ℝ) (h : s₁ = s₂) (μ₁ : Measure (LevelChain L s₁ n))
    (hμ₁ : IsCanonicalGaussian (levelEnergy a s₁ n) μ₁) :
    ∃ μ₂ : Measure (LevelChain L s₂ n), IsCanonicalGaussian (levelEnergy a s₂ n) μ₂ ∧
      ∀ (f₁ : LevelChain L s₁ n → ℝ) (f₂ : LevelChain L s₂ n → ℝ),
        (∀ X₁ X₂, HEq X₁ X₂ → f₁ X₁ = f₂ X₂) → ∫ X, f₁ X ∂μ₁ = ∫ X, f₂ X ∂μ₂ := by
  subst h
  refine ⟨μ₁, hμ₁, fun f₁ f₂ hf => ?_⟩
  congr 1
  funext X
  exact hf X X HEq.rfl
end Chain
section Moments
private theorem gaussian_eLpNorm_le (q : ENNReal) (v : NNReal) :
    eLpNorm id q (gaussianReal 0 v) ≤
      ENNReal.ofReal (Real.sqrt v) * eLpNorm id q (gaussianReal 0 1) := by
  have hmap := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt v)
  have e : NNReal.mk (Real.sqrt v ^ 2) (sq_nonneg _) * 1 = v := by
    rw [mul_one]
    apply NNReal.eq
    exact Real.sq_sqrt v.coe_nonneg
  rw [e, mul_zero] at hmap
  rw [← hmap, eLpNorm_map_measure measurable_id.aestronglyMeasurable (measurable_const_mul _).aemeasurable]
  have e2 : (id ∘ fun x : ℝ => Real.sqrt v * x) = Real.sqrt v • (id : ℝ → ℝ) := by
    funext x
    simp
  rw [e2, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
variable {m : ℕ} [NeZero m]
private theorem curl_sq_le (X : ColourForm m) (p : TorusPlaquette m) (e : Fin 3) :
    curl (X e) p ^ 2 ≤ curlNorm X p ^ 2 := by
  have h : 0 ≤ ∑ e : Fin 3, curl (X e) p ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [curlNorm, Real.sq_sqrt h]
  exact Finset.single_le_sum (f := fun e : Fin 3 => curl (X e) p ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ e)
private theorem curl_moment (E : ColourForm m → ℝ) {C₁ C₂ : ℝ} (hC₂ : 0 ≤ C₂)
    (hK : ∀ (X : ColourForm m) (p : OrientedPlaquette m), curlNorm X p.1 ^ 2 ≤ C₁ * E X)
    (ν : Measure (ColourForm m)) (hν : IsCanonicalGaussian E ν) (p : OrientedPlaquette m)
    (h2 : ∫⁻ X, ENNReal.ofReal (curlNorm X p.1 ^ 2) ∂ν ≤ ENNReal.ofReal C₂) (e : Fin 3) (q : ENNReal) :
    eLpNorm (fun X : ColourForm m => curl (X e) p.1) q ν ≤
      ENNReal.ofReal (Real.sqrt C₂) * eLpNorm id q (gaussianReal 0 1) := by
  have := hν.isProbabilityMeasure
  let f : ColourForm m →ₗ[ℝ] ℝ :=
    { toFun := fun X => curl (X e) p.1
      map_add' := fun X Y => by simp [curl]; ring
      map_smul' := fun c X => by simp [curl]; ring }
  have hfm : Measurable f := curl_measurable e p.1
  have hf0 : ∀ x, E x = 0 → f x = 0 := by
    intro x hx
    have h := hK x p
    rw [hx, mul_zero] at h
    have h1 := curl_sq_le x p.1 e
    have h3 : curl (x e) p.1 ^ 2 ≤ 0 := h1.trans h
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm h3 (sq_nonneg _))
  have hlaw := hν.map_eq f hf0
  set v := (gaussianVariance E f).toNNReal with hvd
  have hv : (v : ℝ) ≤ C₂ := by
    have h3 : ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂(gaussianReal 0 v) ≤ ENNReal.ofReal C₂ := by
      have hmS : Measurable (fun z : ℝ => ENNReal.ofReal (z ^ 2)) :=
        ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2)
      rw [← hlaw, lintegral_map hmS hfm]
      exact (lintegral_mono fun X => ENNReal.ofReal_le_ofReal (curl_sq_le X p.1 e)).trans h2
    have hmem : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) := by
      simpa using memLp_id_gaussianReal (μ := 0) (v := v) 2
    have h4 : ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂(gaussianReal 0 v) = ENNReal.ofReal v := by
      have hi : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v) := hmem.integrable_sq
      rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun z => sq_nonneg z)]
      congr 1
      have h5 := variance_fun_id_gaussianReal (μ := 0) (v := v)
      rw [variance_eq_integral measurable_id'.aemeasurable] at h5
      simpa using h5
    rwa [h4, ENNReal.ofReal_le_ofReal_iff hC₂] at h3
  calc eLpNorm (fun X : ColourForm m => curl (X e) p.1) q ν = eLpNorm id q (ν.map f) :=
        (eLpNorm_map_measure measurable_id.aestronglyMeasurable hfm.aemeasurable).symm
    _ = eLpNorm id q (gaussianReal 0 v) := by rw [hlaw]
    _ ≤ ENNReal.ofReal (Real.sqrt v) * eLpNorm id q (gaussianReal 0 1) := gaussian_eLpNorm_le q v
    _ ≤ _ := by
      gcongr
private theorem curvNorm_of_field {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {Xu : Ω → ColourForm m}
    (hXu : Measurable Xu) (ω : TorusPlaquette m → ℝ) (hω : ∀ p, ω p ≤ 1) (E : ColourForm m → ℝ) {C₁ C₂ : ℝ}
    (hC₂ : 0 ≤ C₂)
    (hK : ∀ (X : ColourForm m) (p : OrientedPlaquette m), curlNorm X p.1 ^ 2 ≤ C₁ * E X)
    (hν : IsCanonicalGaussian E (μ.map Xu))
    (h2 : ∀ p : OrientedPlaquette m, ∫⁻ w, ENNReal.ofReal (curlNorm (Xu w) p.1 ^ 2) ∂μ ≤ ENNReal.ofReal C₂)
    {q : ENNReal} (hq : 1 ≤ q) :
    weightedCurvatureNorm μ ω q Xu ≤ 3 * (ENNReal.ofReal (Real.sqrt C₂) * eLpNorm id q (gaussianReal 0 1)) := by
  unfold weightedCurvatureNorm
  refine iSup_le fun p => ?_
  have hone : ENNReal.ofReal (ω p.1) ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal (hω p.1)
  have hm : ∀ e : Fin 3, Measurable (fun w => curl (Xu w e) p.1) := fun e => (curl_measurable e p.1).comp hXu
  have hpt : ∀ X : ColourForm m, curlNorm X p.1 ≤ ∑ e : Fin 3, |curl (X e) p.1| := by
    intro X
    rw [curlNorm, Fin.sum_univ_three, Fin.sum_univ_three]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have a0 := abs_nonneg (curl (X 0) p.1)
    have a1 := abs_nonneg (curl (X 1) p.1)
    have a2 := abs_nonneg (curl (X 2) p.1)
    have s0 := sq_abs (curl (X 0) p.1)
    have s1 := sq_abs (curl (X 1) p.1)
    have s2 := sq_abs (curl (X 2) p.1)
    nlinarith [mul_nonneg a0 a1, mul_nonneg a0 a2, mul_nonneg a1 a2]
  have h1 : eLpNorm (fun w => curlNorm (Xu w) p.1) q μ ≤
      ∑ e : Fin 3, eLpNorm (fun w => |curl (Xu w e) p.1|) q μ := by
    refine le_trans (eLpNorm_mono_real (g := ∑ e : Fin 3, fun w => |curl (Xu w e) p.1|) fun w => ?_)
      (eLpNorm_sum_le (fun e _ => (hm e).abs.aestronglyMeasurable) hq)
    rw [Real.norm_of_nonneg (curlNorm_nonneg _ _), Finset.sum_apply]
    exact hpt _
  have h3 : ∀ e : Fin 3, eLpNorm (fun w => |curl (Xu w e) p.1|) q μ ≤
      ENNReal.ofReal (Real.sqrt C₂) * eLpNorm id q (gaussianReal 0 1) := by
    intro e
    have e1 : eLpNorm (fun w => |curl (Xu w e) p.1|) q μ = eLpNorm (fun w => curl (Xu w e) p.1) q μ :=
      eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun w => by simp)
    rw [e1]
    have e2 : eLpNorm (fun X : ColourForm m => curl (X e) p.1) q (μ.map Xu) =
        eLpNorm (fun w => curl (Xu w e) p.1) q μ :=
      eLpNorm_map_measure (curl_measurable e p.1).aestronglyMeasurable hXu.aemeasurable
    rw [← e2]
    refine curl_moment E hC₂ hK _ hν p ?_ e q
    have hmS : Measurable (fun X : ColourForm m => ENNReal.ofReal (curlNorm X p.1 ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((curlNorm_measurable p.1).pow_const 2)
    rw [lintegral_map hmS hXu]
    exact h2 p
  calc ENNReal.ofReal (ω p.1) * eLpNorm (fun w => curlNorm (Xu w) p.1) q μ
      ≤ 1 * ∑ _e : Fin 3, ENNReal.ofReal (Real.sqrt C₂) * eLpNorm id q (gaussianReal 0 1) := by
        gcongr
        exact h1.trans (Finset.sum_le_sum fun e _ => h3 e)
    _ = _ := by simp
end Moments
section Conditional
private theorem mean_against_condExp {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g f : Ω → ℝ) (p₀ : ℝ) (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (hae : g =ᵐ[μ] μ[f | m]) (bound : ENNReal)
    (hb : ∫⁻ w, ENNReal.ofReal |g w - p₀| ∂μ ≤ bound) : ENNReal.ofReal |p₀ - ∫ w, f w ∂μ| ≤ bound := by
  have hint : Integrable g μ := (integrable_condExp).congr hae.symm
  have e1 : ∫ w, g w ∂μ = ∫ w, f w ∂μ := (integral_congr_ae hae).trans (integral_condExp hm)
  have e2 : p₀ - ∫ w, f w ∂μ = ∫ w, (p₀ - g w) ∂μ := by
    rw [integral_sub (integrable_const _) hint, e1]
    simp
  rw [e2, ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_trans (le_of_eq ?_) hb)
  refine lintegral_congr fun w => ?_
  rw [Real.enorm_eq_ofReal_abs, abs_sub_comm]
end Conditional
section Parameters
private theorem forAllParameters_and {P Q : MomentParameters → Prop} (hP : ForAllParameters P)
    (hQ : ForAllParameters Q) : ForAllParameters fun Λ => P Λ ∧ Q Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_mono {P Q : MomentParameters → Prop} (h : ∀ Λ, P Λ → Q Λ)
    (hP : ForAllParameters P) : ForAllParameters Q := by apply _root_.YangMills.SharedProofs.p432 <;> assumption
private theorem forAllParameters_facts :
    ForAllParameters fun Λ => Λ.table.Admissible ∧ 1 ≤ Λ.floor ∧ 1 ≤ Λ.k := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hD _ _ _ _ Kr _
  exact ⟨1, fun y hy _ _ g _ _ k _ h2 _ R d _ => ⟨hD, hy, by show 1 ≤ k; omega⟩⟩
end Parameters
section Assembly
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem supportForm_bound {c CQ : ℝ} (hcQ : CQ ≤ c)
    (hQ3 : ∀ (i : Fin Λ.k) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      (X X' : Ω → ColourForm (S.levelSide S.lastSeparated)) (q : ℝ), 1 ≤ q →
      Measurable X → Measurable X' →
      eLpNorm (fun e => colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i) (X e) (X' e))
          (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (CQ * (S.range : ℝ) ^ 4) *
          weightedCurvatureNorm μ (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated))
            (ENNReal.ofReal (2 * q)) X *
          weightedCurvatureNorm μ (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated))
            (ENNReal.ofReal (2 * q)) X')
    {m : ℕ} [NeZero m] (hm : m = S.levelSide S.lastSeparated) (B : Finset (Fin Λ.k))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    ∀ i ∈ B, ∀ X X' : Ω → ColourForm m, Measurable X → Measurable X' →
      eLpNorm (fun w => colourEval (S.supportForm S.lastSeparated m i) (X w) (X' w)) (B.card : ENNReal) P ≤
        ENNReal.ofReal (c * (S.range : ℝ) ^ 4) *
          weightedCurvatureNorm P (S.distanceWeight S.lastSeparated m) (8 * (Λ.k : ENNReal)) X *
          weightedCurvatureNorm P (S.distanceWeight S.lastSeparated m) (8 * (Λ.k : ENNReal)) X' := by
  subst hm
  intro i hi X X' hX hX'
  have hb : 1 ≤ B.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hbk : B.card ≤ Λ.k := by simpa using Finset.card_le_univ B
  have h := hQ3 i Ω P X X' (B.card : ℝ) (by exact_mod_cast hb) hX hX'
  rw [ENNReal.ofReal_natCast] at h
  refine h.trans ?_
  have hq : ENNReal.ofReal (2 * (B.card : ℝ)) ≤ 8 * (Λ.k : ENNReal) := by
    have : (2 * (B.card : ℝ)) = ((2 * B.card : ℕ) : ℝ) := by push_cast; ring
    rw [this, ENNReal.ofReal_natCast]
    have h8 : ((2 * B.card : ℕ) : ENNReal) ≤ ((8 * Λ.k : ℕ) : ENNReal) := by
      exact_mod_cast (by omega : 2 * B.card ≤ 8 * Λ.k)
    simpa using h8
  have hr : ENNReal.ofReal (CQ * (S.range : ℝ) ^ 4) ≤ ENNReal.ofReal (c * (S.range : ℝ) ^ 4) := by
    gcongr
  exact mul_le_mul' (mul_le_mul' hr (curvNorm_exponent_mono P _ hq hX)) (curvNorm_exponent_mono P _ hq hX')
private theorem core_bounds (hD : Λ.table.Admissible) (hx : 0 < S.scaleCoupling) (hk : 1 ≤ Λ.k) {CQ θ CM : ℝ}
    (hQ3 : ∀ (i : Fin Λ.k) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      (X X' : Ω → ColourForm (S.levelSide S.lastSeparated)) (q : ℝ), 1 ≤ q →
      Measurable X → Measurable X' →
      eLpNorm (fun e => colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i) (X e) (X' e))
          (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (CQ * (S.range : ℝ) ^ 4) *
          weightedCurvatureNorm μ (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated))
            (ENNReal.ofReal (2 * q)) X *
          weightedCurvatureNorm μ (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated))
            (ENNReal.ofReal (2 * q)) X')
    (hθ₀ : 0 ≤ θ) (hθ : θ ≤ 2⁻¹ ^ 10 * (Λ.stepParams.side : ℝ) ^ (-(1 / 4) : ℝ))
    (hC : ∀ (d n : ℕ) [NeZero n], 64 ≤ n → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      (X : Ω → ColourForm n) (q : ENNReal), 1 ≤ q → Measurable X →
      weightedCurvatureNorm μ (S.distanceWeight S.lastSeparated (fineSide Λ.stepParams.side d n)) q
        (fun e => descend (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n (X e)) ≤
        ENNReal.ofReal (θ ^ d) * weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) q X)
    (hM : ∀ (d n : ℕ) [NeZero n], S.lastSeparated + d ≤ S.data.windowLevel →
      n = S.levelSide (S.lastSeparated + d) →
      weightedCurvatureNorm (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n)
        (fun _ => 1) (8 * (Λ.k : ENNReal))
        (descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated 1 d n 0) ≤ ENNReal.ofReal CM)
    {d n : ℕ} [NeZero n] (hd : S.lastSeparated + d ≤ S.data.windowLevel)
    (hn : n = S.levelSide (S.lastSeparated + d)) (B : Finset (Fin Λ.k))
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {A A' : Ω → ColourForm n}
    (hA : Measurable A) (hA' : Measurable A') :
    ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w)| ∂μ ≤
        ENNReal.ofReal ((Λ.k : ℝ) * (1 + 2 * max CQ 0) ^ Λ.k * (max 1 CM) ^ (2 * Λ.k) *
            (S.range : ℝ) ^ (4 * B.card)) *
          (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A +
            weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A')) ^
            (2 * B.card) ∧
    ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w) - S.formProductMean d n B 0| ∂μ ≤
        ENNReal.ofReal ((Λ.k : ℝ) * (1 + 2 * max CQ 0) ^ Λ.k * (max 1 CM) ^ (2 * Λ.k) *
            (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(d : ℝ) / 4)) *
          (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A +
            weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A')) ^
            (2 * B.card) ∧
    ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w) - S.formProductMean d n B (A' w)| ∂μ ≤
        ENNReal.ofReal ((Λ.k : ℝ) * (1 + 2 * max CQ 0) ^ Λ.k * (max 1 CM) ^ (2 * Λ.k) *
            (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal))
            (fun w => A w - A' w) *
          (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
            (weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A +
              weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A')) ^
            (2 * B.card - 1) := by
  have hbk : B.card ≤ Λ.k := by simpa using Finset.card_le_univ B
  obtain ⟨h₁, h₂⟩ := real_constants hk (le_max_right CQ 0) (le_max_left 1 CM) hbk
  have hL : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Λ.stepParams.side)
  have hLq : (Λ.stepParams.side : ℝ) ^ (-(1 / 4) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num)
  have hθL : θ ≤ (Λ.stepParams.side : ℝ) ^ (-(1 / 4) : ℝ) := by
    refine hθ.trans ?_
    have : (2⁻¹ : ℝ) ^ 10 ≤ 1 := by norm_num
    nlinarith
  have hth : ENNReal.ofReal (θ ^ d) ≤ 1 := by
    have : θ ^ d ≤ 1 := pow_le_one₀ hθ₀ (hθL.trans hLq)
    simpa using ENNReal.ofReal_le_ofReal this
  have hthL : ENNReal.ofReal (θ ^ d) ≤ ENNReal.ofReal ((Λ.stepParams.side : ℝ) ^ (-(d : ℝ) / 4)) := by
    refine ENNReal.ofReal_le_ofReal ((pow_le_pow_left₀ hθ₀ hθL d).trans (le_of_eq ?_))
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  have hq1 : (1 : ENNReal) ≤ 8 * (Λ.k : ENNReal) := by
    have : ((1 : ℕ) : ENNReal) ≤ ((8 * Λ.k : ℕ) : ENNReal) := by exact_mod_cast (by omega : 1 ≤ 8 * Λ.k)
    simpa using this
  have hm : fineSide Λ.stepParams.side d n = S.levelSide S.lastSeparated := by
    subst hn
    exact side_below S hd
  have h64 : 64 ≤ n := hn ▸ side_large S hD _
  have hcK : ENNReal.ofReal CM ≤ ENNReal.ofReal (max 1 CM) := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hC₀ : 0 ≤ (Λ.k : ℝ) * (1 + 2 * max CQ 0) ^ Λ.k * (max 1 CM) ^ (2 * Λ.k) := by
    positivity
  exact three_bounds S hx B hq1 (S.distanceWeight S.lastSeparated _) (S.distanceWeight (S.lastSeparated + d) n)
    (le_max_right _ _) (le_max_left _ _)
    h₁ h₂ hC₀ hth hthL hcK (fun Ω _ P _ => supportForm_bound S (le_max_left CQ 0) hQ3 hm B Ω P)
    ((curvNorm_weight_mono _ (fun p => distanceWeight_le_one S hD _ _ p) _ _).trans (hM d n hd hn)) μ
    (fun X hX => hC d n h64 Ω μ X _ hq1 hX) hA hA'
private theorem colourEval_scale {m : ℕ} [NeZero m] (q : BondBilinear m) (c : ℝ) (X : ColourForm m) :
    colourEval q (fun e b => c * X e b) (fun e b => c * X e b) = c * c * colourEval q X X := by
  simp only [colourEval, bilinearEval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  ring
private theorem half_formProduct (hx : 0 < S.scaleCoupling) {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂] (hm : m₁ = m₂)
    (B : Finset (Fin Λ.k)) (Y₁ : LevelChain Λ.stepParams.side S.lastSeparated m₁)
    (Y₂ : LevelChain Λ.stepParams.side S.lastSeparated m₂) (h : HEq Y₁ Y₂) :
    ∏ i ∈ B, (1 / 2) * colourEval (S.supportForm S.lastSeparated m₁ i)
        (chainTop S.lastSeparated m₁ Y₁) (chainTop S.lastSeparated m₁ Y₁) =
      S.formProduct S.lastSeparated m₂ B
        (fun c b => S.scaleCoupling ^ (-(1 / 2) : ℝ) * chainTop S.lastSeparated m₂ Y₂ c b) := by
  subst hm
  obtain rfl := eq_of_heq h
  simp only [MomentPoint.formProduct]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [colourEval_scale, ← Real.rpow_add hx]
  have : (-(1 / 2) + -(1 / 2) : ℝ) = -1 := by norm_num
  rw [this, Real.rpow_neg_one]
  field_simp
private theorem fineSide_add (L N e n : ℕ) : fineSide L (N + e) n = fineSide L N (fineSide L e n) := by
  rw [fineSide_eq, fineSide_eq, fineSide_eq, pow_add]
  ring
private theorem chain_bound (hx : 0 < S.scaleCoupling) {C₀ G₀ : ℝ} (hC₀ : 0 ≤ C₀) (hG : 0 ≤ G₀)
    (hcore : ∀ (N n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)), S.lastSeparated + N ≤ S.data.windowLevel →
      n = S.levelSide (S.lastSeparated + N) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → ColourForm n),
      Measurable A →
      ∫⁻ w, ENNReal.ofReal |S.formProductMean N n B (A w) - S.formProductMean N n B 0| ∂μ ≤
        ENNReal.ofReal (C₀ * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(N : ℝ) / 4)) *
          (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + N) n) (8 * (Λ.k : ENNReal)) A +
            weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + N) n) (8 * (Λ.k : ENNReal))
              (fun _ => 0))) ^ (2 * B.card))
    (hcond : ∀ e d : ℕ, S.lastSeparated + e + d = S.data.windowLevel →
      ∀ μ : Measure (LevelChain Λ.stepParams.side (S.lastSeparated + e + d) (S.data.period Λ.stepParams.side)),
      IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling (S.lastSeparated + e + d)
        (S.data.period Λ.stepParams.side)) μ → ∀ B : Finset (Fin Λ.k),
      (fun X => S.formProductMean e (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side)) B
          (fun c b => S.scaleCoupling ^ (-(1 / 2) : ℝ) * chainTop (S.lastSeparated + e) _
            (chainDescend (S.lastSeparated + e) d (S.data.period Λ.stepParams.side) X) c b)) =ᵐ[μ]
        μ[fun X => S.formProduct S.lastSeparated _ B (fun c b => S.scaleCoupling ^ (-(1 / 2) : ℝ) *
            chainTop S.lastSeparated _ (chainDescend S.lastSeparated e _
              (chainDescend (S.lastSeparated + e) d (S.data.period Λ.stepParams.side) X)) c b) |
          MeasurableSpace.comap (fun X (c : Fin 3)
              (p : TorusPlaquette (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))) =>
            curl (chainTop (S.lastSeparated + e) _
              (chainDescend (S.lastSeparated + e) d (S.data.period Λ.stepParams.side) X) c) p) inferInstance])
    (hmom : ∀ u d : ℕ, u + d = S.data.windowLevel →
      ∀ μ : Measure (LevelChain Λ.stepParams.side (u + d) (S.data.period Λ.stepParams.side)),
      IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling (u + d) (S.data.period Λ.stepParams.side)) μ →
      weightedCurvatureNorm μ (S.distanceWeight u (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side)))
        (8 * (Λ.k : ENNReal))
        (fun X => chainTop u _ (chainDescend u d (S.data.period Λ.stepParams.side) X)) ≤ ENNReal.ofReal G₀)
    (N d n : ℕ) [NeZero n] (hK : S.lastSeparated + d = S.data.windowLevel) (hN : N ≤ d)
    (hn : n = S.levelSide (S.lastSeparated + N))
    (μ : Measure (LevelChain Λ.stepParams.side (S.lastSeparated + d) (S.data.period Λ.stepParams.side)))
    (hμ : IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling (S.lastSeparated + d)
      (S.data.period Λ.stepParams.side)) μ) (B : Finset (Fin Λ.k)) :
    |S.formProductMean N n B 0 - ∫ X, ∏ i ∈ B, S.halfForm d (S.data.period Λ.stepParams.side) i X ∂μ| ≤
      C₀ * (1 + G₀) ^ (2 * B.card) * (S.range : ℝ) ^ (4 * B.card) *
        (Λ.stepParams.side : ℝ) ^ (-(N : ℝ) / 4) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = N + e := ⟨d - N, by omega⟩
  have hK' : S.lastSeparated + N + e = S.data.windowLevel := by omega
  have hnn : n = fineSide Λ.stepParams.side e (S.data.period Λ.stepParams.side) := hn.trans (side_top S hK')
  subst hnn
  obtain ⟨μ₂, hμ₂, hint⟩ := chain_transport (L := Λ.stepParams.side) Λ.stepParams.coupling
    (by omega : S.lastSeparated + (N + e) = S.lastSeparated + N + e) μ hμ
  have := hμ₂.isProbabilityMeasure
  have hf : ∫ X, ∏ i ∈ B, S.halfForm (N + e) (S.data.period Λ.stepParams.side) i X ∂μ =
      ∫ X, S.formProduct S.lastSeparated _ B (fun c b => S.scaleCoupling ^ (-(1 / 2) : ℝ) *
          chainTop S.lastSeparated _ (chainDescend S.lastSeparated N _
            (chainDescend (S.lastSeparated + N) e (S.data.period Λ.stepParams.side) X)) c b) ∂μ₂ :=
    hint _ _ fun X₁ X₂ h => half_formProduct S hx (fineSide_add _ _ _ _) B _ _
      (chainDescend_assoc S.lastSeparated N e _ X₁ X₂ h)
  rw [hf]
  have hae := hcond N e hK' μ₂ hμ₂ B
  have hXu : Measurable (fun X : LevelChain Λ.stepParams.side (S.lastSeparated + N + e)
      (S.data.period Λ.stepParams.side) =>
      chainTop (S.lastSeparated + N) (fineSide Λ.stepParams.side e (S.data.period Λ.stepParams.side))
        (chainDescend (S.lastSeparated + N) e (S.data.period Λ.stepParams.side) X)) :=
    (chainTop_measurable (L := Λ.stepParams.side) (S.lastSeparated + N) _).comp
      (chainDescend_measurable (L := Λ.stepParams.side) (S.lastSeparated + N) e _)
  have hAG : Measurable (fun X : LevelChain Λ.stepParams.side (S.lastSeparated + N + e)
      (S.data.period Λ.stepParams.side) => (fun c b => S.scaleCoupling ^ (-(1 / 2) : ℝ) *
      chainTop (S.lastSeparated + N) _ (chainDescend (S.lastSeparated + N) e (S.data.period Λ.stepParams.side) X) c b :
        ColourForm (fineSide Λ.stepParams.side e (S.data.period Λ.stepParams.side)))) :=
    measurable_pi_lambda _ fun c => measurable_pi_lambda _ fun b =>
      ((proj_measurable c b).comp hXu).const_mul _
  have hm : MeasurableSpace.comap (fun (X : LevelChain Λ.stepParams.side (S.lastSeparated + N + e)
        (S.data.period Λ.stepParams.side)) (c : Fin 3)
      (p : TorusPlaquette (fineSide Λ.stepParams.side e (S.data.period Λ.stepParams.side))) =>
      curl (chainTop (S.lastSeparated + N) _
        (chainDescend (S.lastSeparated + N) e (S.data.period Λ.stepParams.side) X) c) p)
        (inferInstance : MeasurableSpace
          (Fin 3 → TorusPlaquette (fineSide Λ.stepParams.side e (S.data.period Λ.stepParams.side)) → ℝ)) ≤
      (inferInstance : MeasurableSpace
        (LevelChain Λ.stepParams.side (S.lastSeparated + N + e) (S.data.period Λ.stepParams.side))) :=
    Measurable.comap_le (measurable_pi_lambda _ fun c => measurable_pi_lambda _ fun p =>
      (curl_measurable c p).comp hXu)
  have hb := hcore N _ B (by omega) (side_top S hK').symm _ μ₂ _ hAG
  have key := mean_against_condExp μ₂ _ _ (S.formProductMean N _ B 0) _ hm hae _ hb
  set s := ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2))
  have hy : (1 + s * (weightedCurvatureNorm μ₂
        (S.distanceWeight (S.lastSeparated + N) (fineSide Λ.stepParams.side e (S.data.period Λ.stepParams.side)))
        (8 * (Λ.k : ENNReal))
        (fun X c b => S.scaleCoupling ^ (-(1 / 2) : ℝ) * chainTop (S.lastSeparated + N) _
          (chainDescend (S.lastSeparated + N) e (S.data.period Λ.stepParams.side) X) c b) +
      weightedCurvatureNorm μ₂
        (S.distanceWeight (S.lastSeparated + N) (fineSide Λ.stepParams.side e (S.data.period Λ.stepParams.side)))
        (8 * (Λ.k : ENNReal)) (fun _ => 0))) ≤
      ENNReal.ofReal (1 + G₀) := by
    rw [curvNorm_zero, add_zero, ENNReal.ofReal_add zero_le_one hG, ENNReal.ofReal_one]
    gcongr
    calc s * _ ≤ s * (ENNReal.ofReal |S.scaleCoupling ^ (-(1 / 2) : ℝ)| *
            weightedCurvatureNorm μ₂ (S.distanceWeight (S.lastSeparated + N)
              (fineSide Λ.stepParams.side e (S.data.period Λ.stepParams.side))) (8 * (Λ.k : ENNReal))
              (fun X => chainTop (S.lastSeparated + N) _
                (chainDescend (S.lastSeparated + N) e (S.data.period Λ.stepParams.side) X))) := by
          gcongr
          exact curvNorm_const_mul_le μ₂ _ _ _ _
      _ = (s * ENNReal.ofReal |S.scaleCoupling ^ (-(1 / 2) : ℝ)|) *
            weightedCurvatureNorm μ₂ (S.distanceWeight (S.lastSeparated + N)
              (fineSide Λ.stepParams.side e (S.data.period Λ.stepParams.side))) (8 * (Λ.k : ENNReal))
              (fun X => chainTop (S.lastSeparated + N) _
                (chainDescend (S.lastSeparated + N) e (S.data.period Λ.stepParams.side) X)) := by ring
      _ ≤ ENNReal.ofReal G₀ := by
          rw [root_mul_inverse S hx, one_mul]
          exact hmom (S.lastSeparated + N) e hK' μ₂ hμ₂
  have hL0 : 0 ≤ (Λ.stepParams.side : ℝ) ^ (-(N : ℝ) / 4) := by positivity
  have hT : 0 ≤ C₀ * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(N : ℝ) / 4) := by positivity
  have fin := key.trans (mul_le_mul' le_rfl (pow_le_pow_left' hy (2 * B.card)))
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hT,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at fin
  refine fin.trans (le_of_eq ?_)
  ring
end Assembly
theorem formMeansAtWeightStatement_holds (hW : scaleWindowStatement) (hQ : supportFormCurvatureKernelStatement)
    (hC : weightContractionStatement) (hM : formMeansStatement)
    (hG : gaussianChainCoordinatesStatement) : formMeansAtWeightStatement := by
  unfold scaleWindowStatement ForAllPoints at hW
  unfold supportFormCurvatureKernelStatement ForAllPoints at hQ
  unfold weightContractionStatement ForAllPoints at hC
  unfold formMeansStatement ForAllPoints at hM
  unfold gaussianChainCoordinatesStatement ForAllPoints at hG
  have h := forAllParameters_and forAllParameters_facts
    (forAllParameters_and hW (forAllParameters_and hQ (forAllParameters_and hC (forAllParameters_and hM hG))))
  unfold formMeansAtWeightStatement ForAllPoints
  refine forAllParameters_mono ?_ h
  rintro Λ ⟨⟨hD, hy, hk⟩, ⟨CW, _, XW, _, hXW, hWS⟩, ⟨CQ, _, _, _, _, hQS⟩, ⟨CC, _, _, _, _, hCS⟩,
    ⟨CM, _, _, _, _, hMS⟩, ⟨CG, _, _, _, _, hGS⟩⟩
  set C₂ := max (CG 0) 0 with hC₂d
  have hC₂ : 0 ≤ C₂ := le_max_right _ _
  set gq := eLpNorm id (8 * (Λ.k : ENNReal)) (gaussianReal 0 1) with hgq
  have hgfin : gq ≠ ⊤ := by
    have h8 := memLp_id_gaussianReal (μ := 0) (v := 1) (8 * (Λ.k : NNReal))
    have e : ((8 * (Λ.k : NNReal) : NNReal) : ENNReal) = 8 * (Λ.k : ENNReal) := by
      push_cast
      rfl
    rw [e] at h8
    exact h8.eLpNorm_lt_top.ne
  set G₀ := 3 * (Real.sqrt C₂ * gq.toReal) with hG₀
  have hG₀0 : 0 ≤ G₀ := by positivity
  set C₀ := (Λ.k : ℝ) * (1 + 2 * max (CQ 0) 0) ^ Λ.k * (max 1 (CM (8 * Λ.k))) ^ (2 * Λ.k) with hC₀d
  have hC₀ : 0 ≤ C₀ := by
    have h1 : 0 ≤ max (CQ 0) 0 := le_max_right _ _
    have h2 : (0 : ℝ) ≤ max 1 (CM (8 * Λ.k)) := zero_le_one.trans (le_max_left _ _)
    positivity
  obtain ⟨C, hC0, hC1⟩ : ∃ C : ℕ → ℝ, C 0 = C₀ ∧ C 1 = C₀ * (1 + G₀) ^ (2 * Λ.k) :=
    ⟨fun i => if i = 0 then C₀ else C₀ * (1 + G₀) ^ (2 * Λ.k), by simp, by simp⟩
  refine ⟨C, 1, max XW Λ.floor, one_pos, le_max_right _ _, fun S hX => ?_⟩
  have hxs : 1 ≤ S.scaleCoupling := hy.trans ((le_max_right _ _).trans hX)
  have hx : 0 < S.scaleCoupling := by linarith
  obtain ⟨_, _, _, _, _, hwin, _⟩ := hWS S ((le_max_left _ _).trans hX)
  obtain ⟨hθ₀, hθ, _, _, _, _, hlast⟩ := hCS S
  obtain ⟨hξ, _, _, _, _, hcond⟩ := hMS S
  have hL0 : 0 ≤ (Λ.stepParams.side : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
  have hQ3 : ∀ (i : Fin Λ.k) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      (X X' : Ω → ColourForm (S.levelSide S.lastSeparated)) (q : ℝ), 1 ≤ q →
      Measurable X → Measurable X' →
      eLpNorm (fun e => colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i) (X e) (X' e))
          (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (CQ 0 * (S.range : ℝ) ^ 4) *
          weightedCurvatureNorm μ (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated))
            (ENNReal.ofReal (2 * q)) X *
          weightedCurvatureNorm μ (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated))
            (ENNReal.ofReal (2 * q)) X' := by
    intro i
    obtain ⟨_, _, _, h3⟩ := hQS S i
    exact h3
  have hξ' : ∀ (d n : ℕ) [NeZero n], S.lastSeparated + d ≤ S.data.windowLevel →
      n = S.levelSide (S.lastSeparated + d) →
      weightedCurvatureNorm (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n)
        (fun _ => 1) (8 * (Λ.k : ENNReal))
        (descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated 1 d n 0) ≤
        ENNReal.ofReal (CM (8 * Λ.k)) := by
    intro d n _ hd hn
    have h1 := hξ d n hd hn (8 * Λ.k) (by omega)
    have e : ((8 * Λ.k : ℕ) : ENNReal) = 8 * (Λ.k : ENNReal) := by
      push_cast
      rfl
    rwa [e] at h1
  have hcore := fun (d n : ℕ) [NeZero n] (hd : S.lastSeparated + d ≤ S.data.windowLevel)
      (hn : n = S.levelSide (S.lastSeparated + d)) (B : Finset (Fin Λ.k))
      (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A A' : Ω → ColourForm n)
      (hA : Measurable A) (hA' : Measurable A') =>
    core_bounds S hD hx hk hQ3 (mul_nonneg hθ₀ hL0) hθ hlast hξ' hd hn B μ hA hA'
  refine ⟨?_, ?_⟩
  · intro d n _ hd hn B Ω _ μ _ A A' hA hA'
    rw [hC0]
    exact hcore d n (by omega) hn B Ω μ A A' hA hA'
  · intro N d n _ hK hN hn μ hμ B
    have hmom : ∀ u d : ℕ, u + d = S.data.windowLevel →
        ∀ μ : Measure (LevelChain Λ.stepParams.side (u + d) (S.data.period Λ.stepParams.side)),
        IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling (u + d) (S.data.period Λ.stepParams.side)) μ →
        weightedCurvatureNorm μ (S.distanceWeight u (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side)))
          (8 * (Λ.k : ENNReal))
          (fun X => chainTop u _ (chainDescend u d (S.data.period Λ.stepParams.side) X)) ≤ ENNReal.ofReal G₀ := by
      intro u d hud μ hμ
      obtain ⟨hKin, hrest⟩ := hGS S u d hud
      obtain ⟨_, hcan, hsq⟩ := hrest μ hμ
      have hq1 : (1 : ENNReal) ≤ 8 * (Λ.k : ENNReal) := by
        have : ((1 : ℕ) : ENNReal) ≤ ((8 * Λ.k : ℕ) : ENNReal) := by exact_mod_cast (by omega : 1 ≤ 8 * Λ.k)
        simpa using this
      refine (curvNorm_of_field μ ((chainTop_measurable (L := Λ.stepParams.side) u _).comp
          (chainDescend_measurable (L := Λ.stepParams.side) u d _)) _
        (fun p => distanceWeight_le_one S hD _ _ p) _ hC₂ hKin hcan
        (fun p => (hsq p).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) hq1).trans (le_of_eq ?_)
      rw [hG₀, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hgfin]
      simp only [ENNReal.ofReal_ofNat]
      rfl
    have hc := chain_bound S hx hC₀ hG₀0
      (fun N n _ B hd hn Ω _ μ _ A hA => (hcore N n hd hn B Ω μ A (fun _ => 0) hA measurable_const).2.1)
      hcond hmom N d n hK hN hn μ hμ B
    rw [hC1]
    refine hc.trans ?_
    have hbk : B.card ≤ Λ.k := by simpa using Finset.card_le_univ B
    have hp : (1 + G₀) ^ (2 * B.card) ≤ (1 + G₀) ^ (2 * Λ.k) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    gcongr
end FormMeansAtWeight
end YangMills.Construction.MomentLaw
end
