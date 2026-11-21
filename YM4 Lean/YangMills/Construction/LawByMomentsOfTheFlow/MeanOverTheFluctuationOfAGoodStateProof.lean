import YangMills.Construction.LawByMomentsOfTheFlow.CarriedCutOfAGoodState
import YangMills.Construction.LawByMomentsOfTheFlow.ColdLawOfAGoodStateProof
import YangMills.Construction.LawByMomentsOfTheFlow.MeanAtTheCutOfAGoodStateProof
import YangMills.Construction.LawByMomentsOfTheFlow.MeanOverTheFluctuationOfAGoodState
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.MomentMethod YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.WeightedResponses YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.ConvexObservables
private theorem forAllParameters_and {P P' : MomentParameters → Prop} (h : ForAllParameters P)
    (h' : ForAllParameters P') : ForAllParameters fun Λ => P Λ ∧ P' Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_mono {P P' : MomentParameters → Prop} (h : ForAllParameters P)
    (f : ∀ Λ, P Λ → P' Λ) : ForAllParameters P' := by apply _root_.YangMills.SharedProofs.p9549 <;> assumption
private theorem forAllParameters_weightRate_pos : ForAllParameters fun Λ => 0 < Λ.stepParams.weightRate := by apply _root_.YangMills.SharedProofs.p57148 <;> assumption
section Forms
variable {m : ℕ} [NeZero m]
private theorem curl_add (A A' : TorusBond m → ℝ) (p : TorusPlaquette m) :
    curl (A + A') p = curl A p + curl A' p := by
  simp only [curl, Pi.add_apply]; ring
private theorem curl_smul (c : ℝ) (A : TorusBond m → ℝ) (p : TorusPlaquette m) :
    curl (c • A) p = c * curl A p := by
  simp only [curl, Pi.smul_apply, smul_eq_mul]; ring
private def curlVector (X : ColourForm m) (p : TorusPlaquette m) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun e => curl (X e) p
private theorem curlNorm_eq_norm (X : ColourForm m) (p : TorusPlaquette m) : curlNorm X p = ‖curlVector X p‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [curlNorm, curlVector, Real.norm_eq_abs, sq_abs]
private theorem curlVector_add (X X' : ColourForm m) (p : TorusPlaquette m) :
    curlVector (X + X') p = curlVector X p + curlVector X' p := by
  ext e
  simp [curlVector, curl_add]
private theorem curlVector_smul (c : ℝ) (X : ColourForm m) (p : TorusPlaquette m) :
    curlVector (c • X) p = c • curlVector X p := by
  ext e
  simp [curlVector, curl_smul]
private theorem curlNorm_add_le (X X' : ColourForm m) (p : TorusPlaquette m) :
    curlNorm (X + X') p ≤ curlNorm X p + curlNorm X' p := by
  simp only [curlNorm_eq_norm, curlVector_add]
  exact norm_add_le _ _
abbrev _root_.YangMills.SharedProofs.p71255 := @curlNorm_add_le
private theorem curlNorm_smul (c : ℝ) (X : ColourForm m) (p : TorusPlaquette m) :
    curlNorm (c • X) p = |c| * curlNorm X p := by
  simp only [curlNorm_eq_norm, curlVector_smul, norm_smul, Real.norm_eq_abs]
abbrev _root_.YangMills.SharedProofs.p47915 := @curlNorm_smul
private theorem curlNorm_nonneg (X : ColourForm m) (p : TorusPlaquette m) : 0 ≤ curlNorm X p := Real.sqrt_nonneg _
private theorem continuous_curlNorm (p : TorusPlaquette m) : Continuous fun X : ColourForm m => curlNorm X p := by
  unfold curlNorm curl
  fun_prop
abbrev _root_.YangMills.SharedProofs.p29578 := @continuous_curlNorm
variable {Ω : Type} [MeasurableSpace Ω]
private theorem weightedCurvatureNorm_const_add_le (P : Measure Ω) [IsProbabilityMeasure P] (ω : TorusPlaquette m → ℝ)
    (hω0 : ∀ p, 0 ≤ ω p) (hω1 : ∀ p, ω p ≤ 1) (q : ENNReal) (hq : 1 ≤ q) (A₀ : ColourForm m) (Y : Ω → ColourForm m)
    (hY : Measurable Y) (a b : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : ∀ p : OrientedPlaquette m, ω p.1 * curlNorm A₀ p.1 ≤ a)
    (hb : ∀ p : OrientedPlaquette m, eLpNorm (fun z => curlNorm (Y z) p.1) q P ≤ ENNReal.ofReal b) :
    weightedCurvatureNorm P ω q (fun z => A₀ + Y z) ≤ ENNReal.ofReal (a + b) := by
  refine iSup_le fun p => ?_
  have hm : Measurable fun z => curlNorm (Y z) p.1 := (continuous_curlNorm p.1).measurable.comp hY
  have h1 : eLpNorm (fun z => curlNorm (A₀ + Y z) p.1) q P ≤
      eLpNorm (fun _ => curlNorm A₀ p.1) q P + eLpNorm (fun z => curlNorm (Y z) p.1) q P := by
    refine le_trans (eLpNorm_mono_real (g := fun z => curlNorm A₀ p.1 + curlNorm (Y z) p.1) fun z => ?_)
      (eLpNorm_add_le aestronglyMeasurable_const hm.aestronglyMeasurable hq)
    rw [Real.norm_eq_abs, abs_of_nonneg (curlNorm_nonneg _ _)]
    exact curlNorm_add_le _ _ _
  have h2 : eLpNorm (fun _ : Ω => curlNorm A₀ p.1) q P ≤ ENNReal.ofReal (curlNorm A₀ p.1) := by
    have := eLpNorm_le_of_ae_bound (μ := P) (p := q) (f := fun _ : Ω => curlNorm A₀ p.1) (C := curlNorm A₀ p.1)
      (Filter.Eventually.of_forall fun _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (curlNorm_nonneg _ _)])
    simpa using this
  have hω := hω0 p.1
  calc ENNReal.ofReal (ω p.1) * eLpNorm (fun z => curlNorm (A₀ + Y z) p.1) q P
      ≤ ENNReal.ofReal (ω p.1) * (ENNReal.ofReal (curlNorm A₀ p.1) + ENNReal.ofReal b) := by
        gcongr
        exact le_trans h1 (add_le_add h2 (hb p))
    _ = ENNReal.ofReal (ω p.1 * curlNorm A₀ p.1) + ENNReal.ofReal (ω p.1 * b) := by
        rw [mul_add, ENNReal.ofReal_mul hω, ENNReal.ofReal_mul hω]
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal b := by
        gcongr
        · exact ha p
        · exact mul_le_of_le_one_left hb0 (hω1 p.1)
    _ = ENNReal.ofReal (a + b) := (ENNReal.ofReal_add ha0 hb0).symm
private theorem eLpNorm_curlNorm_linComb_le (P : Measure Ω) (q : ENNReal) (hq : 1 ≤ q) (Y₁ Y₂ : Ω → ColourForm m)
    (h₁ : Measurable Y₁) (h₂ : Measurable Y₂) (c₁ c₂ b₁ b₂ : ℝ) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (p : TorusPlaquette m)
    (H₁ : eLpNorm (fun z => curlNorm (Y₁ z) p) q P ≤ ENNReal.ofReal b₁)
    (H₂ : eLpNorm (fun z => curlNorm (Y₂ z) p) q P ≤ ENNReal.ofReal b₂) :
    eLpNorm (fun z => curlNorm (c₁ • Y₁ z + c₂ • Y₂ z) p) q P ≤ ENNReal.ofReal (|c₁| * b₁ + |c₂| * b₂) := by
  have m₁ : Measurable fun z => curlNorm (Y₁ z) p := (continuous_curlNorm p).measurable.comp h₁
  have m₂ : Measurable fun z => curlNorm (Y₂ z) p := (continuous_curlNorm p).measurable.comp h₂
  have e₁ : eLpNorm (fun z => |c₁| * curlNorm (Y₁ z) p) q P ≤ ENNReal.ofReal (|c₁| * b₁) := by
    have : (fun z => |c₁| * curlNorm (Y₁ z) p) = |c₁| • fun z => curlNorm (Y₁ z) p := rfl
    rw [this, eLpNorm_const_smul, ENNReal.ofReal_mul (abs_nonneg _)]
    refine mul_le_mul' ?_ H₁
    rw [Real.enorm_eq_ofReal (abs_nonneg _)]
  have e₂ : eLpNorm (fun z => |c₂| * curlNorm (Y₂ z) p) q P ≤ ENNReal.ofReal (|c₂| * b₂) := by
    have : (fun z => |c₂| * curlNorm (Y₂ z) p) = |c₂| • fun z => curlNorm (Y₂ z) p := rfl
    rw [this, eLpNorm_const_smul, ENNReal.ofReal_mul (abs_nonneg _)]
    refine mul_le_mul' ?_ H₂
    rw [Real.enorm_eq_ofReal (abs_nonneg _)]
  calc eLpNorm (fun z => curlNorm (c₁ • Y₁ z + c₂ • Y₂ z) p) q P
      ≤ eLpNorm ((fun z => |c₁| * curlNorm (Y₁ z) p) + fun z => |c₂| * curlNorm (Y₂ z) p) q P := by
        refine eLpNorm_mono_real fun z => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (curlNorm_nonneg _ _)]
        refine le_trans (curlNorm_add_le _ _ _) ?_
        rw [curlNorm_smul, curlNorm_smul]
        rfl
    _ ≤ eLpNorm (fun z => |c₁| * curlNorm (Y₁ z) p) q P + eLpNorm (fun z => |c₂| * curlNorm (Y₂ z) p) q P :=
        eLpNorm_add_le (m₁.const_mul _).aestronglyMeasurable (m₂.const_mul _).aestronglyMeasurable hq
    _ ≤ ENNReal.ofReal (|c₁| * b₁) + ENNReal.ofReal (|c₂| * b₂) := add_le_add e₁ e₂
    _ = ENNReal.ofReal (|c₁| * b₁ + |c₂| * b₂) :=
        (ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) hb₁) (mul_nonneg (abs_nonneg _) hb₂)).symm
end Forms
section Chart
variable {L : ℕ} [NeZero L] {u n : ℕ} [NeZero n]
private def chartLinearMap : BondField (ChartBondIndex L u n) →L[ℝ] ColourForm (n * L) :=
  LinearMap.toContinuousLinearMap
    { toFun := chartColourForm
      map_add' := fun k k' => by
        funext e c
        simp only [chartColourForm, extendChart, Pi.add_apply, PiLp.add_apply]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
      map_smul' := fun a k => by
        funext e c
        simp only [chartColourForm, extendChart, Pi.smul_apply, PiLp.smul_apply, RingHom.id_apply, smul_eq_mul,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp }
private theorem chartLinearMap_apply (k : BondField (ChartBondIndex L u n)) : chartLinearMap k = chartColourForm k := rfl
private theorem chartColourForm_fieldOfCoordinates (ζ : StepFluctuation L u n) :
    chartColourForm (fieldOfCoordinates ζ) = extendFluctuation ζ := rfl
end Chart
private theorem eLpNorm_le_of_weightedCurvatureNorm {m : ℕ} [NeZero m] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (q : ENNReal) (X : Ω → ColourForm m) (b : ENNReal) (h : weightedCurvatureNorm P (fun _ => 1) q X ≤ b)
    (pp : OrientedPlaquette m) :
    eLpNorm (fun z => curlNorm (X z) pp.1) q P ≤ b := by
  have h1 := le_iSup (fun p : OrientedPlaquette m => ENNReal.ofReal 1 * eLpNorm (fun z => curlNorm (X z) p.1) q P) pp
  simp only [ENNReal.ofReal_one, one_mul] at h1
  refine le_trans h1 ?_
  simpa [weightedCurvatureNorm] using h
section ChartContinuity
variable {L : ℕ} [NeZero L] {u n : ℕ} [NeZero n]
private theorem continuous_fieldOfCoordinates :
    Continuous (fieldOfCoordinates :
      EuclideanSpace ℝ (Fin 3 × ChartBondIndex L u n) → BondField (ChartBondIndex L u n)) := by
  unfold fieldOfCoordinates
  fun_prop
private theorem fieldOfCoordinates_smul (c : ℝ) (ζ : EuclideanSpace ℝ (Fin 3 × ChartBondIndex L u n)) :
    fieldOfCoordinates (c • ζ) = c • fieldOfCoordinates ζ := by
  funext b
  ext e
  simp [fieldOfCoordinates]
private theorem continuous_extendFluctuation :
    Continuous (extendFluctuation : StepFluctuation L u n → ColourForm (n * L)) :=
  (chartLinearMap (L := L) (u := u) (n := n)).continuous.comp continuous_fieldOfCoordinates
private theorem extendFluctuation_smul (c : ℝ) (ζ : StepFluctuation L u n) :
    extendFluctuation (c • ζ) = c • extendFluctuation ζ := by
  rw [← chartColourForm_fieldOfCoordinates, fieldOfCoordinates_smul, ← chartLinearMap_apply, map_smul,
    chartLinearMap_apply, chartColourForm_fieldOfCoordinates]
end ChartContinuity
section Gaussian
variable (a : ℝ) (L : ℕ) [NeZero L] (u n : ℕ)
private theorem fluctuationCov_posSemidef (x : ℝ) (hx : 0 < x) (hS : (fluctuationCov a L 1 u n).PosSemidef) :
    (fluctuationCov a L x u n).PosSemidef := by
  have hE : fluctuationCov a L x u n = x⁻¹ • fluctuationCov a L 1 u n := by
    ext i j
    simp only [fluctuationCov, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hE]
  exact hS.smul (inv_pos.2 hx).le
open Classical in
private theorem fluctuationGaussian_map_smul (x : ℝ) (hx : 0 < x) (hS : (fluctuationCov a L 1 u n).PosSemidef) :
    (fluctuationGaussian a L 1 u n).map (fun ζ => x ^ (-(1 / 2) : ℝ) • ζ) = fluctuationGaussian a L x u n := by
  have hxi : 0 ≤ x⁻¹ := (inv_pos.2 hx).le
  have hE : fluctuationCov a L x u n = x⁻¹ • fluctuationCov a L 1 u n := by
    ext i j
    simp only [fluctuationCov, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hS' : (fluctuationCov a L x u n).PosSemidef := by
    rw [hE]
    exact hS.smul hxi
  have hc : (x ^ (-(1 / 2) : ℝ)) * (x ^ (-(1 / 2) : ℝ)) = x⁻¹ := by
    rw [← Real.rpow_add hx, ← Real.rpow_neg_one x]
    norm_num
  unfold fluctuationGaussian
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_multivariateGaussian hS', charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have h1 : ∀ v : EuclideanSpace ℝ (Fin 3 × ChartBondIndex L u n),
      Complex.exp ((inner ℝ (x ^ (-(1 / 2) : ℝ) • v) t : ℝ) * Complex.I) =
        Complex.exp ((inner ℝ v (x ^ (-(1 / 2) : ℝ) • t) : ℝ) * Complex.I) := fun v => by
    rw [real_inner_smul_left, real_inner_smul_right]
  simp_rw [h1]
  rw [← charFun_apply, charFun_multivariateGaussian hS, hE]
  congr 1
  simp [Matrix.smul_mulVec, dotProduct_smul, Matrix.mulVec_smul, smul_dotProduct]
  have hc2 : x ^ (-(2⁻¹ : ℝ)) * x ^ (-(2⁻¹ : ℝ)) = x⁻¹ := by
    have e : (-(2⁻¹ : ℝ)) = -(1 / 2) := by norm_num
    rw [e]
    exact hc
  have hc3 : ((x ^ (-(2⁻¹ : ℝ)) : ℝ) : ℂ) * ((x ^ (-(2⁻¹ : ℝ)) : ℝ) : ℂ) = (x : ℂ)⁻¹ := by
    exact_mod_cast hc2
  rw [← mul_assoc, hc3]
end Gaussian
private theorem log_le_two_mul_sqrt (x : ℝ) (hx : 0 < x) : Real.log x ≤ 2 * x ^ ((1 : ℝ) / 2) := by apply _root_.YangMills.SharedProofs.p12056 <;> assumption
private theorem inv_sqrt_sub_le (x x' cn : ℝ) (hx : 1 ≤ x) (hcn : 0 ≤ cn) (h1 : |x' - x| ≤ cn * Real.log x)
    (h2 : cn * Real.log x ≤ x / 2) :
    0 < x' ∧ |x' ^ (-(1 / 2) : ℝ) - x ^ (-(1 / 2) : ℝ)| ≤ 4 * cn * x⁻¹ ∧
      x' ^ (-(1 / 2) : ℝ) ≤ 2 * x ^ (-(1 / 2) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hx' : x / 2 ≤ x' := by
    have := (abs_le.1 (le_trans h1 h2)).1
    linarith
  have hx'0 : 0 < x' := by linarith
  have e1 : ∀ z : ℝ, 0 < z → z ^ (-(1 / 2) : ℝ) = (Real.sqrt z)⁻¹ := fun z hz => by
    rw [Real.rpow_neg hz.le, ← Real.sqrt_eq_rpow]
  rw [e1 x hx0, e1 x' hx'0]
  set h := Real.sqrt x with hh
  set h' := Real.sqrt x' with hh'
  have hsq : h * h = x := Real.mul_self_sqrt hx0.le
  have hsq' : h' * h' = x' := Real.mul_self_sqrt hx'0.le
  have h0 : 0 < h := Real.sqrt_pos.2 hx0
  have h0' : 0 < h' := Real.sqrt_pos.2 hx'0
  have hb : h / 2 ≤ h' := by
    by_contra hc
    push Not at hc
    nlinarith
  have hlog : Real.log x ≤ 2 * h := by
    have := log_le_two_mul_sqrt x hx0
    rwa [← Real.sqrt_eq_rpow] at this
  have hgap : |h - h'| * (h + h') ≤ 2 * cn * h := by
    have e2 : |h - h'| * (h + h') = |x' - x| := by
      have e21 : (h - h') * (h + h') = x - x' := by nlinarith
      rw [abs_sub_comm x' x, ← e21, abs_mul, abs_of_pos (show 0 < h + h' by positivity)]
    rw [e2]
    refine le_trans h1 ?_
    nlinarith
  have hgap' : |h - h'| ≤ 2 * cn := by
    by_contra hc
    push Not at hc
    have : 2 * cn * h < |h - h'| * (h + h') := by
      have := abs_nonneg (h - h')
      nlinarith
    linarith
  refine ⟨hx'0, ?_, ?_⟩
  · have e3 : h'⁻¹ - h⁻¹ = (h - h') / (h * h') := by
      field_simp
    rw [e3, abs_div, abs_of_pos (show 0 < h * h' by positivity), ← hsq, mul_inv]
    rw [div_le_iff₀ (by positivity)]
    have e4 : 4 * cn * (h⁻¹ * h⁻¹) * (h * h') = 4 * cn * h' * h⁻¹ := by
      field_simp
    rw [e4]
    have : 2 * cn ≤ 4 * cn * h' * h⁻¹ := by
      have : h / 2 * h⁻¹ ≤ h' * h⁻¹ := by gcongr
      have e5 : h / 2 * h⁻¹ = 1 / 2 := by field_simp
      rw [e5] at this
      nlinarith
    linarith
  · rw [inv_le_comm₀ h0' (by positivity)]
    have : (2 * h⁻¹)⁻¹ = h / 2 := by field_simp
    rw [this]
    exact hb
private theorem weight_mul_sqrt_exp_le (c rd rr dp z : ℝ) (hc : 0 < c) (hrd : 0 ≤ rd) (hr : 1 ≤ rr) (hdp : 0 ≤ dp)
    (hz : 0 ≤ z) (cr : ℝ) (hcr : rd ≤ cr * rr) :
    (1 + (1 + (dp + 1) + rr) * z) * Real.sqrt (Real.exp (-(c * max 0 (dp - rd)))) ≤
      (4 + cr + 2 / (c / 2)) * rr * (1 + z) := by
  set t := max 0 (dp - rd) with ht
  have hdt : dp ≤ rd + t := by
    have := le_max_right 0 (dp - rd)
    linarith
  have hcr0 : 0 ≤ cr := by
    by_contra hn
    push Not at hn
    nlinarith
  set E := Real.sqrt (Real.exp (-(c * t))) with hE
  have hEe : E = Real.exp (-(c / 2 * t)) := by
    rw [hE, Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _), ← Real.exp_add]
    congr 1
    ring
  have hE0 : 0 < E := by rw [hEe]; exact Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hEe]
    exact Real.exp_le_one_iff.2 (by have : 0 ≤ c / 2 * t := by positivity
                                    linarith)
  set T := 2 / (c / 2) with hT
  have htE : t * E ≤ T := by
    have h1 : c / 2 * t ≤ Real.exp (c / 2 * t) := by
      have := Real.add_one_le_exp (c / 2 * t)
      linarith
    have h2 : c / 2 * t * E ≤ 1 := by
      have e : Real.exp (c / 2 * t) * E = 1 := by
        rw [hEe, ← Real.exp_add]
        simp
      calc c / 2 * t * E ≤ Real.exp (c / 2 * t) * E := by gcongr
        _ = 1 := e
    have hc2 : 0 < c / 2 := by positivity
    have h3 : t * E ≤ 1 / (c / 2) := by
      rw [le_div_iff₀ hc2]
      linarith
    have : 1 / (c / 2) ≤ T := by
      rw [hT]
      gcongr
      norm_num
    linarith
  have hzE : z * E ≤ z := mul_le_of_le_one_right hz hE1
  have h1 : (1 + (1 + (dp + 1) + rr) * z) * E ≤ 1 + (2 + rd + rr) * z + T * z := by
    have a1 : dp * (z * E) ≤ (rd + t) * (z * E) := by gcongr
    have a2 : (rd + t) * (z * E) ≤ rd * z + T * z := by
      have b1 : rd * (z * E) ≤ rd * z := by gcongr
      have b3 : (t * E) * z ≤ T * z := by gcongr
      nlinarith
    have a3 : (2 + rr) * (z * E) ≤ (2 + rr) * z := by gcongr
    nlinarith
  refine le_trans h1 ?_
  have h2 : T * z ≤ T * rr * z := by
    have : T * 1 ≤ T * rr := by gcongr
    nlinarith
  have h3 : 1 + (2 + rd + rr) * z ≤ (4 + cr) * rr * (1 + z) := by
    have c2 : (2 + rd + rr) ≤ (4 + cr) * rr := by nlinarith
    have c3 : (2 + rd + rr) * z ≤ (4 + cr) * rr * z := by gcongr
    nlinarith
  have h4 : 0 ≤ T * rr * 1 := by positivity
  nlinarith
section Core
variable {L : ℕ} [NeZero L] {u n : ℕ} [NeZero n]
private theorem eLpNorm_curlNorm_map_smul_le (γ₁ : Measure (StepFluctuation L u n)) (c cq : ℝ) (hc : 0 < c)
    (q : ENNReal) (pp : OrientedPlaquette (n * L))
    (N2 : eLpNorm (fun ζ => curlNorm (extendFluctuation ζ) pp.1) q γ₁ ≤ ENNReal.ofReal cq) :
    eLpNorm (fun ζ => curlNorm (extendFluctuation ζ) pp.1) q (γ₁.map fun ζ => c • ζ) ≤ ENNReal.ofReal (c * cq) := by
  rw [eLpNorm_map_measure]
  · have e1 : ((fun ζ : StepFluctuation L u n => curlNorm (extendFluctuation ζ) pp.1) ∘ fun ζ => c • ζ) =
        c • fun ζ => curlNorm (extendFluctuation ζ) pp.1 := by
      funext ζ
      simp only [Function.comp, Pi.smul_apply, smul_eq_mul]
      rw [extendFluctuation_smul, curlNorm_smul, abs_of_pos hc]
    rw [e1, eLpNorm_const_smul, ENNReal.ofReal_mul hc.le, Real.enorm_eq_ofReal hc.le]
    exact mul_le_mul' le_rfl N2
  · exact ((continuous_curlNorm pp.1).comp continuous_extendFluctuation).measurable.aestronglyMeasurable
  · exact (measurable_const_smul _).aemeasurable
private theorem weightedCurvatureNorm_rotation_le (μ : Measure (BondField (ChartBondIndex L u n)))
    [IsProbabilityMeasure μ] (γ : Measure (StepFluctuation L u n)) [IsProbabilityMeasure γ]
    (ω : TorusPlaquette (n * L) → ℝ) (hω0 : ∀ p, 0 ≤ ω p) (hω1 : ∀ p, ω p ≤ 1) (q : ENNReal) (hq : 1 ≤ q)
    (A₀ : ColourForm (n * L)) (s b₁ b₂ : ℝ) (hs : 0 ≤ s) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hcar : ∀ pp : OrientedPlaquette (n * L), ω pp.1 * curlNorm A₀ pp.1 ≤ s)
    (N1 : ∀ pp : OrientedPlaquette (n * L),
      eLpNorm (fun k => curlNorm (chartColourForm k) pp.1) q μ ≤ ENNReal.ofReal b₁)
    (N2 : ∀ pp : OrientedPlaquette (n * L),
      eLpNorm (fun ζ => curlNorm (extendFluctuation ζ) pp.1) q γ ≤ ENNReal.ofReal b₂) (θ : ℝ) :
    weightedCurvatureNorm (μ.prod γ) ω q
        (fun z => A₀ + chartColourForm (Real.cos θ • z.1 + Real.sin θ • fieldOfCoordinates z.2)) ≤
      ENNReal.ofReal (s + (b₁ + b₂)) := by
  have hrew : (fun z : BondField (ChartBondIndex L u n) × StepFluctuation L u n =>
      A₀ + chartColourForm (Real.cos θ • z.1 + Real.sin θ • fieldOfCoordinates z.2)) =
      fun z => A₀ + (Real.cos θ • chartColourForm z.1 + Real.sin θ • extendFluctuation z.2) := by
    funext z
    rw [← chartLinearMap_apply, map_add, map_smul, map_smul]
    rfl
  rw [hrew]
  have c₁ : Continuous fun z : BondField (ChartBondIndex L u n) × StepFluctuation L u n => chartColourForm z.1 :=
    (chartLinearMap (L := L) (u := u) (n := n)).continuous.comp continuous_fst
  have c₂ : Continuous fun z : BondField (ChartBondIndex L u n) × StepFluctuation L u n => extendFluctuation z.2 :=
    continuous_extendFluctuation.comp continuous_snd
  have m₁ := c₁.measurable
  have m₂ := c₂.measurable
  have hY : Measurable fun z : BondField (ChartBondIndex L u n) × StepFluctuation L u n =>
      Real.cos θ • chartColourForm z.1 + Real.sin θ • extendFluctuation z.2 :=
    ((c₁.const_smul (Real.cos θ)).add (c₂.const_smul (Real.sin θ))).measurable
  have hcos := Real.abs_cos_le_one θ
  have hsin := Real.abs_sin_le_one θ
  refine le_trans (weightedCurvatureNorm_const_add_le (μ.prod γ) ω hω0 hω1 q hq A₀ _ hY s
    (|Real.cos θ| * b₁ + |Real.sin θ| * b₂) hs (by positivity) hcar fun pp => ?_) (ENNReal.ofReal_le_ofReal ?_)
  · refine eLpNorm_curlNorm_linComb_le _ q hq _ _ m₁ m₂ _ _ b₁ b₂ hb₁ hb₂ pp.1 ?_ ?_
    · have := eLpNorm_comp_measurePreserving (p := q) (g := fun k => curlNorm (chartColourForm k) pp.1)
        (((continuous_curlNorm pp.1).comp
          (chartLinearMap (L := L) (u := u) (n := n)).continuous).measurable.aestronglyMeasurable)
        (measurePreserving_fst (μ := μ) (ν := γ))
      exact le_trans (le_of_eq this) (N1 pp)
    · have := eLpNorm_comp_measurePreserving (p := q) (g := fun ζ => curlNorm (extendFluctuation ζ) pp.1)
        (((continuous_curlNorm pp.1).comp continuous_extendFluctuation).measurable.aestronglyMeasurable)
        (measurePreserving_snd (μ := μ) (ν := γ))
      exact le_trans (le_of_eq this) (N2 pp)
  · nlinarith [mul_le_mul_of_nonneg_right hcos hb₁, mul_le_mul_of_nonneg_right hsin hb₂]
private theorem gaussianComparison_shifted (hK : gaussianComparisonStatement) (ρ : ℝ) (p : ℝ → ℝ)
    (Ψ : BondField (ChartBondIndex L u n) → ℝ) (hρ : 0 < ρ) (hcut : IsCutoff ρ p) (hΨ : ContDiff ℝ 1 Ψ)
    (Gc : Matrix (Fin 3 × ChartBondIndex L u n) (Fin 3 × ChartBondIndex L u n) ℝ) (hGc : Gc.PosSemidef)
    [IsProbabilityMeasure (normalizedBallLaw (cutoffFactor ρ p) Ψ)]
    [IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3 × ChartBondIndex L u n)) Gc)]
    (G₀ : ColourForm (n * L) → ℝ) (hG : ContDiff ℝ 2 G₀) (Cg : ℝ) (kg : ℕ)
    (hgrow : ∀ (A : ColourForm (n * L)) (l : ℕ), l ≤ 2 → ‖iteratedFDeriv ℝ l G₀ A‖ ≤ Cg * (1 + ‖A‖) ^ kg)
    (A₀ : ColourForm (n * L)) (ω : TorusPlaquette (n * L) → ℝ) (q : ENNReal)
    (w : ChartBondIndex L u n → ℝ) (hw : ∀ b, 0 ≤ w b) (α α₀ T hb Db b : ℝ) (hα : 0 ≤ α) (hα₀ : α₀ ≤ α)
    (hT : 0 ≤ T) (hb0 : 0 ≤ hb) (hb1 : 0 ≤ b) (hDb : 1 + hb * b ≤ Db) (m : ℕ) (hDb0 : 0 ≤ Db)
    (hdrift : ∀ j : Fin 3 × ChartBondIndex L u n,
      eLpNorm (fun k => driftCoord Gc p Ψ k j) 2 (normalizedBallLaw (cutoffFactor ρ p) Ψ) ≤
        ENNReal.ofReal (α₀ * w j.2))
    (hslope : ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → ColourForm (n * L)),
      Measurable A →
      ∑ j : Fin 3 × ChartBondIndex L u n, ENNReal.ofReal (w j.2) *
          eLpNorm (fun z => fderiv ℝ G₀ (A z) (chartColourForm (unitVariation j))) 2 μ ≤
        ENNReal.ofReal T * (1 + ENNReal.ofReal hb * weightedCurvatureNorm μ ω q A) ^ m)
    (hcurv : ∀ θ : ℝ, weightedCurvatureNorm
      ((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 Gc)) ω q
      (fun z => A₀ + chartColourForm (Real.cos θ • z.1 + Real.sin θ • fieldOfCoordinates z.2)) ≤ ENNReal.ofReal b) :
    |(∫ k, G₀ (A₀ + chartColourForm k) ∂normalizedBallLaw (cutoffFactor ρ p) Ψ) -
        ∫ ζ, G₀ (A₀ + extendFluctuation ζ) ∂multivariateGaussian 0 Gc| ≤ α * (T * Db ^ m) := by
  set Lm := chartLinearMap (L := L) (u := u) (n := n) with hLm
  have hF : ContDiff ℝ 2 (fun k => G₀ (A₀ + chartColourForm k)) := hG.comp (contDiff_const.add Lm.contDiff)
  have hshift : ContDiff ℝ 2 (fun Z : ColourForm (n * L) => G₀ (A₀ + Z)) := hG.comp (contDiff_const.add contDiff_id)
  have hgrowF : ∀ (η : BondField (ChartBondIndex L u n)) (l : ℕ), l ≤ 2 →
      ‖iteratedFDeriv ℝ l (fun k => G₀ (A₀ + chartColourForm k)) η‖ ≤
        (|Cg| * (1 + ‖A₀‖ + ‖Lm‖) ^ kg * (1 + ‖Lm‖) ^ 2) * (1 + ‖η‖) ^ kg := by
    intro η l hl
    have e1 : (fun k => G₀ (A₀ + chartColourForm k)) = (fun Z : ColourForm (n * L) => G₀ (A₀ + Z)) ∘ Lm := rfl
    rw [e1, ContinuousLinearMap.iteratedFDeriv_comp_right Lm hshift η (by exact_mod_cast hl)]
    refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
    rw [iteratedFDeriv_comp_add_left]
    have h1 := hgrow (A₀ + Lm η) l hl
    have hLn : 0 ≤ ‖Lm‖ := norm_nonneg _
    have h2 : ∏ _i : Fin l, ‖Lm‖ ≤ (1 + ‖Lm‖) ^ 2 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      calc ‖Lm‖ ^ l ≤ (1 + ‖Lm‖) ^ l := by gcongr; linarith
        _ ≤ (1 + ‖Lm‖) ^ 2 := pow_le_pow_right₀ (by linarith) hl
    have h3 : 1 + ‖A₀ + Lm η‖ ≤ (1 + ‖A₀‖ + ‖Lm‖) * (1 + ‖η‖) := by
      have a1 := norm_add_le A₀ (Lm η)
      have a2 := Lm.le_opNorm η
      have a3 := norm_nonneg η
      have a4 := norm_nonneg A₀
      nlinarith [mul_nonneg a4 a3]
    have h4 : (1 + ‖A₀ + Lm η‖) ^ kg ≤ (1 + ‖A₀‖ + ‖Lm‖) ^ kg * (1 + ‖η‖) ^ kg := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h3 kg
    calc ‖iteratedFDeriv ℝ l G₀ (A₀ + Lm η)‖ * ∏ _i : Fin l, ‖Lm‖
        ≤ (|Cg| * ((1 + ‖A₀‖ + ‖Lm‖) ^ kg * (1 + ‖η‖) ^ kg)) * (1 + ‖Lm‖) ^ 2 := by
          refine mul_le_mul ?_ h2 (Finset.prod_nonneg fun _ _ => hLn) (by positivity)
          refine le_trans h1 ?_
          exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
            (mul_le_mul_of_nonneg_left h4 (abs_nonneg _))
      _ = _ := by ring
  have hfd : ∀ (k' : BondField (ChartBondIndex L u n)) (j : Fin 3 × ChartBondIndex L u n),
      fderiv ℝ (fun k => G₀ (A₀ + chartColourForm k)) k' (unitVariation j) =
        fderiv ℝ G₀ (A₀ + chartColourForm k') (chartColourForm (unitVariation j)) := by
    intro k' j
    have hd0 : HasFDerivAt G₀ (fderiv ℝ G₀ (A₀ + Lm k')) (A₀ + Lm k') :=
      ((hG.differentiable (by norm_num)) _).hasFDerivAt
    have hd1 : HasFDerivAt (fun k => A₀ + Lm k) Lm k' := Lm.hasFDerivAt.const_add A₀
    have hd2 := hd0.comp k' hd1
    have e : (fun k => G₀ (A₀ + chartColourForm k)) = G₀ ∘ fun k => A₀ + Lm k := rfl
    rw [e, hd2.fderiv]
    rfl
  have hAT : 0 ≤ α * (T * Db ^ m) := by positivity
  have hmain := hK (ChartBondIndex L u n) ρ p Ψ (fun k => G₀ (A₀ + chartColourForm k)) Gc _ (α * (T * Db ^ m)) kg
    (fun j => α₀ * w j.2) hρ hcut hΨ hGc hF hAT hgrowF hdrift ?_
  · exact hmain
  intro θ _ _
  have hAm : Measurable fun z : BondField (ChartBondIndex L u n) × EuclideanSpace ℝ (Fin 3 × ChartBondIndex L u n) =>
      A₀ + chartColourForm (Real.cos θ • z.1 + Real.sin θ • fieldOfCoordinates z.2) := by
    have c₀ : Continuous fun z : BondField (ChartBondIndex L u n) × EuclideanSpace ℝ (Fin 3 × ChartBondIndex L u n) =>
        Real.cos θ • z.1 + Real.sin θ • fieldOfCoordinates z.2 :=
      (continuous_fst.const_smul (Real.cos θ)).add
        ((continuous_fieldOfCoordinates.comp continuous_snd).const_smul (Real.sin θ))
    exact (continuous_const.add (Lm.continuous.comp c₀)).measurable
  have hs := hslope _ ((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 Gc)) _ hAm
  have hc1 : (1 + ENNReal.ofReal hb * weightedCurvatureNorm
      ((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 Gc)) ω q
      (fun z => A₀ + chartColourForm (Real.cos θ • z.1 + Real.sin θ • fieldOfCoordinates z.2))) ≤
      ENNReal.ofReal Db := by
    have h1 : ENNReal.ofReal hb * weightedCurvatureNorm
        ((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 Gc)) ω q
        (fun z => A₀ + chartColourForm (Real.cos θ • z.1 + Real.sin θ • fieldOfCoordinates z.2)) ≤
        ENNReal.ofReal hb * ENNReal.ofReal b :=
      mul_le_mul' le_rfl (hcurv θ)
    calc _ ≤ 1 + ENNReal.ofReal hb * ENNReal.ofReal b := add_le_add le_rfl h1
      _ = ENNReal.ofReal (1 + hb * b) := by
          rw [ENNReal.ofReal_add zero_le_one (mul_nonneg hb0 hb1), ENNReal.ofReal_mul hb0, ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal Db := ENNReal.ofReal_le_ofReal hDb
  calc ∑ j, ENNReal.ofReal (α₀ * w j.2) *
          eLpNorm (fun z : BondField (ChartBondIndex L u n) × EuclideanSpace ℝ (Fin 3 × ChartBondIndex L u n) =>
          fderiv ℝ (fun k => G₀ (A₀ + chartColourForm k))
            (Real.cos θ • z.1 + Real.sin θ • fieldOfCoordinates z.2) (unitVariation j)) 2
          ((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 Gc))
      ≤ ∑ j, ENNReal.ofReal α * (ENNReal.ofReal (w j.2) *
          eLpNorm (fun z : BondField (ChartBondIndex L u n) × EuclideanSpace ℝ (Fin 3 × ChartBondIndex L u n) =>
          fderiv ℝ G₀ (A₀ + chartColourForm (Real.cos θ • z.1 + Real.sin θ • fieldOfCoordinates z.2))
            (chartColourForm (unitVariation j))) 2
          ((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 Gc))) := by
        refine Finset.sum_le_sum fun j _ => ?_
        simp only [hfd]
        rw [← mul_assoc, ← ENNReal.ofReal_mul hα]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hα₀ (hw _))) le_rfl
    _ = ENNReal.ofReal α * ∑ j, ENNReal.ofReal (w j.2) *
          eLpNorm (fun z : BondField (ChartBondIndex L u n) × EuclideanSpace ℝ (Fin 3 × ChartBondIndex L u n) =>
          fderiv ℝ G₀ (A₀ + chartColourForm (Real.cos θ • z.1 + Real.sin θ • fieldOfCoordinates z.2))
            (chartColourForm (unitVariation j))) 2
          ((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 Gc)) := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal α * (ENNReal.ofReal T * ENNReal.ofReal Db ^ m) := by
        refine mul_le_mul' le_rfl (le_trans hs (mul_le_mul' le_rfl ?_))
        exact pow_le_pow_left' hc1 m
    _ = ENNReal.ofReal (α * (T * Db ^ m)) := by
        rw [ENNReal.ofReal_mul hα, ENNReal.ofReal_mul hT, ENNReal.ofReal_pow hDb0]
private theorem integral_map_smul_extendFluctuation (γ₁ : Measure (StepFluctuation L u n)) (c : ℝ)
    (G₀ : ColourForm (n * L) → ℝ) (hGc : Continuous G₀) (A₀ : ColourForm (n * L)) :
    ∫ ζ, G₀ (A₀ + extendFluctuation ζ) ∂(γ₁.map fun ζ => c • ζ) =
      ∫ ζ, G₀ (A₀ + c • extendFluctuation ζ) ∂γ₁ := by
  have hm : AEMeasurable (fun ζ : StepFluctuation L u n => c • ζ) γ₁ := (measurable_const_smul c).aemeasurable
  have hs : AEStronglyMeasurable (fun ζ : StepFluctuation L u n => G₀ (A₀ + extendFluctuation ζ))
      (γ₁.map fun ζ => c • ζ) :=
    (hGc.comp (continuous_const.add continuous_extendFluctuation)).aestronglyMeasurable
  rw [integral_map hm hs]
  simp only [extendFluctuation_smul]
private theorem abs_integral_sub_scaled_le (γ₁ : Measure (StepFluctuation L u n)) [IsProbabilityMeasure γ₁]
    (G₀ : ColourForm (n * L) → ℝ) (hGc : Continuous G₀) (A₀ : ColourForm (n * L))
    (ω : TorusPlaquette (n * L) → ℝ) (hω0 : ∀ p, 0 ≤ ω p) (hω1 : ∀ p, ω p ≤ 1) (q : ENNReal) (hq : 1 ≤ q)
    (s c₁ c₂ cq hb Db P Q : ℝ) (m m' : ℕ) (hs : 0 ≤ s) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hcq : 0 ≤ cq) (hb0 : 0 ≤ hb) (hQ : 0 ≤ Q) (hDb0 : 0 ≤ Db)
    (hDb : 1 + hb * (s + c₁ * cq + (s + c₂ * cq)) ≤ Db)
    (hcar : ∀ pp : OrientedPlaquette (n * L), ω pp.1 * curlNorm A₀ pp.1 ≤ s)
    (N2 : ∀ pp : OrientedPlaquette (n * L),
      eLpNorm (fun ζ => curlNorm (extendFluctuation ζ) pp.1) q γ₁ ≤ ENNReal.ofReal cq)
    (hi : ∀ A A' : StepFluctuation L u n → ColourForm (n * L), Measurable A → Measurable A' →
      ∫⁻ w, ENNReal.ofReal |G₀ (A w)| ∂γ₁ ≤
        ENNReal.ofReal P * (1 + ENNReal.ofReal hb *
          (weightedCurvatureNorm γ₁ ω q A + weightedCurvatureNorm γ₁ ω q A')) ^ m')
    (Q₀ : ℝ) (hQ₀ : Q₀ ≤ Q) (m₂ : ℕ) (hm₂ : m₂ = m)
    (hiii : ∀ A A' : StepFluctuation L u n → ColourForm (n * L), Measurable A → Measurable A' →
      ∫⁻ w, ENNReal.ofReal |G₀ (A w) - G₀ (A' w)| ∂γ₁ ≤
        ENNReal.ofReal Q₀ * weightedCurvatureNorm γ₁ ω q (fun w => A w - A' w) *
          (1 + ENNReal.ofReal hb * (weightedCurvatureNorm γ₁ ω q A + weightedCurvatureNorm γ₁ ω q A')) ^ m₂) :
    |(∫ ζ, G₀ (A₀ + c₁ • extendFluctuation ζ) ∂γ₁) - ∫ ζ, G₀ (A₀ + c₂ • extendFluctuation ζ) ∂γ₁| ≤
      Q * (|c₁ - c₂| * cq) * Db ^ m := by
  have hlm : Measurable (extendFluctuation : StepFluctuation L u n → ColourForm (n * L)) :=
    continuous_extendFluctuation.measurable
  have hN : ∀ (c : ℝ) (pp : OrientedPlaquette (n * L)),
      eLpNorm (fun ζ => curlNorm (c • extendFluctuation ζ) pp.1) q γ₁ ≤ ENNReal.ofReal (|c| * cq) := fun c pp => by
    have e1 : (fun ζ : StepFluctuation L u n => curlNorm (c • extendFluctuation ζ) pp.1) =
        |c| • fun ζ => curlNorm (extendFluctuation ζ) pp.1 := by
      funext ζ
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [curlNorm_smul]
    rw [e1, eLpNorm_const_smul, ENNReal.ofReal_mul (abs_nonneg _), Real.enorm_eq_ofReal (abs_nonneg _)]
    exact mul_le_mul' le_rfl (N2 pp)
  have hAm : ∀ c : ℝ, Measurable fun ζ : StepFluctuation L u n => A₀ + c • extendFluctuation ζ := fun c =>
    (continuous_const.add (continuous_extendFluctuation.const_smul c)).measurable
  have hA : ∀ c : ℝ, 0 ≤ c → weightedCurvatureNorm γ₁ ω q (fun ζ => A₀ + c • extendFluctuation ζ) ≤
      ENNReal.ofReal (s + c * cq) := fun c hc => by
    have := weightedCurvatureNorm_const_add_le γ₁ ω hω0 hω1 q hq A₀ (fun ζ => c • extendFluctuation ζ)
      (hlm.const_smul c) s (|c| * cq) hs (by positivity) hcar (hN c)
    rwa [abs_of_nonneg hc] at this
  have hdiff : weightedCurvatureNorm γ₁ ω q
      (fun ζ => (A₀ + c₁ • extendFluctuation ζ) - (A₀ + c₂ • extendFluctuation ζ)) ≤
      ENNReal.ofReal (|c₁ - c₂| * cq) := by
    have e1 : (fun ζ : StepFluctuation L u n => (A₀ + c₁ • extendFluctuation ζ) - (A₀ + c₂ • extendFluctuation ζ)) =
        fun ζ => (0 : ColourForm (n * L)) + (c₁ - c₂) • extendFluctuation ζ := by
      funext ζ
      rw [sub_smul]
      abel
    rw [e1]
    have h0 : ∀ pp : OrientedPlaquette (n * L), ω pp.1 * curlNorm (0 : ColourForm (n * L)) pp.1 ≤ 0 := fun pp => by
      have : curlNorm (0 : ColourForm (n * L)) pp.1 = 0 := by simp [curlNorm, curl]
      rw [this, mul_zero]
    have := weightedCurvatureNorm_const_add_le γ₁ ω hω0 hω1 q hq 0 (fun ζ => (c₁ - c₂) • extendFluctuation ζ)
      (hlm.const_smul (c₁ - c₂)) 0 (|c₁ - c₂| * cq) le_rfl (by positivity) h0 (hN _)
    rwa [zero_add] at this
  have hfin : ∀ c c' : ℝ, 0 ≤ c → 0 ≤ c' →
      (1 + ENNReal.ofReal hb * (weightedCurvatureNorm γ₁ ω q (fun ζ => A₀ + c • extendFluctuation ζ) +
        weightedCurvatureNorm γ₁ ω q (fun ζ => A₀ + c' • extendFluctuation ζ))) ≤
        ENNReal.ofReal (1 + hb * (s + c * cq + (s + c' * cq))) := fun c c' hc hc' => by
    have a1 : 0 ≤ s + c * cq := by positivity
    have a2 : 0 ≤ s + c' * cq := by positivity
    rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_mul hb0,
      ENNReal.ofReal_add a1 a2]
    exact add_le_add le_rfl (mul_le_mul' le_rfl (add_le_add (hA c hc) (hA c' hc')))
  have hint : ∀ c c' : ℝ, 0 ≤ c → 0 ≤ c' → Integrable (fun ζ => G₀ (A₀ + c • extendFluctuation ζ)) γ₁ :=
    fun c c' hc hc' => by
    refine ⟨(hGc.comp (continuous_const.add (continuous_extendFluctuation.const_smul c))).aestronglyMeasurable, ?_⟩
    have h1 := hi (fun ζ => A₀ + c • extendFluctuation ζ) (fun ζ => A₀ + c' • extendFluctuation ζ) (hAm c) (hAm c')
    exact show ∫⁻ w, ‖G₀ (A₀ + c • extendFluctuation w)‖ₑ ∂γ₁ < ⊤ from by
      simp only [Real.enorm_eq_ofReal_abs]
      refine lt_of_le_of_lt h1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top ?_))
      exact lt_of_le_of_lt (hfin c c' hc hc') ENNReal.ofReal_lt_top
  have i₁ := hint c₁ c₂ hc₁ hc₂
  have i₂ := hint c₂ c₁ hc₂ hc₁
  rw [← integral_sub i₁ i₂]
  have hb1 : (∫⁻ ζ, ENNReal.ofReal ‖G₀ (A₀ + c₁ • extendFluctuation ζ) - G₀ (A₀ + c₂ • extendFluctuation ζ)‖ ∂γ₁) ≤
      ENNReal.ofReal (Q * (|c₁ - c₂| * cq) * Db ^ m) := by
    simp only [Real.norm_eq_abs]
    subst hm₂
    refine le_trans (hiii _ _ (hAm c₁) (hAm c₂)) ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hQ, ENNReal.ofReal_pow hDb0]
    refine mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hQ₀) hdiff) (pow_le_pow_left' ?_ m₂)
    exact le_trans (hfin c₁ c₂ hc₁ hc₂) (ENNReal.ofReal_le_ofReal hDb)
  have h3 := norm_integral_le_lintegral_norm (μ := γ₁)
    (fun ζ => G₀ (A₀ + c₁ • extendFluctuation ζ) - G₀ (A₀ + c₂ • extendFluctuation ζ))
  rw [Real.norm_eq_abs] at h3
  refine le_trans h3 (ENNReal.toReal_le_of_le_ofReal (by positivity) hb1)
end Core
private theorem combined_bound_le (cc cs D₃ cm cn cq D r x h e y δ : ℝ) (m kk b : ℕ) (hcc : 0 ≤ cc) (hcs : 0 ≤ cs)
    (hD₃ : 0 ≤ D₃) (hcm : 0 ≤ cm) (hcn : 0 ≤ cn) (hcq : 0 ≤ cq) (hD : 1 ≤ D) (hr : 1 ≤ r) (hy : 1 ≤ y) (hh : 0 < h)
    (he : 0 < e) (hhe : h * e = 1) (hx : x⁻¹ = e * e) (hmk : m ≤ 2 * kk) (hδ : δ ≤ 4 * cn * x⁻¹) :
    cc * x⁻¹ * (cs * (D₃ * r * y) * r ^ b * h * (D * y) ^ m) + cm * r ^ b * h * (δ * cq) * (D * y) ^ m ≤
      (cc * cs * D₃ + 4 * cm * cn * cq) * D ^ (2 * kk) * r ^ (b + 1) * e * y ^ (m + 1) := by
  have hR : 1 ≤ r ^ b := one_le_pow₀ hr
  have hY : 1 ≤ y ^ m := one_le_pow₀ hy
  have hDm : D ^ m ≤ D ^ (2 * kk) := pow_le_pow_right₀ hD hmk
  set R := r ^ b with hRd
  set Yp := y ^ m with hYd
  have e1 : cc * x⁻¹ * (cs * (D₃ * r * y) * R * h * (D * y) ^ m) =
      cc * cs * D₃ * D ^ m * (R * r) * e * (Yp * y) := by
    rw [mul_pow, hx]
    have : e * e * h = e := by
      calc e * e * h = e * (h * e) := by ring
        _ = e := by rw [hhe, mul_one]
    calc cc * (e * e) * (cs * (D₃ * r * y) * R * h * (D ^ m * Yp)) =
          cc * cs * D₃ * D ^ m * (R * r) * (e * e * h) * (Yp * y) := by ring
      _ = _ := by rw [this]
  have e2 : cm * R * h * (δ * cq) * (D * y) ^ m ≤ 4 * cm * cn * cq * D ^ m * (R * r) * e * (Yp * y) := by
    have a1 : δ * cq ≤ 4 * cn * (e * e) * cq := by
      rw [← hx]
      exact mul_le_mul_of_nonneg_right hδ hcq
    have a2 : h * (4 * cn * (e * e) * cq) = 4 * cn * cq * e := by
      calc h * (4 * cn * (e * e) * cq) = 4 * cn * cq * e * (h * e) := by ring
        _ = _ := by rw [hhe, mul_one]
    have a3 : R ≤ R * r := le_mul_of_one_le_right (by linarith) hr
    have a4 : Yp ≤ Yp * y := le_mul_of_one_le_right (by linarith) hy
    calc cm * R * h * (δ * cq) * (D * y) ^ m ≤ cm * R * h * (4 * cn * (e * e) * cq) * (D * y) ^ m := by gcongr
      _ = 4 * cm * cn * cq * D ^ m * R * e * Yp := by
          rw [mul_pow]
          calc cm * R * h * (4 * cn * (e * e) * cq) * (D ^ m * Yp) =
                cm * R * (h * (4 * cn * (e * e) * cq)) * (D ^ m * Yp) := by ring
            _ = _ := by rw [a2]; ring
      _ ≤ 4 * cm * cn * cq * D ^ m * (R * r) * e * (Yp * y) := by gcongr
  rw [e1, pow_succ r, pow_succ y]
  calc cc * cs * D₃ * D ^ m * (R * r) * e * (Yp * y) + cm * R * h * (δ * cq) * (D * y) ^ m
      ≤ cc * cs * D₃ * D ^ m * (R * r) * e * (Yp * y) + 4 * cm * cn * cq * D ^ m * (R * r) * e * (Yp * y) := by
        gcongr
    _ = (cc * cs * D₃ + 4 * cm * cn * cq) * D ^ m * ((R * r) * e * (Yp * y)) := by ring
    _ ≤ (cc * cs * D₃ + 4 * cm * cn * cq) * D ^ (2 * kk) * ((R * r) * e * (Yp * y)) := by gcongr
    _ = _ := by ring
set_option maxHeartbeats 2000000 in
theorem fluctuationMeanOfGoodState
    (hK : gaussianComparisonStatement) (hP : normalizedBallLawIsProbabilityStatement)
    (hS : formMeanDerivBoundStatement) (hC : goodStateColdLawStatement)
    (hA : carriedCutCurvatureStatement) (hM : formMeansAtWeightStatement)
    (hW : formMeansStatement) (hN : scaleWindowStatement)
    (hR : farLevelSupportSitesStatement) :
    fluctuationMeanOfGoodStateStatement := by
  unfold formMeanDerivBoundStatement goodStateColdLawStatement carriedCutCurvatureStatement
    formMeansAtWeightStatement formMeansStatement scaleWindowStatement
    farLevelSupportSitesStatement ForAllPoints at *
  unfold fluctuationMeanOfGoodStateStatement ForAllPoints
  refine forAllParameters_mono (forAllParameters_and forAllParameters_weightRate_pos (forAllParameters_and hS
    (forAllParameters_and hC (forAllParameters_and hA (forAllParameters_and hM (forAllParameters_and hW
      (forAllParameters_and hN hR))))))) ?_
  rintro Λ ⟨hrate, ⟨Cs, _, Xs, _, _, hs⟩, ⟨Cc, _, Xc, _, _, hc⟩, ⟨Ca, _, Xa, _, _, ha⟩, ⟨Cm, _, Xm, _, _, hm⟩,
    ⟨Cw, _, _, _, _, hw⟩, ⟨Cn, _, Xn, _, _, hwindow⟩, ⟨Cr, _, _, _, _, hr⟩⟩
  set cr := |Cr 0| with hcr
  set cq := |Cc (8 * Λ.k)| with hcq
  set ca := |Ca 0| with hca
  set cs := |Cs 0| with hcs
  set cc := |Cc 0| with hcc
  set cm := |Cm 0| with hcm
  set cn := |Cn 0| with hcn
  set cw := Λ.stepParams.weightRate / 8 with hcw
  set D := 1 + 2 * ca + 6 * cq with hD
  set D₃ := 4 + cr + 2 / (cw / 2) with hD₃
  set K := (cc * cs * D₃ + 4 * cm * cn * cq) * D ^ (2 * Λ.k) with hKdef
  refine ⟨fun _ => K, 1, max (max (max Xs Xc) (max Xa Xm)) (max (max Xn Λ.floor) (max 1 (16 * cn ^ 2))), one_pos,
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _), ?_⟩
  intro S hx d n _ hd hn V Y hg B
  have hxs : Xs ≤ S.scaleCoupling :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxc : Xc ≤ S.scaleCoupling :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxa : Xa ≤ S.scaleCoupling :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hxm : Xm ≤ S.scaleCoupling :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hxn : Xn ≤ S.scaleCoupling :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have hx1 : 1 ≤ S.scaleCoupling :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have hx2 : 16 * cn ^ 2 ≤ S.scaleCoupling :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have hx0 : 0 < S.scaleCoupling := by linarith
  obtain ⟨hGd, ⟨Cg, kg, hgrow⟩, hslope⟩ := hs S hxs d n hd hn B
  obtain ⟨hPSD, hGauss, hV⟩ := hc S hxc d n hd hn
  obtain ⟨ρ, p, Ψ, hρ, hcut, hΨ, hmean, hnorm, hdrift⟩ := hV V Y hg
  have hcarried := ha S hxa d n hd hn V Y hg
  obtain ⟨hmeans, -⟩ := hm S hxm
  obtain ⟨-, -, -, -, hstep, -⟩ := hw S
  obtain ⟨-, -, -, -, -, hKle, hwin⟩ := hwindow S hxn
  obtain ⟨-, hrd, -⟩ := hr S
  have hnear := (hwin (S.lastSeparated + d) (by omega) (by omega)).1
  have hlog0 : 0 ≤ Real.log S.scaleCoupling := Real.log_nonneg hx1
  have hnear' : |S.coupling (S.lastSeparated + d) - S.scaleCoupling| ≤ cn * Real.log S.scaleCoupling :=
    le_trans hnear (mul_le_mul_of_nonneg_right (le_abs_self _) hlog0)
  have hh0 : 0 < S.scaleCoupling ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hx0 _
  have hhh : S.scaleCoupling ^ ((1 : ℝ) / 2) * S.scaleCoupling ^ ((1 : ℝ) / 2) = S.scaleCoupling := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hhe : S.scaleCoupling ^ ((1 : ℝ) / 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ) = 1 := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hcn0 : 0 ≤ cn := abs_nonneg _
  have hfloor : cn * Real.log S.scaleCoupling ≤ S.scaleCoupling / 2 := by
    have h1 := log_le_two_mul_sqrt S.scaleCoupling hx0
    have h2 : 4 * cn ≤ S.scaleCoupling ^ ((1 : ℝ) / 2) := by
      by_contra hc'
      push Not at hc'
      nlinarith
    nlinarith
  obtain ⟨hx'0, hgap, he'⟩ :=
    inv_sqrt_sub_le S.scaleCoupling (S.coupling (S.lastSeparated + d)) cn hx1 hcn0 hnear' hfloor
  have hnL : n * Λ.stepParams.side = S.levelSide (S.lastSeparated + d) := by
    have h1 : S.lastSeparated + d + 1 ≤ S.data.windowLevel := by omega
    rw [hn]
    show S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (S.lastSeparated + d + 1)) * Λ.stepParams.side =
      S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (S.lastSeparated + d))
    rw [mul_assoc, ← pow_succ]
    congr 2
    omega
  have hω0 : ∀ p, 0 ≤ S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side) p := fun p => (Real.exp_pos _).le
  have hω1 : ∀ p, S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side) p ≤ 1 := fun p => by
    refine Real.exp_le_one_iff.2 ?_
    have : 0 ≤ Λ.stepParams.weightRate / 8 *
        max 0 ((TorusFields.supDist p.1 (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ) -
        (S.radius : ℝ)) :=
      mul_nonneg (div_pos hrate (by norm_num)).le (le_max_left _ _)
    linarith
  have hk1 : 1 ≤ 8 * Λ.k := by
    have := NeZero.pos Λ.k
    omega
  have hq : (8 * (Λ.k : ENNReal)) = ((8 * Λ.k : ℕ) : ENNReal) := by push_cast; rfl
  have hq1 : (1 : ENNReal) ≤ 8 * (Λ.k : ENNReal) := by
    rw [hq]
    exact_mod_cast hk1
  have hprobs := hP _ ρ p Ψ hρ hcut hΨ.continuous
  have hμp : IsProbabilityMeasure (normalizedBallLaw (cutoffFactor ρ p) Ψ) := hprobs.1
  have hγ₁ : IsProbabilityMeasure (fluctuationGaussian Λ.stepParams.coupling Λ.stepParams.side 1 (S.lastSeparated + d) n) := by
    unfold fluctuationGaussian
    infer_instance
  have hγ : IsProbabilityMeasure
      (fluctuationGaussian Λ.stepParams.coupling Λ.stepParams.side (S.coupling (S.lastSeparated + d)) (S.lastSeparated + d) n) := by
    unfold fluctuationGaussian
    infer_instance
  have hscale := fluctuationGaussian_map_smul Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n
    (S.coupling (S.lastSeparated + d)) hx'0 hPSD
  have N1 : ∀ pp : OrientedPlaquette (n * Λ.stepParams.side),
      eLpNorm (fun k => curlNorm (chartColourForm k) pp.1) (8 * (Λ.k : ENNReal))
        (normalizedBallLaw (cutoffFactor ρ p) Ψ) ≤ ENNReal.ofReal (cq * S.scaleCoupling ^ (-(1 / 2) : ℝ)) :=
    fun pp => by
    have h1 := hnorm (8 * Λ.k) hk1
    rw [← hq] at h1
    refine le_trans (eLpNorm_le_of_weightedCurvatureNorm _ _ _ _ h1 pp) (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_pos_of_pos hx0 _).le
  have N2 : ∀ pp : OrientedPlaquette (n * Λ.stepParams.side),
      eLpNorm (fun ζ => curlNorm (extendFluctuation ζ) pp.1) (8 * (Λ.k : ENNReal))
        (fluctuationGaussian Λ.stepParams.coupling Λ.stepParams.side 1 (S.lastSeparated + d) n) ≤ ENNReal.ofReal cq := fun pp => by
    have h1 := hGauss (8 * Λ.k) hk1
    rw [← hq] at h1
    exact le_trans (eLpNorm_le_of_weightedCurvatureNorm _ _ _ _ h1 pp) (ENNReal.ofReal_le_ofReal (le_abs_self _))
  clear hs hc ha hm hw hwindow hr hGauss hnorm
  have hv0 : 0 ≤ S.localCurvature (S.lastSeparated + d + 1) n V := by
    unfold MomentPoint.localCurvature boxCurvature
    exact Real.iSup_nonneg fun _ => norm_nonneg _
  have hr1 : (1 : ℝ) ≤ (S.range : ℝ) := by
    have : 0 < S.range := Nat.ceil_pos.2 (Real.rpow_pos_of_pos hx0 _)
    exact_mod_cast this
  have hcq0 : 0 ≤ cq := abs_nonneg _
  have hca0 : 0 ≤ ca := abs_nonneg _
  have hcs0 : 0 ≤ cs := abs_nonneg _
  have hcc0 : 0 ≤ cc := abs_nonneg _
  have hcm0 : 0 ≤ cm := abs_nonneg _
  have hcr0 : 0 ≤ cr := abs_nonneg _
  have hcw0 : 0 < cw := div_pos hrate (by norm_num)
  have hD1 : 1 ≤ D := by
    rw [hD]
    linarith only [hca0, hcq0]
  have hD₃0 : 0 ≤ D₃ := by
    rw [hD₃]
    have : 0 ≤ 2 / (cw / 2) := div_nonneg (by norm_num) (by linarith only [hcw0])
    linarith only [this, hcr0]
  set e := S.scaleCoupling ^ (-(1 / 2) : ℝ) with he
  set h := S.scaleCoupling ^ ((1 : ℝ) / 2) with hh
  set e' := S.coupling (S.lastSeparated + d) ^ (-(1 / 2) : ℝ) with hedef
  set v := S.localCurvature (S.lastSeparated + d + 1) n V with hvdef
  have he0 : 0 < e := Real.rpow_pos_of_pos hx0 _
  have he'0 : 0 < e' := Real.rpow_pos_of_pos hx'0 _
  set A₀ : ColourForm (n * Λ.stepParams.side) := fun e b => pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side (S.lastSeparated + d)
    (S.cutoffColourForm (S.lastSeparated + d + 1) n V) e b with hA₀
  have hcar : ∀ pp : OrientedPlaquette (n * Λ.stepParams.side),
      S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side) pp.1 * curlNorm A₀ pp.1 ≤ ca * v := fun pp =>
    le_trans (hcarried pp) (mul_le_mul_of_nonneg_right (le_abs_self _) hv0)
  have hcav : 0 ≤ ca * v := mul_nonneg hca0 hv0
  have hm1 : ∀ Φ₀ : ColourForm (n * Λ.stepParams.side) → ℝ,
      (coldExpectation (S.tower.stage (S.lastSeparated + d)).toStepSetup
        (S.smoothedField (S.lastSeparated + d + 1) n V) fun η =>
      Φ₀ (fun e b => A₀ e b + freeCoordForm (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
        (S.smoothedField (S.lastSeparated + d + 1) n V)) η e b)) =
      ∫ k, Φ₀ (A₀ + chartColourForm k) ∂normalizedBallLaw (cutoffFactor ρ p) Ψ := fun Φ₀ => hmean fun Z => Φ₀ (A₀ + Z)
  rw [hm1 (S.formProductMean d (n * Λ.stepParams.side) B), hstep d n B]
  change |(∫ k, S.formProductMean d (n * Λ.stepParams.side) B (A₀ + chartColourForm k) ∂normalizedBallLaw (cutoffFactor ρ p) Ψ) -
    ∫ η, S.formProductMean d (n * Λ.stepParams.side) B (A₀ + e • extendFluctuation η)
      ∂fluctuationGaussian Λ.stepParams.coupling Λ.stepParams.side 1 (S.lastSeparated + d) n| ≤
    K * (S.range : ℝ) ^ (4 * B.card + 1) * e * (1 + h * v) ^ (2 * B.card)
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    have : 0 ≤ cc * cs * D₃ + 4 * cm * cn * cq := by positivity
    exact mul_nonneg this (pow_nonneg (by linarith only [hD1]) _)
  have hz0 : 0 ≤ h * v := mul_nonneg hh0.le hv0
  have hy1 : 1 ≤ 1 + h * v := by linarith only [hz0]
  rcases B.eq_empty_or_nonempty with rfl | hB
  · have hconst : ∀ A : ColourForm (n * Λ.stepParams.side),
        S.formProductMean d (n * Λ.stepParams.side) ∅ A = S.formProductMean d (n * Λ.stepParams.side) ∅ 0 := fun A => by
      simp [MomentPoint.formProductMean, MomentPoint.formProduct]
    simp only [hconst, integral_const, probReal_univ, one_smul, sub_self, abs_zero]
    positivity
  obtain ⟨m, hm⟩ : ∃ m, 2 * B.card = m + 1 := ⟨2 * B.card - 1, by have := hB.card_pos; omega⟩
  have hmsub : 2 * B.card - 1 = m := by omega
  have hmk : m ≤ 2 * Λ.k := by
    have : B.card ≤ Λ.k := by simpa using Finset.card_le_univ B
    omega
  have hexx : S.scaleCoupling⁻¹ = e * e := by
    refine eq_comm.1 (eq_inv_of_mul_eq_one_left ?_)
    calc e * e * S.scaleCoupling = e * e * (h * h) := by rw [hhh]
      _ = (h * e) * (h * e) := by ring
      _ = 1 := by rw [hhe]; norm_num
  have hrd' : (S.radius : ℝ) ≤ cr * (S.range : ℝ) :=
    le_trans hrd (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith only [hr1]))
  set y := 1 + h * v with hy
  set W := D₃ * (S.range : ℝ) * y with hW
  have hW0 : 0 ≤ W := mul_nonneg (mul_nonneg hD₃0 (by linarith only [hr1])) (by linarith only [hy1])
  have hwts : ∀ (b : ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n) (pl : TorusPlaquette (n * Λ.stepParams.side)),
      TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) b.1.1) pl.1 ≤ 1 →
      (1 + (1 + (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) b.1.1)
          (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ) + (S.range : ℝ)) * h * v) *
        Real.sqrt (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side) pl) ≤ W := by
    intro b pl hb
    have h1 : (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) b.1.1)
          (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ) ≤
        (TorusFields.supDist pl.1 (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ) + 1 := by
      have h2 := supDist_triangle (toTorusSite (n * Λ.stepParams.side) b.1.1) pl.1
        (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side))
      have h3 : TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) b.1.1)
            (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) ≤
          TorusFields.supDist pl.1 (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) + 1 := by omega
      exact_mod_cast h3
    have h4 := weight_mul_sqrt_exp_le cw (S.radius : ℝ) (S.range : ℝ)
      (TorusFields.supDist pl.1 (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ) (h * v) hcw0
      (Nat.cast_nonneg _) hr1 (Nat.cast_nonneg _) hz0 cr hrd'
    refine le_trans ?_ (le_trans h4 (le_of_eq ?_))
    · refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      have h5 : (1 + (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) b.1.1)
            (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ) + (S.range : ℝ)) * (h * v) ≤
          (1 + ((TorusFields.supDist pl.1 (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ) + 1) +
            (S.range : ℝ)) *
            (h * v) :=
        mul_le_mul_of_nonneg_right (by linarith only [h1]) hz0
      linarith only [h5]
    · rw [hW, hy, hD₃]
  have hw0 : ∀ b : ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n,
      0 ≤ 1 + (1 + (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) b.1.1)
        (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ) + (S.range : ℝ)) * h * v := fun b => by
    have : 0 ≤ (1 + (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) b.1.1)
        (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ) + (S.range : ℝ)) * h * v :=
      mul_nonneg (mul_nonneg (by have := Nat.cast_nonneg (α := ℝ) (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) b.1.1)
                                   (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)))
                                 linarith only [this, hr1]) hh0.le) hv0
    linarith only [this]
  have hPSDx := fluctuationCov_posSemidef Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n
    (S.coupling (S.lastSeparated + d)) hx'0 hPSD
  have hhe' : h * e' ≤ 2 := by
    calc h * e' ≤ h * (2 * e) := mul_le_mul_of_nonneg_left he' hh0.le
      _ = 2 * (h * e) := by ring
      _ = 2 := by rw [hhe]; norm_num
  have hDy0 : 0 ≤ D * y := mul_nonneg (by linarith only [hD1]) (by linarith only [hy1])
  have hDb : 1 + h * (ca * v + (cq * e + e' * cq)) ≤ D * y := by
    have e1 : h * (ca * v + (cq * e + e' * cq)) = ca * (h * v) + cq * (h * e) + (h * e') * cq := by ring
    rw [e1, hhe, hD, hy]
    nlinarith only [mul_nonneg hca0 hz0, mul_nonneg hcq0 hz0, mul_le_mul_of_nonneg_right hhe' hcq0, hcq0, hca0, hz0]
  have hDb' : 1 + h * (ca * v + e' * cq + (ca * v + e * cq)) ≤ D * y := by
    have e1 : h * (ca * v + e' * cq + (ca * v + e * cq)) = 2 * (ca * (h * v)) + (h * e') * cq + cq * (h * e) := by
      ring
    rw [e1, hhe, hD, hy]
    nlinarith only [mul_nonneg hca0 hz0, mul_nonneg hcq0 hz0, mul_le_mul_of_nonneg_right hhe' hcq0, hcq0, hca0, hz0]
  have N2'' : ∀ pp : OrientedPlaquette (n * Λ.stepParams.side),
      eLpNorm (fun ζ => curlNorm (extendFluctuation ζ) pp.1) (8 * (Λ.k : ENNReal))
        (multivariateGaussian 0 (fluctuationCov Λ.stepParams.coupling Λ.stepParams.side (S.coupling (S.lastSeparated + d))
          (S.lastSeparated + d) n)) ≤ ENNReal.ofReal (e' * cq) := fun pp => by
    have h1 := eLpNorm_curlNorm_map_smul_le _ e' cq he'0 _ pp (N2 pp)
    rw [hscale] at h1
    exact h1
  have hR := gaussianComparison_shifted hK ρ p Ψ hρ hcut hΨ
    (fluctuationCov Λ.stepParams.coupling Λ.stepParams.side (S.coupling (S.lastSeparated + d)) (S.lastSeparated + d) n) hPSDx
    (S.formProductMean d (n * Λ.stepParams.side) B) hGd Cg kg hgrow A₀ (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side))
    (8 * (Λ.k : ENNReal))
    (fun b => 1 + (1 + (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) b.1.1)
      (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ) + (S.range : ℝ)) * h * v) hw0
    (cc * S.scaleCoupling⁻¹) (Cc 0 * S.scaleCoupling⁻¹) (cs * W * (S.range : ℝ) ^ (4 * B.card) * h) h (D * y)
    (ca * v + (cq * e + e' * cq))
    (mul_nonneg hcc0 (inv_pos.2 hx0).le) (mul_le_mul_of_nonneg_right (le_abs_self _) (inv_pos.2 hx0).le)
    (by have : (0 : ℝ) ≤ (S.range : ℝ) ^ (4 * B.card) := pow_nonneg (Nat.cast_nonneg _) _
        exact mul_nonneg (mul_nonneg (mul_nonneg hcs0 hW0) this) hh0.le) hh0.le
    (add_nonneg hcav (add_nonneg (mul_nonneg hcq0 he0.le) (mul_nonneg he'0.le hcq0))) hDb m hDy0
    (fun j => hdrift j) ?_
    (fun θ => weightedCurvatureNorm_rotation_le _ _ _ hω0 hω1 _ hq1 A₀ (ca * v) (cq * e) (e' * cq) hcav
      (mul_nonneg hcq0 he0.le) (mul_nonneg he'0.le hcq0) hcar N1 N2'' θ)
  swap
  · intro Ω _ μ' _ A hAm
    have h1 := hslope _ W hw0 hW0 hwts Ω μ' A hAm
    rw [hmsub] at h1
    refine le_trans h1 (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    have : (0 : ℝ) ≤ (S.range : ℝ) ^ (4 * B.card) := pow_nonneg (Nat.cast_nonneg _) _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hW0) this) hh0.le
  have hT2 := abs_integral_sub_scaled_le (fluctuationGaussian Λ.stepParams.coupling Λ.stepParams.side 1 (S.lastSeparated + d) n)
    (S.formProductMean d (n * Λ.stepParams.side) B) hGd.continuous A₀
    (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side)) hω0 hω1 (8 * (Λ.k : ENNReal)) hq1 (ca * v) e' e cq h (D * y)
    (Cm 0 * (S.range : ℝ) ^ (4 * B.card)) (cm * (S.range : ℝ) ^ (4 * B.card) * h) m (2 * B.card) hcav he'0.le he0.le
    hcq0 hh0.le
    (by have : (0 : ℝ) ≤ (S.range : ℝ) ^ (4 * B.card) := pow_nonneg (Nat.cast_nonneg _) _
        exact mul_nonneg (mul_nonneg hcm0 this) hh0.le) hDy0 hDb' hcar N2
    (fun A A' hA hA' => (hmeans d (n * Λ.stepParams.side) (by omega) hnL B _ _ A A' hA hA').1)
    (Cm 0 * (S.range : ℝ) ^ (4 * B.card) * h) (by
      have : (0 : ℝ) ≤ (S.range : ℝ) ^ (4 * B.card) := pow_nonneg (Nat.cast_nonneg _) _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) this) hh0.le)
    (2 * B.card - 1) hmsub
    (fun A A' hA hA' => (hmeans d (n * Λ.stepParams.side) (by omega) hnL B _ _ A A' hA hA').2.2)
  have he2 : ∫ ζ, S.formProductMean d (n * Λ.stepParams.side) B (A₀ + extendFluctuation ζ)
        ∂multivariateGaussian 0 (fluctuationCov Λ.stepParams.coupling Λ.stepParams.side (S.coupling (S.lastSeparated + d))
          (S.lastSeparated + d) n) =
      ∫ ζ, S.formProductMean d (n * Λ.stepParams.side) B (A₀ + e' • extendFluctuation ζ)
        ∂fluctuationGaussian Λ.stepParams.coupling Λ.stepParams.side 1 (S.lastSeparated + d) n := by
    have h1 : multivariateGaussian 0 (fluctuationCov Λ.stepParams.coupling Λ.stepParams.side (S.coupling (S.lastSeparated + d))
          (S.lastSeparated + d) n) =
        (fluctuationGaussian Λ.stepParams.coupling Λ.stepParams.side 1 (S.lastSeparated + d) n).map fun ζ => e' • ζ := hscale.symm
    rw [h1]
    exact integral_map_smul_extendFluctuation _ e' _ hGd.continuous A₀
  rw [he2] at hR
  have hfin := combined_bound_le cc cs D₃ cm cn cq D (S.range : ℝ) S.scaleCoupling h e y |e' - e| m Λ.k (4 * B.card)
    hcc0 hcs0 hD₃0 hcm0 hcn0 hcq0 hD1 hr1 hy1 hh0 he0 hhe hexx hmk hgap
  rw [← hm] at hfin
  calc _ ≤ _ := abs_sub_le _ (∫ ζ, S.formProductMean d (n * Λ.stepParams.side) B (A₀ + e' • extendFluctuation ζ)
        ∂fluctuationGaussian Λ.stepParams.coupling Λ.stepParams.side 1 (S.lastSeparated + d) n) _
    _ ≤ _ := add_le_add hR hT2
    _ ≤ _ := hfin
end YangMills.Construction.MomentLaw
end
