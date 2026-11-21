import YangMills.Construction.Towers.TheResponseNearZeroProof
import Reconstruction.MinkowskiSpace.ArgumentsOfTheFieldProductsOfAWightmanTheoryLieInTheirDomainsProof
import Reconstruction.MinkowskiSpace.LocalityOfTheWightmanValuesProof
import Reconstruction.MinkowskiSpace.TranslationOperatorsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Topology Asymptotics
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace YangMills.Construction.FieldFormTranslations
open MinkowskiSpace OneLoopNotation ComplexHilbert HilbertToolkit ProjectionMeasures
  SesquilinearForms FieldForms WightmanTheory PVMCalculus
theorem sqrt_two_mul_le_rexp {x : ℝ} (hx : 0 ≤ x) : Real.sqrt 2 * x ≤ Real.exp x := by
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [sq_nonneg (x - Real.sqrt 2)]
theorem rexp_neg_mul_mul_le_inv {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    Real.exp (-(ε * t)) * (Real.sqrt 2 * t) ≤ ε⁻¹ := by
  have hq := sqrt_two_mul_le_rexp (mul_nonneg hε.le ht)
  rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), ← div_eq_mul_inv, le_div_iff₀ hε]
  calc Real.sqrt 2 * t * ε = Real.sqrt 2 * (ε * t) := by ring
    _ ≤ _ := hq
theorem rexp_neg_mul_mul_sq_le {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    Real.exp (-(ε * t)) * t ^ 2 ≤ 2 / ε ^ 2 := by
  have hq := Real.quadratic_le_exp_of_nonneg (mul_nonneg hε.le ht)
  have hεt : 0 ≤ ε * t := mul_nonneg hε.le ht
  rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_div_assoc', le_div_iff₀ (by positivity)]
  nlinarith
theorem norm_cexp_sub_cexp_le {z w : ℂ} {c : ℝ} (hz : z.re ≤ -c) (hw : w.re ≤ -c) :
    ‖Complex.exp w - Complex.exp z‖ ≤ Real.exp (-c) * ‖w - z‖ := by
  refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Complex.exp)
    (f' := Complex.exp) (s := {x : ℂ | x.re ≤ -c})
    (fun x _ => (Complex.hasDerivAt_exp x).hasDerivWithinAt) (fun x hx => ?_)
    (convex_halfSpace_re_le _) hz hw
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr hx
theorem norm_cexp_sub_cexp_sub_le {z w : ℂ} {c : ℝ} (hz : z.re ≤ -c) (hw : w.re ≤ -c) :
    ‖Complex.exp w - Complex.exp z - (w - z) * Complex.exp z‖ ≤
      Real.exp (-c) * ‖w - z‖ ^ 2 := by
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x : ℂ => Complex.exp x - x * Complex.exp z)
    (f' := fun x : ℂ => Complex.exp x - Complex.exp z) (s := segment ℝ z w)
    (C := Real.exp (-c) * ‖w - z‖) (x := z) (y := w)
    (fun x _ => by
      have hx₁ : HasDerivAt (fun y : ℂ => Complex.exp y - y * Complex.exp z)
          (Complex.exp x - 1 * Complex.exp z) x :=
        (Complex.hasDerivAt_exp x).sub ((hasDerivAt_id x).mul_const (Complex.exp z))
      simpa using hx₁.hasDerivWithinAt)
    (fun x hx => by
      have hre : x.re ≤ -c := (convex_halfSpace_re_le (-c)).segment_subset hz hw hx
      refine (norm_cexp_sub_cexp_le hz hre).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
      have hlin : a • z + b • w - z = (b : ℂ) * (w - z) := by
        have ha' : (a : ℂ) = 1 - b := by
          rw [eq_sub_iff_add_eq]
          exact_mod_cast hab
        simp only [Complex.real_smul, ha']
        ring
      rw [hlin, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb]
      have hb1 : b ≤ 1 := by linarith
      exact mul_le_of_le_one_left (norm_nonneg _) hb1)
    (convex_segment z w) (left_mem_segment ℝ z w) (right_mem_segment ℝ z w)
  have hrw : Complex.exp w - w * Complex.exp z - (Complex.exp z - z * Complex.exp z) =
      Complex.exp w - Complex.exp z - (w - z) * Complex.exp z := by ring
  rw [hrw] at hmv
  calc _ ≤ _ := hmv
    _ = _ := by ring
theorem minkowskiForm_toComplex_eq (w : ComplexVec4) (p : RealVec4) :
    minkowskiForm w (toComplex p) =
      w 0 * (p 0 : ℂ) - (w 1 * (p 1 : ℂ) + w 2 * (p 2 : ℂ) + w 3 * (p 3 : ℂ)) := by
  unfold minkowskiForm spaceBilin spacePart toComplex
  rw [Fin.sum_univ_three]
  rfl
theorem re_I_mul_minkowskiForm (ζ : ComplexVec4) (p : RealVec4) :
    (Complex.I * minkowskiForm ζ (toComplex p)).re =
      -(minkowskiForm (toComplex (imPart ζ)) (toComplex p)).re := by
  rw [minkowskiForm_toComplex_eq, minkowskiForm_toComplex_eq]
  simp [toComplex, imPart]
theorem zeroth_nonneg_of_mem_closedFutureCone {p : RealVec4} (hp : p ∈ closedFutureCone) :
    0 ≤ p 0 := by apply _root_.YangMills.Construction.WightmanTheory.DomainFacts.time_nonneg_of_mem_closedFutureCone <;> assumption
theorem zero_mem_closedFutureCone' : (0 : RealVec4) ∈ closedFutureCone := by apply _root_.YangMills.Construction.WightmanLocality.origin_mem_closedFutureCone <;> assumption
theorem re_I_mul_minkowskiForm_le (hform : ConeTubeLorentz.FormOnClosedCone) {ζ : ComplexVec4}
    {p : RealVec4} (hζ : ImInClosedCone ζ) (hp : p ∈ closedFutureCone) :
    (Complex.I * minkowskiForm ζ (toComplex p)).re ≤ -(tubeGap ζ * p 0) := by
  rw [re_I_mul_minkowskiForm]
  have hf := (hform _ hζ p hp).1
  unfold tubeGap
  linarith
theorem re_I_mul_minkowskiForm_le_of_gap (hform : ConeTubeLorentz.FormOnClosedCone)
    {ζ : ComplexVec4} {p : RealVec4} {ε : ℝ} (hε : 0 ≤ ε) (hζ : ε ≤ tubeGap ζ)
    (hp : p ∈ closedFutureCone) : (Complex.I * minkowskiForm ζ (toComplex p)).re ≤ -(ε * p 0) := by
  have hc : ImInClosedCone ζ := by
    show coneGap (imPart ζ) ≥ 0
    exact hε.trans hζ
  have hr := re_I_mul_minkowskiForm_le hform hc hp
  have hm := mul_le_mul_of_nonneg_right hζ (zeroth_nonneg_of_mem_closedFutureCone hp)
  linarith
theorem norm_minkowskiForm_le (w : ComplexVec4) (p : RealVec4) :
    ‖minkowskiForm w (toComplex p)‖ ≤ complexEucNorm w * TorusMetric.euclidNormVec p := by
  have hsum : ‖minkowskiForm w (toComplex p)‖ ≤ ∑ μ, ‖w μ‖ * |p μ| := by
    rw [minkowskiForm_toComplex_eq, Fin.sum_univ_four]
    have hterm : ∀ μ, ‖w μ * (p μ : ℂ)‖ = ‖w μ‖ * |p μ| := fun μ => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have t₁ := norm_sub_le (w 0 * (p 0 : ℂ)) (w 1 * (p 1 : ℂ) + w 2 * (p 2 : ℂ) + w 3 * (p 3 : ℂ))
    have t₂ := norm_add_le (w 1 * (p 1 : ℂ) + w 2 * (p 2 : ℂ)) (w 3 * (p 3 : ℂ))
    have t₃ := norm_add_le (w 1 * (p 1 : ℂ)) (w 2 * (p 2 : ℂ))
    rw [hterm 0] at t₁
    rw [hterm 3] at t₂
    rw [hterm 1, hterm 2] at t₃
    linarith
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun μ => ‖w μ‖) (fun μ => |p μ|)
  simp only [sq_abs] at hcs
  exact hsum.trans hcs
theorem norm_minkowskiForm_le_zeroth (hform : ConeTubeLorentz.FormOnClosedCone) (w : ComplexVec4)
    {p : RealVec4} (hp : p ∈ closedFutureCone) :
    ‖minkowskiForm w (toComplex p)‖ ≤ complexEucNorm w * (Real.sqrt 2 * p 0) :=
  (norm_minkowskiForm_le w p).trans
    (mul_le_mul_of_nonneg_left (hform p hp p hp).2.2 (Real.sqrt_nonneg _))
theorem tubeGap_continuous : Continuous tubeGap := by apply _root_.YangMills.Construction.FieldForms.SpacelikeExtension.continuous_tubeGap <;> assumption
theorem futureTube_isOpen : IsOpen futureTube :=
  isOpen_lt continuous_const tubeGap_continuous
theorem complexEucNorm_continuous : Continuous complexEucNorm := by apply _root_.YangMills.Construction.Tower.ResponseAtSmallMomentum.continuous_euclidNorm <;> assumption
theorem conjPoint_coord (ζ : ComplexVec4) (μ : Fin 4) :
    conjPoint ζ μ = conj (ζ μ) := by
  apply Complex.ext <;> simp [conjPoint, toComplex, rePart, imPart]
def expSymbol (ζ : ComplexVec4) : (Fin 4 → ℝ) → ℂ :=
  closedFutureCone.indicator fun p => Complex.exp (Complex.I * minkowskiForm ζ (toComplex p))
def expDerivSymbol (b w : ComplexVec4) : (Fin 4 → ℝ) → ℂ :=
  closedFutureCone.indicator fun p =>
    Complex.I * minkowskiForm w (toComplex p) * Complex.exp (Complex.I * minkowskiForm b (toComplex p))
theorem continuous_minkowskiForm_toComplex (ζ : ComplexVec4) :
    Continuous fun p : Fin 4 → ℝ => minkowskiForm ζ (toComplex p) := by
  simp only [minkowskiForm_toComplex_eq]
  fun_prop
theorem isBddMeasurableFun_indicator_of_continuous {f : (Fin 4 → ℝ) → ℂ} (hf : Continuous f)
    {b : ℝ} (hb₀ : 0 ≤ b) (hb : ∀ p ∈ closedFutureCone, ‖f p‖ ≤ b) :
    IsBddMeasurableFun (closedFutureCone.indicator f) := by
  refine ⟨hf.measurable.indicator closedFutureConeBorel.2, b, fun p => ?_⟩
  by_cases hp : p ∈ closedFutureCone
  · rw [Set.indicator_of_mem hp]
    exact hb p hp
  · rw [Set.indicator_of_notMem hp, norm_zero]
    exact hb₀
theorem norm_cexp_I_mul_le_one (hform : ConeTubeLorentz.FormOnClosedCone)
    {ζ : ComplexVec4} (hζ : ImInClosedCone ζ) {p : RealVec4}
    (hp : p ∈ closedFutureCone) : ‖Complex.exp (Complex.I * minkowskiForm ζ (toComplex p))‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have hr := re_I_mul_minkowskiForm_le hform hζ hp
  have hn : 0 ≤ tubeGap ζ * p 0 := mul_nonneg hζ (zeroth_nonneg_of_mem_closedFutureCone hp)
  linarith
theorem isBddMeasurableFun_expSymbol (hform : ConeTubeLorentz.FormOnClosedCone)
    {ζ : ComplexVec4} (hζ : ImInClosedCone ζ) :
    IsBddMeasurableFun (expSymbol ζ) :=
  isBddMeasurableFun_indicator_of_continuous
    (Complex.continuous_exp.comp (continuous_const.mul (continuous_minkowskiForm_toComplex ζ)))
    zero_le_one fun _ hp => norm_cexp_I_mul_le_one hform hζ hp
theorem isBddMeasurableFun_expDerivSymbol
    (hform : ConeTubeLorentz.FormOnClosedCone) {b : ComplexVec4} (w : ComplexVec4)
    {ε : ℝ} (hε : 0 < ε) (hb : ε ≤ tubeGap b) :
    IsBddMeasurableFun (expDerivSymbol b w) := by
  refine isBddMeasurableFun_indicator_of_continuous (b := complexEucNorm w * ε⁻¹)
    ((continuous_const.mul (continuous_minkowskiForm_toComplex w)).mul
      (Complex.continuous_exp.comp (continuous_const.mul (continuous_minkowskiForm_toComplex b))))
    (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr hε.le)) fun p hp => ?_
  have hre := re_I_mul_minkowskiForm_le_of_gap hform hε.le hb hp
  have hfw := norm_minkowskiForm_le_zeroth hform w hp
  have hdec := rexp_neg_mul_mul_le_inv hε (zeroth_nonneg_of_mem_closedFutureCone hp)
  have hw : 0 ≤ complexEucNorm w := Real.sqrt_nonneg _
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_exp]
  calc ‖minkowskiForm w (toComplex p)‖ * Real.exp (Complex.I * minkowskiForm b (toComplex p)).re
      ≤ (complexEucNorm w * (Real.sqrt 2 * p 0)) * Real.exp (-(ε * p 0)) :=
        mul_le_mul hfw (Real.exp_le_exp.mpr hre) (Real.exp_pos _).le
          (mul_nonneg hw (mul_nonneg (Real.sqrt_nonneg _)
            (zeroth_nonneg_of_mem_closedFutureCone hp)))
    _ = complexEucNorm w * (Real.exp (-(ε * p 0)) * (Real.sqrt 2 * p 0)) := by ring
    _ ≤ complexEucNorm w * ε⁻¹ := mul_le_mul_of_nonneg_left hdec hw
theorem isBddMeasurableFun_sub {u u' : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u)
    (hu' : IsBddMeasurableFun u') : IsBddMeasurableFun fun p => u p - u' p := by
  obtain ⟨hm, b, hb⟩ := hu
  obtain ⟨hm', b', hb'⟩ := hu'
  exact ⟨hm.sub hm', b + b', fun p => (norm_sub_le _ _).trans (add_le_add (hb p) (hb' p))⟩
theorem isBddMeasurableFun_const_mul (c : ℂ) {u : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u) :
    IsBddMeasurableFun fun p => c * u p := by
  obtain ⟨hm, b, hb⟩ := hu
  refine ⟨hm.const_mul c, ‖c‖ * b, fun p => ?_⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb p) (norm_nonneg _)
theorem expSymbol_mul (ζ ζ' : ComplexVec4) (p : Fin 4 → ℝ) :
    expSymbol ζ p * expSymbol ζ' p = expSymbol (ζ + ζ') p := by
  by_cases hp : p ∈ closedFutureCone
  · simp only [expSymbol, Set.indicator_of_mem hp, minkowskiForm_add_left, mul_add, Complex.exp_add]
  · simp only [expSymbol, Set.indicator_of_notMem hp, mul_zero]
theorem conj_expSymbol (ζ : ComplexVec4) (p : Fin 4 → ℝ) :
    conj (expSymbol ζ p) = expSymbol (-conjPoint ζ) p := by
  by_cases hp : p ∈ closedFutureCone
  · simp only [expSymbol, Set.indicator_of_mem hp]
    rw [← Complex.exp_conj]
    congr 1
    simp only [minkowskiForm_toComplex_eq, Pi.neg_apply, conjPoint_coord]
    simp
    ring
  · simp only [expSymbol, Set.indicator_of_notMem hp, map_zero]
theorem norm_expSymbol_second_diff_le (hform : ConeTubeLorentz.FormOnClosedCone)
    {b w : ComplexVec4} {s : ℂ} {ε : ℝ} (hε : 0 < ε) (hb : ε ≤ tubeGap b)
    (hs : ε ≤ tubeGap (b + s • w)) {p : RealVec4} (hp : p ∈ closedFutureCone) :
    ‖expSymbol (b + s • w) p - expSymbol b p - s * expDerivSymbol b w p‖ ≤
      complexEucNorm w ^ 2 * (4 / ε ^ 2) * ‖s‖ ^ 2 := by
  simp only [expSymbol, expDerivSymbol, Set.indicator_of_mem hp]
  have hz := re_I_mul_minkowskiForm_le_of_gap hform hε.le hb hp
  have hv := re_I_mul_minkowskiForm_le_of_gap hform hε.le hs hp
  have hdiff : Complex.I * minkowskiForm (b + s • w) (toComplex p) -
      Complex.I * minkowskiForm b (toComplex p) =
      s * (Complex.I * minkowskiForm w (toComplex p)) := by
    rw [minkowskiForm_add_left, minkowskiForm_smul_left]
    ring
  have hsec := norm_cexp_sub_cexp_sub_le hz hv
  rw [hdiff] at hsec
  have hassoc : s * (Complex.I * minkowskiForm w (toComplex p) *
      Complex.exp (Complex.I * minkowskiForm b (toComplex p))) =
      s * (Complex.I * minkowskiForm w (toComplex p)) *
        Complex.exp (Complex.I * minkowskiForm b (toComplex p)) := by ring
  rw [hassoc]
  refine hsec.trans ?_
  have hfw := norm_minkowskiForm_le_zeroth hform w hp
  have ht := zeroth_nonneg_of_mem_closedFutureCone hp
  have hnorm : ‖s * (Complex.I * minkowskiForm w (toComplex p))‖ =
      ‖s‖ * ‖minkowskiForm w (toComplex p)‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hdec := rexp_neg_mul_mul_sq_le hε ht
  rw [hnorm]
  calc Real.exp (-(ε * p 0)) * (‖s‖ * ‖minkowskiForm w (toComplex p)‖) ^ 2
      ≤ Real.exp (-(ε * p 0)) * (‖s‖ * (complexEucNorm w * (Real.sqrt 2 * p 0))) ^ 2 := by
        gcongr
    _ = (Real.exp (-(ε * p 0)) * p 0 ^ 2) * (2 * complexEucNorm w ^ 2 * ‖s‖ ^ 2) := by
        rw [mul_pow, mul_pow, mul_pow, hsq]
        ring
    _ ≤ (2 / ε ^ 2) * (2 * complexEucNorm w ^ 2 * ‖s‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hdec (by positivity)
    _ = _ := by ring
theorem norm_expSymbol_sub_le (hform : ConeTubeLorentz.FormOnClosedCone)
    {ζ ζ' : ComplexVec4} {ε : ℝ} (hε : 0 < ε) (hζ : ε ≤ tubeGap ζ) (hζ' : ε ≤ tubeGap ζ')
    {p : RealVec4} (hp : p ∈ closedFutureCone) :
    ‖expSymbol ζ p - expSymbol ζ' p‖ ≤ ε⁻¹ * complexEucNorm (ζ - ζ') := by
  simp only [expSymbol, Set.indicator_of_mem hp]
  have hz := re_I_mul_minkowskiForm_le_of_gap hform hε.le hζ hp
  have hz' := re_I_mul_minkowskiForm_le_of_gap hform hε.le hζ' hp
  have hfirst := norm_cexp_sub_cexp_le hz' hz
  have hdiff : Complex.I * minkowskiForm ζ (toComplex p) -
      Complex.I * minkowskiForm ζ' (toComplex p) =
      Complex.I * minkowskiForm (ζ - ζ') (toComplex p) := by
    simp only [minkowskiForm_toComplex_eq, Pi.sub_apply]
    ring
  rw [hdiff, norm_mul, Complex.norm_I, one_mul] at hfirst
  have hfw := norm_minkowskiForm_le_zeroth hform (ζ - ζ') hp
  have hw : 0 ≤ complexEucNorm (ζ - ζ') := Real.sqrt_nonneg _
  have hdec := rexp_neg_mul_mul_le_inv hε (zeroth_nonneg_of_mem_closedFutureCone hp)
  calc _ ≤ _ := hfirst
    _ ≤ Real.exp (-(ε * p 0)) * (complexEucNorm (ζ - ζ') * (Real.sqrt 2 * p 0)) :=
        mul_le_mul_of_nonneg_left hfw (Real.exp_pos _).le
    _ = (Real.exp (-(ε * p 0)) * (Real.sqrt 2 * p 0)) * complexEucNorm (ζ - ζ') := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hdec hw
theorem isBddMeasurableFun_setIndicator (Δ : FourBorelSet) :
    IsBddMeasurableFun (Δ.1.indicator fun _ => (1 : ℂ)) := by
  refine ⟨measurable_const.indicator Δ.2, 1, fun p => ?_⟩
  by_cases hp : p ∈ Δ.1
  · simp [Set.indicator_of_mem hp]
  · simp [Set.indicator_of_notMem hp]
theorem imInClosedCone_toComplex (a : RealVec4) :
    ImInClosedCone (toComplex a) := by
  have him : imPart (toComplex a) = 0 := by
    funext μ
    simp [imPart, toComplex]
  show imPart (toComplex a) ∈ closedFutureCone
  rw [him]
  exact zero_mem_closedFutureCone'
section Operators
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : FourBorelSet → BddOp K}
theorem spectralTranslation_eq_pvmIntegral (E : FourBorelSet → BddOp K) (ζ : ComplexVec4) :
    spectralTranslation E ζ = pvmIntegral E (expSymbol ζ) := rfl
theorem opNormOf_pvmIntegral_le
    (hI : PvmIntegralBasic E closedFutureConeBorel)
    {u : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u) {b : ℝ}
    (hb : ∀ p ∈ closedFutureCone, ‖u p‖ ≤ b) : opNormOf (pvmIntegral E u) ≤ b := by
  have : Nonempty closedFutureConeBorel.1 := ⟨⟨0, zero_mem_closedFutureCone'⟩⟩
  exact ((hI.1 u hu).2.2).trans (ciSup_le fun p => hb p p.2)
theorem pvmIntegral_sub
    (hI : PvmIntegralBasic E closedFutureConeBorel)
    {u u' : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u) (hu' : IsBddMeasurableFun u') :
    pvmIntegral E (fun p => u p - u' p) = pvmIntegral E u - pvmIntegral E u' := by
  have hlin := hI.2 1 (-1) u u' hu hu'
  simpa [sub_eq_add_neg] using hlin
theorem pvmIntegral_const_mul
    (hI : PvmIntegralBasic E closedFutureConeBorel) (c : ℂ)
    {u : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u) :
    pvmIntegral E (fun p => c * u p) = c • pvmIntegral E u := by
  have hlin := hI.2 c 0 u u hu hu
  simpa using hlin
theorem spectralTranslation_mul (hform : ConeTubeLorentz.FormOnClosedCone)
    (hR : PvmIntegralRules E) {ζ ζ' : ComplexVec4}
    (hζ : ImInClosedCone ζ) (hζ' : ImInClosedCone ζ') :
    spectralTranslation E ζ * spectralTranslation E ζ' = spectralTranslation E (ζ + ζ') := by
  rw [spectralTranslation_eq_pvmIntegral, spectralTranslation_eq_pvmIntegral,
    spectralTranslation_eq_pvmIntegral,
    ← hR.1 _ _ (isBddMeasurableFun_expSymbol hform hζ) (isBddMeasurableFun_expSymbol hform hζ')]
  exact congrArg _ (funext fun p => expSymbol_mul ζ ζ' p)
theorem adjointOp_spectralTranslation (hform : ConeTubeLorentz.FormOnClosedCone)
    (hR : PvmIntegralRules E) {ζ : ComplexVec4} (hζ : ImInClosedCone ζ) :
    adjointOp (spectralTranslation E ζ) = spectralTranslation E (-conjPoint ζ) := by
  rw [spectralTranslation_eq_pvmIntegral, spectralTranslation_eq_pvmIntegral,
    hR.2.1 _ (isBddMeasurableFun_expSymbol hform hζ)]
  exact congrArg _ (funext fun p => conj_expSymbol ζ p)
theorem spectralTranslation_zero
    (hI : PvmIntegralBasic E closedFutureConeBorel)
    (hR : PvmIntegralRules E) (hsupp : IsSupportedOn E closedFutureConeBorel) :
    spectralTranslation E 0 = idOp K := by
  have hin := hR.2.2.1 closedFutureConeBorel
  let outside := FourBorelSet.compl closedFutureConeBorel
  have hout := hR.2.2.1 outside
  have hadd := hI.2 1 1 _ _ (isBddMeasurableFun_setIndicator closedFutureConeBorel)
    (isBddMeasurableFun_setIndicator outside)
  have hone : (fun p => (1 : ℂ) * closedFutureConeBorel.1.indicator (fun _ => (1 : ℂ)) p +
      1 * outside.1.indicator (fun _ => (1 : ℂ)) p) =
      fun _ => (1 : ℂ) := by
    funext p
    by_cases hp : p ∈ closedFutureConeBorel.1
    · have hp' : p ∉ outside.1 := fun h => h hp
      simp [Set.indicator_of_mem hp, Set.indicator_of_notMem hp']
    · have hp' : p ∈ outside.1 := hp
      simp [Set.indicator_of_notMem hp, Set.indicator_of_mem hp']
  rw [hone, hR.2.2.2, hin, hout, hsupp] at hadd
  have hsym : expSymbol 0 = closedFutureConeBorel.1.indicator fun _ => (1 : ℂ) := by
    have hexp : (fun p : Fin 4 → ℝ => Complex.exp (Complex.I * minkowskiForm 0 (toComplex p))) =
        fun _ => (1 : ℂ) := by
      funext p
      rw [minkowskiForm_toComplex_eq]
      simp
    unfold expSymbol
    rw [hexp]
    rfl
  rw [spectralTranslation_eq_pvmIntegral, hsym, hin, hadd]
  simp
theorem spectralTranslation_apply_of_fixed (hform : ConeTubeLorentz.FormOnClosedCone)
    (hR : PvmIntegralRules E) {ζ : ComplexVec4}
    (hζ : ImInClosedCone ζ) {Ω : K} (hΩ : E originBorel Ω = Ω) :
    spectralTranslation E ζ Ω = Ω := by
  have hprod := hR.1 _ _ (isBddMeasurableFun_expSymbol hform hζ)
    (isBddMeasurableFun_setIndicator originBorel)
  have hfun : (fun p => expSymbol ζ p * originBorel.1.indicator (fun _ => (1 : ℂ)) p) =
      originBorel.1.indicator fun _ => (1 : ℂ) := by
    funext p
    by_cases h : p ∈ originBorel.1
    · have h0 : p = 0 := h
      subst h0
      have hz : minkowskiForm ζ (toComplex 0) = 0 := by
        rw [minkowskiForm_toComplex_eq]
        simp
      simp [expSymbol, Set.indicator_of_mem h, Set.indicator_of_mem zero_mem_closedFutureCone', hz]
    · simp [Set.indicator_of_notMem h]
  rw [hfun, hR.2.2.1 originBorel] at hprod
  calc spectralTranslation E ζ Ω = spectralTranslation E ζ (E originBorel Ω) := by rw [hΩ]
    _ = (spectralTranslation E ζ * E originBorel) Ω := rfl
    _ = E originBorel Ω := by
        rw [spectralTranslation_eq_pvmIntegral, ← hprod]
    _ = Ω := hΩ
theorem opNormOf_spectralTranslation_le (hform : ConeTubeLorentz.FormOnClosedCone)
    (hI : PvmIntegralBasic E closedFutureConeBorel) {ζ : ComplexVec4}
    (hζ : ImInClosedCone ζ) : opNormOf (spectralTranslation E ζ) ≤ 1 :=
  opNormOf_pvmIntegral_le hI (isBddMeasurableFun_expSymbol hform hζ) fun p hp => by
    simp only [expSymbol, Set.indicator_of_mem hp]
    exact norm_cexp_I_mul_le_one hform hζ hp
theorem isUnitaryMap_spectralTranslation (hform : ConeTubeLorentz.FormOnClosedCone)
    (hI : PvmIntegralBasic E closedFutureConeBorel)
    (hR : PvmIntegralRules E) (hsupp : IsSupportedOn E closedFutureConeBorel)
    (a : RealVec4) : IsUnitaryMap (spectralTranslation E (toComplex a) : K →ₗ[ℂ] K) := by
  have hc := imInClosedCone_toComplex
  have hsum : ∀ a : RealVec4, toComplex a + toComplex (-a) = 0 := fun a => by
    funext μ
    simp [toComplex]
  have hinv : ∀ (a : RealVec4) (ψ : K),
      spectralTranslation E (toComplex a) (spectralTranslation E (toComplex (-a)) ψ) = ψ :=
    fun a ψ => by
      have hm := spectralTranslation_mul hform hR (hc a) (hc (-a))
      rw [hsum, spectralTranslation_zero hI hR hsupp] at hm
      exact DFunLike.congr_fun hm ψ
  have hle : ∀ (b : RealVec4) (ψ : K), ‖spectralTranslation E (toComplex b) ψ‖ ≤ ‖ψ‖ :=
    fun b ψ => by
      have hop := (spectralTranslation E (toComplex b)).le_of_opNorm_le
        (opNormOf_spectralTranslation_le hform hI (hc b)) ψ
      simpa using hop
  refine ⟨fun ψ => le_antisymm (hle a ψ) ?_, fun ψ => ⟨_, hinv a ψ⟩⟩
  have hback := hle (-a) (spectralTranslation E (toComplex a) ψ)
  have hret := hinv (-a) ψ
  rw [neg_neg] at hret
  rw [hret] at hback
  exact hback
theorem stronglyContinuous_spectralTranslation
    (hform : ConeTubeLorentz.FormOnClosedCone)
    (hN : PvmIntegralNormAndConvergence E closedFutureConeBorel) :
    StronglyContinuous fun a : RealVec4 => spectralTranslation E (toComplex a) := by
  intro χ
  rw [continuous_iff_seqContinuous]
  intro τ a₀ hτ
  have hc := imInClosedCone_toComplex
  have hb : ∀ a : RealVec4, IsBddMeasurableFun (expSymbol (toComplex a)) := fun a =>
    isBddMeasurableFun_expSymbol hform (hc a)
  refine (hN.2 RealVec4 (fun a => expSymbol (toComplex a)) τ (expSymbol (toComplex a₀)) hb
    ⟨1, fun a p hp => ?_⟩ (fun p hp => ?_)).2 (hb a₀) χ
  · have hp' : p ∈ closedFutureCone := hp
    simp only [expSymbol, Set.indicator_of_mem hp']
    exact norm_cexp_I_mul_le_one hform (hc a) hp'
  · have hp' : p ∈ closedFutureCone := hp
    simp only [expSymbol, Set.indicator_of_mem hp']
    have hf : Continuous fun a : RealVec4 =>
        Complex.exp (Complex.I * minkowskiForm (toComplex a) (toComplex p)) := by
      simp only [minkowskiForm_toComplex_eq, toComplex]
      fun_prop
    exact (hf.tendsto a₀).comp hτ
theorem lipschitzInTube_of (hform : ConeTubeLorentz.FormOnClosedCone)
    (hI : PvmIntegralBasic E closedFutureConeBorel) :
    LipschitzInTube E := by
  intro ζ ζ' ε hζ hζ' hε h h'
  rw [spectralTranslation_eq_pvmIntegral, spectralTranslation_eq_pvmIntegral,
    ← pvmIntegral_sub hI (isBddMeasurableFun_expSymbol hform hζ)
      (isBddMeasurableFun_expSymbol hform hζ')]
  exact opNormOf_pvmIntegral_le hI
    (isBddMeasurableFun_sub (isBddMeasurableFun_expSymbol hform hζ)
      (isBddMeasurableFun_expSymbol hform hζ'))
    fun p hp => norm_expSymbol_sub_le hform hε h h' hp
theorem imInClosedCone_of_gap {ζ : ComplexVec4} {ε : ℝ} (hε : 0 < ε)
    (h : ε ≤ tubeGap ζ) : ImInClosedCone ζ := by
  show coneGap (imPart ζ) ≥ 0
  exact hε.le.trans h
theorem continuousOn_spectralTranslation (hL : LipschitzInTube E) :
    ContinuousOn (spectralTranslation E) futureTube := by
  intro ζ₀ h₀
  have hm : 0 < tubeGap ζ₀ := h₀
  have hε : 0 < tubeGap ζ₀ / 2 := by positivity
  have hlt : tubeGap ζ₀ / 2 < tubeGap ζ₀ := by linarith
  have hev : ∀ᶠ ζ in 𝓝 ζ₀, tubeGap ζ₀ / 2 ≤ tubeGap ζ :=
    (tubeGap_continuous.tendsto ζ₀).eventually (Ioi_mem_nhds hlt) |>.mono fun _ h => le_of_lt h
  have hc : Continuous fun ζ => (tubeGap ζ₀ / 2)⁻¹ * complexEucNorm (ζ - ζ₀) :=
    continuous_const.mul (complexEucNorm_continuous.comp (continuous_id.sub continuous_const))
  have hlim : Tendsto (fun ζ => (tubeGap ζ₀ / 2)⁻¹ * complexEucNorm (ζ - ζ₀)) (𝓝 ζ₀) (𝓝 0) := by
    simpa [complexEucNorm] using hc.tendsto ζ₀
  have hT : Tendsto (spectralTranslation E) (𝓝 ζ₀) (𝓝 (spectralTranslation E ζ₀)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (hev.mono fun ζ h => ?_) hlim)
    exact hL ζ ζ₀ _ (imInClosedCone_of_gap hε h)
      (imInClosedCone_of_gap hε (by linarith)) hε h (by linarith)
  exact ContinuousAt.continuousWithinAt hT
theorem hasDerivAt_spectralTranslation_line (hform : ConeTubeLorentz.FormOnClosedCone)
    (hI : PvmIntegralBasic E closedFutureConeBorel) {b : ComplexVec4}
    (hb : b ∈ futureTube) (w : ComplexVec4) :
    HasDerivAt (fun s : ℂ => spectralTranslation E (b + s • w))
      (pvmIntegral E (expDerivSymbol b w)) 0 := by
  have hm : 0 < tubeGap b := hb
  have hε : 0 < tubeGap b / 2 := by positivity
  have hle : tubeGap b / 2 ≤ tubeGap b := by linarith
  have hc : Continuous fun s : ℂ => tubeGap (b + s • w) :=
    tubeGap_continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hev : ∀ᶠ s : ℂ in 𝓝 0, tubeGap b / 2 ≤ tubeGap (b + s • w) := by
    have hlt : tubeGap b / 2 < tubeGap (b + (0 : ℂ) • w) := by
      rw [zero_smul, add_zero]
      linarith
    exact ((hc.tendsto 0).eventually (Ioi_mem_nhds hlt)).mono fun _ h => le_of_lt h
  rw [hasDerivAt_iff_isLittleO]
  simp only [zero_smul, add_zero, sub_zero]
  have hD := isBddMeasurableFun_expDerivSymbol hform w hε hle
  have hB := isBddMeasurableFun_expSymbol hform (imInClosedCone_of_gap hε hle)
  have hO : (fun s : ℂ => spectralTranslation E (b + s • w) - spectralTranslation E b -
      s • pvmIntegral E (expDerivSymbol b w)) =O[𝓝 0] fun s : ℂ => s ^ 2 := by
    refine IsBigO.of_bound (complexEucNorm w ^ 2 * (4 / (tubeGap b / 2) ^ 2)) (hev.mono ?_)
    intro s hs
    have hS := isBddMeasurableFun_expSymbol hform (imInClosedCone_of_gap hε hs)
    rw [spectralTranslation_eq_pvmIntegral, spectralTranslation_eq_pvmIntegral,
      ← pvmIntegral_const_mul hI s hD, ← pvmIntegral_sub hI hS hB,
      ← pvmIntegral_sub hI (isBddMeasurableFun_sub hS hB) (isBddMeasurableFun_const_mul s hD),
      norm_pow]
    exact opNormOf_pvmIntegral_le hI
      (isBddMeasurableFun_sub (isBddMeasurableFun_sub hS hB) (isBddMeasurableFun_const_mul s hD))
      fun p hp => norm_expSymbol_second_diff_le hform hε hle hs hp
  exact hO.trans_isLittleO (isLittleO_pow_id one_lt_two)
theorem holomorphicMatrixCoeffs_of (hform : ConeTubeLorentz.FormOnClosedCone)
    (hI : PvmIntegralBasic E closedFutureConeBorel) :
    HolomorphicMatrixCoeffs E := by
  intro χ χ'
  let L : BddOp K →L[ℂ] ℂ := (innerSL ℂ χ).comp (ContinuousLinearMap.apply ℂ K χ')
  have hT := continuousOn_spectralTranslation (lipschitzInTube_of hform hI)
  refine ⟨futureTube_isOpen, continuousOn_pi.mpr fun _ => L.continuous.comp_continuousOn hT,
    fun a ha j => ?_⟩
  have hcont : Continuous fun s : ℂ => a + s • Coordinates.ComplexCoordinates.stdBasisVector j :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hopen : ∀ᶠ s : ℂ in 𝓝 0,
      a + s • Coordinates.ComplexCoordinates.stdBasisVector j ∈ futureTube := by
    refine (hcont.tendsto 0).eventually (futureTube_isOpen.mem_nhds ?_)
    simpa using ha
  filter_upwards [hopen] with s hs
  have hd := hasDerivAt_spectralTranslation_line hform hI hs
    (Coordinates.ComplexCoordinates.stdBasisVector j)
  have hd₂ : HasDerivAt
      (fun r : ℂ => spectralTranslation E (a + r • Coordinates.ComplexCoordinates.stdBasisVector j))
      (pvmIntegral E (expDerivSymbol (a + s • Coordinates.ComplexCoordinates.stdBasisVector j)
        (Coordinates.ComplexCoordinates.stdBasisVector j))) s := by
    have hshift := HasDerivAt.comp_sub_const s s (by simpa using hd)
    refine hshift.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
    have hline : a + s • Coordinates.ComplexCoordinates.stdBasisVector j +
        (r - s) • Coordinates.ComplexCoordinates.stdBasisVector j =
        a + r • Coordinates.ComplexCoordinates.stdBasisVector j := by
      rw [sub_smul]
      abel
    simp only [hline]
  exact differentiableAt_pi.mpr fun _ => L.differentiableAt.comp s hd₂.differentiableAt
end Operators
theorem translationOperatorFacts_holds (hcalc : PVMCalculus.BoundedFunctionalCalculus)
    (hcone : MinkowskiSpace.ConeTubeLorentz.Statement) : TranslationOperatorFacts := by
  intro K _ _ _ E Ω A ℘ C hb
  obtain ⟨-, -, hform, -⟩ := hcone
  obtain ⟨-, hH⟩ := hcalc
  obtain ⟨-, hE⟩ := hH K
  obtain ⟨-, hI, hR, hN, -⟩ := hE E closedFutureConeBorel hb.isPVM hb.supportedOn
  refine ⟨⟨fun ζ ζ' hζ hζ' => ⟨opNormOf_spectralTranslation_le hform hI hζ,
      spectralTranslation_mul hform hR hζ hζ', adjointOp_spectralTranslation hform hR hζ,
      spectralTranslation_zero hI hR hb.supportedOn,
      spectralTranslation_apply_of_fixed hform hR hζ hb.origin_fixes⟩,
    isUnitaryMap_spectralTranslation hform hI hR hb.supportedOn,
    stronglyContinuous_spectralTranslation hform hN⟩,
    lipschitzInTube_of hform hI, holomorphicMatrixCoeffs_of hform hI⟩
end YangMills.Construction.FieldFormTranslations
