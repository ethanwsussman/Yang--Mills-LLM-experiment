import YangMills.Construction.Towers.PowersOfTheMassivePropagatorProof
import YangMills.Construction.PeriodicOperators.AdditivityAndIntegralOfTheLogarithmicNumberProof
import YangMills.Construction.PeriodicOperators.SymbolOfTheKernelOfAMatrixFunctionProof
import YangMills.Construction.Towers.TracesOfTheParametrixOverTheHalfLine
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (torusAverage toComplexVec)
open Matrices.RectangularMatrix (diagSum)
namespace Tower.MagneticWeyl.HalfLineTrace
open FluxExpansion
abbrev box : Set AmbientSpace := Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi)
theorem isCompact_box : IsCompact box := isCompact_Icc
theorem integrableOn_box {g : AmbientSpace → ℂ} (hg : Continuous g) : IntegrableOn g box :=
  hg.continuousOn.integrableOn_compact isCompact_box
theorem volume_real_box : volume.real box = (2 * Real.pi) ^ 4 := by apply _root_.YangMills.Construction.Tower.MassivePropagator.volume_real_brillouinZone <;> assumption
theorem average_add {f g : AmbientSpace → ℂ} (hf : Continuous f) (hg : Continuous g) :
    (torusAverage fun q => f q + g q) = torusAverage f + torusAverage g := by apply _root_.YangMills.SharedProofs.p18494 <;> assumption
theorem average_sub {f g : AmbientSpace → ℂ} (hf : Continuous f) (hg : Continuous g) :
    (torusAverage fun q => f q - g q) = torusAverage f - torusAverage g := by
  unfold torusAverage
  rw [integral_sub (integrableOn_box hf) (integrableOn_box hg)]
  ring
theorem average_const_mul (c : ℂ) (f : AmbientSpace → ℂ) :
    (torusAverage fun q => c * f q) = c * torusAverage f := by apply _root_.YangMills.Construction.PeriodicOperators.KernelSymbol.torusAverage_const_mul <;> assumption
theorem average_mul_const (c : ℂ) (f : AmbientSpace → ℂ) :
    (torusAverage fun q => f q * c) = torusAverage f * c := by
  simpa [mul_comm] using average_const_mul c f
theorem average_const (c : ℂ) : (torusAverage fun _ => c) = c := by
  unfold torusAverage
  rw [setIntegral_const, volume_real_box]
  have h : (2 * Real.pi) ≠ 0 := by positivity
  simp only [Complex.real_smul]
  push_cast
  field_simp
theorem norm_average_le {g : AmbientSpace → ℂ} {C : ℝ} (hC : ∀ q ∈ box, ‖g q‖ ≤ C) :
    ‖torusAverage g‖ ≤ C := by
  unfold torusAverage
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := box) (C := C)
    isCompact_box.measure_lt_top hC
  rw [volume_real_box] at h
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc ((2 * Real.pi) ^ 4)⁻¹ * _ ≤ ((2 * Real.pi) ^ 4)⁻¹ * (C * (2 * Real.pi) ^ 4) := by gcongr
    _ = C := by field_simp
theorem continuous_average {f : ℝ → AmbientSpace → ℂ} (hf : Continuous (Function.uncurry f)) :
    Continuous fun w => torusAverage (f w) := by
  unfold torusAverage
  exact continuous_const.mul (continuous_parametric_integral_of_continuous hf isCompact_box)
theorem intervalIntegral_average_comm {f : ℝ → AmbientSpace → ℂ}
    (hf : Continuous (Function.uncurry f)) {y : ℝ} (hy : 0 ≤ y) :
    (∫ w in (0 : ℝ)..y, torusAverage (f w)) = torusAverage fun q => ∫ w in (0 : ℝ)..y, f w q := by
  unfold torusAverage
  rw [intervalIntegral.integral_const_mul]
  congr 1
  simp_rw [intervalIntegral.integral_of_le hy]
  refine integral_integral_swap ?_
  rw [Measure.prod_restrict]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_box)).mono_set
    (prod_mono Ioc_subset_Icc_self subset_rfl)
def baseSymbolReal (q : AmbientSpace) : ℝ := ∑ μ, (2 - 2 * Real.cos (q μ))
theorem baseSymbol_eq_ofReal (q : AmbientSpace) : baseSymbol q = (baseSymbolReal q : ℂ) := by
  simp [baseSymbol, baseSymbolReal, Massive.latticeSymbol, Massive.axisSymbol, toComplexVec]
theorem baseSymbolReal_nonneg (q : AmbientSpace) : 0 ≤ baseSymbolReal q :=
  Finset.sum_nonneg fun μ _ => by linarith [Real.cos_le_one (q μ)]
theorem baseSymbolReal_le_sixteen (q : AmbientSpace) : baseSymbolReal q ≤ 16 := by
  have h : baseSymbolReal q ≤ ∑ _μ : Fin 4, (4 : ℝ) :=
    Finset.sum_le_sum fun μ _ => by linarith [Real.neg_one_le_cos (q μ)]
  simpa using h.trans (by norm_num)
theorem continuous_baseSymbolReal : Continuous baseSymbolReal := by
  unfold baseSymbolReal
  fun_prop
def shiftedInverseReal (s : ℝ) (q : AmbientSpace) : ℝ := (baseSymbolReal q + s)⁻¹
theorem shiftedInverse_eq_ofReal (s : ℝ) (q : AmbientSpace) :
    shiftedInverse s q = (shiftedInverseReal s q : ℂ) := by
  simp [shiftedInverse, shiftedInverseReal, baseSymbol_eq_ofReal]
theorem baseSymbolReal_add_pos {s : ℝ} (hs : 0 < s) (q : AmbientSpace) : 0 < baseSymbolReal q + s := by
  linarith [baseSymbolReal_nonneg q]
theorem continuous_shiftedInverseReal_clamped {z : ℝ} (hz : 0 < z) :
    Continuous fun p : ℝ × AmbientSpace => shiftedInverseReal (z + max p.1 0) p.2 := by
  unfold shiftedInverseReal
  refine Continuous.inv₀ ?_ fun p => ?_
  · have := continuous_baseSymbolReal
    fun_prop
  · exact (baseSymbolReal_add_pos (by linarith [le_max_right p.1 0]) _).ne'
theorem continuous_shiftedInverse {z : ℝ} (hz : 0 < z) : Continuous (shiftedInverse z) := by
  have h := (continuous_shiftedInverseReal_clamped hz).comp (continuous_const.prodMk continuous_id :
    Continuous fun q : AmbientSpace => ((0 : ℝ), q))
  have h' : shiftedInverse z = fun q => ((shiftedInverseReal (z + max 0 0) q : ℝ) : ℂ) := by
    funext q
    simp [shiftedInverse_eq_ofReal]
  rw [h']
  exact Complex.continuous_ofReal.comp h
theorem continuous_baseSymbolDeriv (μ : Fin 4) : Continuous (baseSymbolDeriv μ) := by
  unfold baseSymbolDeriv
  have : Continuous fun q : AmbientSpace => ((q μ : ℝ) : ℂ) := by fun_prop
  exact continuous_const.mul (Complex.continuous_sin.comp this)
theorem continuous_baseSymbolSecondDeriv (μ : Fin 4) : Continuous (baseSymbolSecondDeriv μ) := by
  unfold baseSymbolSecondDeriv
  have : Continuous fun q : AmbientSpace => ((q μ : ℝ) : ℂ) := by fun_prop
  exact continuous_const.mul (Complex.continuous_cos.comp this)
theorem integral_inv_add_pow {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 ≤ y) (k : ℕ) :
    (∫ w in (0 : ℝ)..y, ((a + w)⁻¹) ^ (k + 2)) =
      ((a⁻¹) ^ (k + 1) - ((a + y)⁻¹) ^ (k + 1)) / ((k : ℝ) + 1) := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have hd : ∀ w ∈ uIcc (0 : ℝ) y, HasDerivAt (fun w => -((a + w)⁻¹) ^ (k + 1) / ((k : ℝ) + 1))
      (((a + w)⁻¹) ^ (k + 2)) w := by
    intro w hw
    rw [uIcc_of_le hy] at hw
    have hne : a + w ≠ 0 := by linarith [hw.1]
    have h0 : HasDerivAt (fun w => (a + w)⁻¹) (-1 / (a + w) ^ 2) w :=
      ((hasDerivAt_id w).const_add a).inv hne
    have h1 : HasDerivAt (fun w => (a + w)⁻¹) (-((a + w)⁻¹) ^ 2) w :=
      h0.congr_deriv (by field_simp)
    have h2 : HasDerivAt (fun w => -((a + w)⁻¹) ^ (k + 1) / ((k : ℝ) + 1)) _ w :=
      (h1.pow (k + 1)).neg.div_const ((k : ℝ) + 1)
    refine h2.congr_deriv ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    generalize (a + w)⁻¹ = x
    field_simp
    try ring
  have hc : ContinuousOn (fun w => ((a + w)⁻¹) ^ (k + 2)) (uIcc (0 : ℝ) y) := by
    refine ContinuousOn.pow (ContinuousOn.inv₀ (by fun_prop) fun w hw => ?_) _
    rw [uIcc_of_le hy] at hw
    linarith [hw.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp only [add_zero]
  field_simp
  ring
theorem integral_inv_sub_inv {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 ≤ y) :
    (∫ w in (0 : ℝ)..y, ((1 + w)⁻¹ - (a + w)⁻¹)) =
      Real.log (1 + y) - Real.log (a + y) + Real.log a := by
  have hd : ∀ w ∈ uIcc (0 : ℝ) y, HasDerivAt (fun w => Real.log (1 + w) - Real.log (a + w))
      ((1 + w)⁻¹ - (a + w)⁻¹) w := by
    intro w hw
    rw [uIcc_of_le hy] at hw
    have h1 : 1 + w ≠ 0 := by linarith [hw.1]
    have h2 : a + w ≠ 0 := by linarith [hw.1]
    have h : HasDerivAt (fun w => Real.log (1 + w) - Real.log (a + w)) (1 / (1 + w) - 1 / (a + w)) w :=
      (((hasDerivAt_id w).const_add 1).log h1).sub (((hasDerivAt_id w).const_add a).log h2)
    exact h.congr_deriv (by simp [one_div])
  have hc : ContinuousOn (fun w => (1 + w)⁻¹ - (a + w)⁻¹) (uIcc (0 : ℝ) y) := by
    refine ContinuousOn.sub (ContinuousOn.inv₀ (by fun_prop) fun w hw => ?_)
      (ContinuousOn.inv₀ (by fun_prop) fun w hw => ?_) <;> rw [uIcc_of_le hy] at hw <;>
      linarith [hw.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp
theorem abs_log_sub_log_le {a b y : ℝ} (hy : 0 < y) (ha : y ≤ a) (hb : y ≤ b) {C : ℝ}
    (hC : |a - b| ≤ C) : |Real.log a - Real.log b| ≤ C / y := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have h1 : Real.log a - Real.log b ≤ C / y := by
    rw [← Real.log_div ha0.ne' hb0.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    have h2 : a / b - 1 = (a - b) / b := by field_simp
    have h3 : (a - b) / b ≤ C / y := by
      have hC0 : 0 ≤ C := (abs_nonneg _).trans hC
      calc (a - b) / b ≤ C / b := by gcongr; exact (le_abs_self _).trans hC
        _ ≤ C / y := by gcongr
    linarith
  have h2 : Real.log b - Real.log a ≤ C / y := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    have h2 : b / a - 1 = (b - a) / a := by field_simp
    have h3 : (b - a) / a ≤ C / y := by
      have hC0 : 0 ≤ C := (abs_nonneg _).trans hC
      calc (b - a) / a ≤ C / a := by gcongr; exact (neg_le_abs (a - b)).trans' (by linarith) |>.trans hC
        _ ≤ C / y := by gcongr
    linarith
  exact abs_le.mpr ⟨by linarith, h1⟩
section Powers
variable {z : ℝ} (hz : 0 < z) {A : AmbientSpace → ℂ} (hA : Continuous A)
include hz hA
theorem continuous_clamped_pow_mul (k : ℕ) :
    Continuous (Function.uncurry fun (w : ℝ) (q : AmbientSpace) =>
      ((shiftedInverseReal (z + max w 0) q : ℝ) : ℂ) ^ k * A q) := by
  have h := continuous_shiftedInverseReal_clamped hz
  have h' : Continuous fun p : ℝ × AmbientSpace => ((shiftedInverseReal (z + max p.1 0) p.2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp h
  exact (h'.pow k).mul (hA.comp continuous_snd)
omit hz hA in
theorem average_pow_mul_eq_clamped (k : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    (torusAverage fun q => shiftedInverse (z + w) q ^ k * A q) =
      torusAverage fun q => ((shiftedInverseReal (z + max w 0) q : ℝ) : ℂ) ^ k * A q := by
  simp only [max_eq_left hw, shiftedInverse_eq_ofReal]
theorem continuousOn_average_pow_mul (k : ℕ) :
    ContinuousOn (fun w : ℝ => torusAverage fun q => shiftedInverse (z + w) q ^ k * A q) (Ici 0) :=
  (continuous_average (continuous_clamped_pow_mul hz hA k)).continuousOn.congr
    fun _ hw => average_pow_mul_eq_clamped k hw
theorem intervalIntegrable_average_pow_mul (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    IntervalIntegrable (fun w : ℝ => torusAverage fun q => shiftedInverse (z + w) q ^ k * A q)
      volume 0 y :=
  ((continuousOn_average_pow_mul hz hA k).mono (by
    rw [uIcc_of_le hy]
    exact Icc_subset_Ici_self)).intervalIntegrable
omit hz in
theorem continuous_pow_mul (k : ℕ) {s : ℝ} (hs : 0 < s) :
    Continuous fun q => shiftedInverse s q ^ k * A q :=
  ((continuous_shiftedInverse hs).pow k).mul hA
theorem integral_average_pow_mul (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (∫ w in (0 : ℝ)..y, torusAverage fun q => shiftedInverse (z + w) q ^ (k + 2) * A q) =
      ((torusAverage fun q => shiftedInverse z q ^ (k + 1) * A q) -
        torusAverage fun q => shiftedInverse (z + y) q ^ (k + 1) * A q) / ((k : ℂ) + 1) := by
  have h1 : (∫ w in (0 : ℝ)..y, torusAverage fun q => shiftedInverse (z + w) q ^ (k + 2) * A q) =
      ∫ w in (0 : ℝ)..y, torusAverage fun q =>
        ((shiftedInverseReal (z + max w 0) q : ℝ) : ℂ) ^ (k + 2) * A q := by
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [uIcc_of_le hy] at hw
    exact average_pow_mul_eq_clamped _ hw.1
  rw [h1, intervalIntegral_average_comm (continuous_clamped_pow_mul hz hA (k + 2)) hy]
  have h2 : (fun q => ∫ w in (0 : ℝ)..y,
      ((shiftedInverseReal (z + max w 0) q : ℝ) : ℂ) ^ (k + 2) * A q) =
      fun q => (shiftedInverse z q ^ (k + 1) * A q - shiftedInverse (z + y) q ^ (k + 1) * A q) *
        ((k : ℂ) + 1)⁻¹ := by
    funext q
    rw [intervalIntegral.integral_mul_const]
    have hp := baseSymbolReal_add_pos hz q
    have h3 : (∫ w in (0 : ℝ)..y, ((shiftedInverseReal (z + max w 0) q : ℝ) : ℂ) ^ (k + 2)) =
        (((∫ w in (0 : ℝ)..y, ((baseSymbolReal q + z + w)⁻¹) ^ (k + 2)) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun w hw => ?_
      rw [uIcc_of_le hy] at hw
      simp only [shiftedInverseReal, max_eq_left hw.1, add_assoc]
      push_cast
      rfl
    rw [h3, integral_inv_add_pow hp hy, shiftedInverse_eq_ofReal, shiftedInverse_eq_ofReal]
    simp only [shiftedInverseReal, add_assoc]
    push_cast
    ring
  rw [h2, average_mul_const, average_sub (continuous_pow_mul hA _ hz)
    (continuous_pow_mul hA _ (by linarith)), div_eq_mul_inv]
theorem tendsto_average_pow_mul_zero (k : ℕ) :
    Tendsto (fun y : ℝ => torusAverage fun q => shiftedInverse (z + y) q ^ (k + 1) * A q) atTop
      (nhds 0) := by
  obtain ⟨M, hM⟩ := isCompact_box.exists_bound_of_continuousOn hA.continuousOn
  have hlim : Tendsto (fun y : ℝ => ((z + y)⁻¹) ^ (k + 1) * M) atTop (nhds 0) := by
    have h1 : Tendsto (fun y : ℝ => (z + y)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ z tendsto_id)
    simpa using (h1.pow (k + 1)).mul_const M
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with y hy
  refine norm_average_le fun q hq => ?_
  have hs : 0 < z + y := by linarith
  have hp := baseSymbolReal_add_pos hs q
  have hu : ‖shiftedInverse (z + y) q‖ ≤ (z + y)⁻¹ := by
    rw [shiftedInverse_eq_ofReal, Complex.norm_real, shiftedInverseReal,
      Real.norm_of_nonneg (by positivity)]
    exact inv_anti₀ hs (by linarith [baseSymbolReal_nonneg q])
  rw [norm_mul, norm_pow]
  have hMq := hM q hq
  gcongr
theorem tendsto_integral_average_pow_mul (k : ℕ) :
    Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y,
        torusAverage fun q => shiftedInverse (z + w) q ^ (k + 2) * A q)
      atTop (nhds ((torusAverage fun q => shiftedInverse z q ^ (k + 1) * A q) / ((k : ℂ) + 1))) := by
  have h := ((tendsto_average_pow_mul_zero hz hA k).const_sub
    (torusAverage fun q => shiftedInverse z q ^ (k + 1) * A q)).div_const ((k : ℂ) + 1)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with y hy
  exact (integral_average_pow_mul hz hA k hy).symm
end Powers
theorem tendsto_integral_log {z : ℝ} (hz : 0 < z) (N : ℂ) :
    Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y, (N * (((1 + w)⁻¹ : ℝ) : ℂ) -
        torusAverage fun q => shiftedInverse (z + w) q ^ 1 * N)) atTop
      (nhds (N * torusAverage fun q => ((Real.log (baseSymbolReal q + z) : ℝ) : ℂ))) := by
  have hD : Continuous (Function.uncurry fun (w : ℝ) (q : AmbientSpace) =>
      (((1 + max w 0)⁻¹ - shiftedInverseReal (z + max w 0) q : ℝ) : ℂ)) := by
    have h1 : Continuous fun p : ℝ × AmbientSpace => (1 + max p.1 0)⁻¹ := by
      refine Continuous.inv₀ (by fun_prop) fun p => ?_
      have := le_max_right p.1 0
      linarith
    exact Complex.continuous_ofReal.comp (h1.sub (continuous_shiftedInverseReal_clamped hz))
  have hlog : Continuous fun q => ((Real.log (baseSymbolReal q + z) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      ((continuous_baseSymbolReal.add continuous_const).log fun q =>
        (baseSymbolReal_add_pos hz q).ne')
  have hrest : ∀ y : ℝ, 0 ≤ y → Continuous fun q =>
      ((Real.log (1 + y) - Real.log (baseSymbolReal q + z + y) : ℝ) : ℂ) := fun y hy =>
    Complex.continuous_ofReal.comp (continuous_const.sub
      (((continuous_baseSymbolReal.add continuous_const).add continuous_const).log fun q =>
        (by linarith [baseSymbolReal_add_pos hz q] : baseSymbolReal q + z + y ≠ 0) ))
  have key : ∀ y : ℝ, 0 ≤ y → (∫ w in (0 : ℝ)..y, (N * (((1 + w)⁻¹ : ℝ) : ℂ) -
      torusAverage fun q => shiftedInverse (z + w) q ^ 1 * N)) =
      N * (torusAverage fun q => ((Real.log (baseSymbolReal q + z) : ℝ) : ℂ)) +
        N * torusAverage fun q =>
          ((Real.log (1 + y) - Real.log (baseSymbolReal q + z + y) : ℝ) : ℂ) := by
    intro y hy
    have h1 : (∫ w in (0 : ℝ)..y, (N * (((1 + w)⁻¹ : ℝ) : ℂ) -
        torusAverage fun q => shiftedInverse (z + w) q ^ 1 * N)) =
        ∫ w in (0 : ℝ)..y, N * torusAverage fun q =>
          (((1 + max w 0)⁻¹ - shiftedInverseReal (z + max w 0) q : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr fun w hw => ?_
      rw [uIcc_of_le hy] at hw
      have hw0 : 0 ≤ w := hw.1
      have hs : 0 < z + w := by linarith
      simp only [max_eq_left hw0]
      have hc : Continuous fun q => ((shiftedInverseReal (z + w) q : ℝ) : ℂ) := by
        have : (fun q => ((shiftedInverseReal (z + w) q : ℝ) : ℂ)) = shiftedInverse (z + w) := by
          funext q
          rw [shiftedInverse_eq_ofReal]
        rw [this]
        exact continuous_shiftedInverse hs
      have e1 : (fun q => (((1 + w)⁻¹ - shiftedInverseReal (z + w) q : ℝ) : ℂ)) =
          fun q => (((1 + w)⁻¹ : ℝ) : ℂ) - ((shiftedInverseReal (z + w) q : ℝ) : ℂ) := by
        funext q
        push_cast
        rfl
      have e2 : (fun q => shiftedInverse (z + w) q ^ 1 * N) =
          fun q => ((shiftedInverseReal (z + w) q : ℝ) : ℂ) * N := by
        funext q
        rw [shiftedInverse_eq_ofReal, pow_one]
      rw [e1, e2, average_sub continuous_const hc, average_const, average_mul_const]
      ring
    rw [h1, intervalIntegral.integral_const_mul, intervalIntegral_average_comm hD hy, ← mul_add,
      ← average_add hlog (hrest y hy)]
    congr 2
    funext q
    have hp := baseSymbolReal_add_pos hz q
    have h3 : (∫ w in (0 : ℝ)..y,
        (((1 + max w 0)⁻¹ - shiftedInverseReal (z + max w 0) q : ℝ) : ℂ)) =
        (((∫ w in (0 : ℝ)..y, ((1 + w)⁻¹ - (baseSymbolReal q + z + w)⁻¹)) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun w hw => ?_
      rw [uIcc_of_le hy] at hw
      simp only [shiftedInverseReal, max_eq_left hw.1, add_assoc]
    rw [h3, integral_inv_sub_inv hp hy]
    push_cast
    ring
  have hlim : Tendsto (fun y : ℝ => (17 + z) / y) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hzero : Tendsto (fun y : ℝ => torusAverage fun q =>
      ((Real.log (1 + y) - Real.log (baseSymbolReal q + z + y) : ℝ) : ℂ)) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with y hy
    refine norm_average_le fun q _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine abs_log_sub_log_le hy (by linarith) (by linarith [baseSymbolReal_add_pos hz q]) ?_
    rw [abs_le]
    constructor <;> linarith [baseSymbolReal_le_sixteen q, baseSymbolReal_nonneg q]
  have h := (hzero.const_mul N).const_add
    (N * torusAverage fun q => ((Real.log (baseSymbolReal q + z) : ℝ) : ℂ))
  rw [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with y hy
  exact (key y hy).symm
def fluxField (z : ℝ) (μ ν : Fin 4) (q : AmbientSpace) : ℝ :=
  shiftedInverseReal z q * shiftedInverseReal z q * (2 * Real.sin (q μ)) * (2 * Real.cos (q ν))
def fluxFieldDiv (z : ℝ) (μ ν : Fin 4) (q : AmbientSpace) : ℝ :=
  shiftedInverseReal z q ^ 2 * ((2 * Real.cos (q μ)) * (2 * Real.cos (q ν))) -
    2 * (shiftedInverseReal z q ^ 3 * ((2 * Real.sin (q μ)) ^ 2 * (2 * Real.cos (q ν))))
theorem hasFDerivAt_baseSymbolReal (q : AmbientSpace) : HasFDerivAt baseSymbolReal
    (∑ i, (2 * Real.sin (q i)) • (ContinuousLinearMap.proj i : AmbientSpace →L[ℝ] ℝ)) q := by
  unfold baseSymbolReal
  refine HasFDerivAt.fun_sum fun i _ => ?_
  have h : HasFDerivAt (fun q : AmbientSpace => 2 - 2 * Real.cos (q i)) _ q :=
    (((hasFDerivAt_apply i q).cos).const_mul 2).const_sub 2
  refine h.congr_fderiv ?_
  ext v
  simp
  ring
theorem hasFDerivAt_fluxField {z : ℝ} (hz : 0 < z) {μ ν : Fin 4} (hμν : μ ≠ ν) (q : AmbientSpace) :
    ∃ L : AmbientSpace →L[ℝ] ℝ, HasFDerivAt (fluxField z μ ν) L q ∧
      L (Pi.single μ 1) = fluxFieldDiv z μ ν q := by
  have hne : baseSymbolReal q + z ≠ 0 := (baseSymbolReal_add_pos hz q).ne'
  have hu : HasFDerivAt (shiftedInverseReal z) _ q :=
    (hasDerivAt_inv hne).comp_hasFDerivAt q ((hasFDerivAt_baseSymbolReal q).add_const z)
  have ha : HasFDerivAt (fun q : AmbientSpace => 2 * Real.sin (q μ)) _ q :=
    ((hasFDerivAt_apply μ q).sin).const_mul 2
  have hb : HasFDerivAt (fun q : AmbientSpace => 2 * Real.cos (q ν)) _ q :=
    ((hasFDerivAt_apply ν q).cos).const_mul 2
  refine ⟨_, ((hu.mul hu).mul ha).mul hb, ?_⟩
  have hsum : (∑ i, (2 * Real.sin (q i)) • (ContinuousLinearMap.proj i : AmbientSpace →L[ℝ] ℝ))
      (Pi.single μ 1) = 2 * Real.sin (q μ) := by
    simp [Pi.single_apply]
  have hν : (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ν = 0 := by
    simp [hμν.symm]
  have e : ((baseSymbolReal q + z) ^ 2)⁻¹ = shiftedInverseReal z q ^ 2 := by
    simp [shiftedInverseReal, inv_pow]
  simp [hsum, hν]
  rw [e]
  unfold fluxFieldDiv
  ring
theorem continuous_shiftedInverseReal {z : ℝ} (hz : 0 < z) : Continuous (shiftedInverseReal z) := by
  unfold shiftedInverseReal
  exact (continuous_baseSymbolReal.add continuous_const).inv₀ fun q =>
    (baseSymbolReal_add_pos hz q).ne'
theorem integral_fluxFieldDiv_eq_zero {z : ℝ} (hz : 0 < z) {μ ν : Fin 4} (hμν : μ ≠ ν) :
    ∫ q in box, fluxFieldDiv z μ ν q = 0 := by
  choose L hL hL' using hasFDerivAt_fluxField hz hμν
  have hcont : Continuous (fluxField z μ ν) :=
    continuous_iff_continuousAt.2 fun q => (hL q).continuousAt
  have hdc : Continuous (fluxFieldDiv z μ ν) := by
    have := continuous_shiftedInverseReal hz
    unfold fluxFieldDiv
    fun_prop
  let f : AmbientSpace → Fin 4 → ℝ := fun q => Pi.single μ (fluxField z μ ν q)
  let f' : AmbientSpace → AmbientSpace →L[ℝ] Fin 4 → ℝ := fun q =>
    (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => ℝ) μ).comp (L q)
  have hsum : ∀ q, ∑ i, f' q (Pi.single i 1) i = fluxFieldDiv z μ ν q := by
    intro q
    rw [← hL' q]
    simp [f', Pi.single_apply]
  have hf : Continuous f :=
    (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => ℝ) μ).continuous.comp hcont
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable (fun _ : Fin 4 => -Real.pi)
    (fun _ => Real.pi) (fun _ => by linarith [Real.pi_pos]) f f' ∅ countable_empty hf.continuousOn
    (fun q _ => (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => ℝ) μ).hasFDerivAt.comp q (hL q))
    (by
      simp_rw [hsum]
      exact hdc.continuousOn.integrableOn_compact isCompact_box)
  simp_rw [hsum] at hdiv
  rw [hdiv]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hb : ∀ c : ℝ, Real.sin c = 0 → ∀ x : Fin 3 → ℝ, f (Fin.insertNth i c x) i = 0 := by
    intro c hc x
    by_cases h : i = μ
    · subst h
      simp [f, fluxField, hc]
    · simp [f, h]
  have hπ : Real.sin (-Real.pi) = 0 := by simp
  simp only [hb _ Real.sin_pi, hb _ hπ]
  simp
theorem average_neg (f : AmbientSpace → ℂ) : (torusAverage fun q => -f q) = -torusAverage f := by
  simpa using average_const_mul (-1) f
theorem average_by_parts {z : ℝ} (hz : 0 < z) {μ ν : Fin 4} (hμν : μ ≠ ν) :
    2 * (torusAverage fun q =>
        shiftedInverse z q ^ 3 * (baseSymbolDeriv μ q ^ 2 * baseSymbolSecondDeriv ν q)) =
      torusAverage fun q =>
        shiftedInverse z q ^ 2 * (baseSymbolSecondDeriv μ q * baseSymbolSecondDeriv ν q) := by
  have hC : (torusAverage fun q => ((fluxFieldDiv z μ ν q : ℝ) : ℂ)) = 0 := by
    have h0 : (∫ q in box, ((fluxFieldDiv z μ ν q : ℝ) : ℂ)) = 0 := by
      rw [integral_complex_ofReal, integral_fluxFieldDiv_eq_zero hz hμν]
      simp
    unfold torusAverage
    rw [h0, mul_zero]
  have e : (fun q => ((fluxFieldDiv z μ ν q : ℝ) : ℂ)) =
      fun q => shiftedInverse z q ^ 2 * (baseSymbolSecondDeriv μ q * baseSymbolSecondDeriv ν q) -
        2 * (shiftedInverse z q ^ 3 * (baseSymbolDeriv μ q ^ 2 * baseSymbolSecondDeriv ν q)) := by
    funext q
    simp only [fluxFieldDiv, shiftedInverse_eq_ofReal, baseSymbolDeriv, baseSymbolSecondDeriv]
    push_cast
    ring
  have h1 := continuous_baseSymbolDeriv μ
  have h2 := continuous_baseSymbolSecondDeriv μ
  have h3 := continuous_baseSymbolSecondDeriv ν
  have cL : Continuous fun q =>
      shiftedInverse z q ^ 2 * (baseSymbolSecondDeriv μ q * baseSymbolSecondDeriv ν q) :=
    continuous_pow_mul (h2.mul h3) 2 hz
  have cR : Continuous fun q =>
      2 * (shiftedInverse z q ^ 3 * (baseSymbolDeriv μ q ^ 2 * baseSymbolSecondDeriv ν q)) :=
    continuous_const.mul (continuous_pow_mul ((h1.pow 2).mul h3) 3 hz)
  rw [e, average_sub cL cR, average_const_mul] at hC
  linear_combination -hC
section Traces
variable {N' : ℕ} [NeZero N']
theorem diagSum_smul (c : ℂ) (X : Matrix (Fin N') (Fin N') ℂ) :
    diagSum (c • X) = c * diagSum X := by
  simp [diagSum, Finset.mul_sum]
theorem diagSum_add (X Y : Matrix (Fin N') (Fin N') ℂ) :
    diagSum (X + Y) = diagSum X + diagSum Y := by
  simp [diagSum, Finset.sum_add_distrib]
theorem diagSum_sub (X Y : Matrix (Fin N') (Fin N') ℂ) :
    diagSum (X - Y) = diagSum X - diagSum Y := by
  simp [diagSum, Finset.sum_sub_distrib]
theorem diagSum_one : diagSum (1 : Matrix (Fin N') (Fin N') ℂ) = N' := by
  simp [diagSum]
theorem continuous_diagSum {X : AmbientSpace → Matrix (Fin N') (Fin N') ℂ} (h : Continuous X) :
    Continuous fun q => diagSum (X q) := by
  unfold diagSum
  exact continuous_finsetSum _ fun i _ => h.matrix_elem i i
def coeffTwo (σ₂ : AmbientSpace → Matrix (Fin N') (Fin N') ℂ) (q : AmbientSpace) : ℂ :=
  -diagSum (σ₂ q)
def coeffThree (σ₁ : AmbientSpace → Matrix (Fin N') (Fin N') ℂ) (q : AmbientSpace) : ℂ :=
  diagSum (σ₁ q ^ 2) - (N' : ℂ) / 4 * (baseSymbolSecondDeriv 0 q * baseSymbolSecondDeriv 1 q)
def coeffFour (N' : ℕ) (q : AmbientSpace) : ℂ :=
  (N' : ℂ) / 4 * (baseSymbolDeriv 0 q ^ 2 * baseSymbolSecondDeriv 1 q +
    baseSymbolDeriv 1 q ^ 2 * baseSymbolSecondDeriv 0 q)
theorem diagSum_termZero (s : ℝ) (q : AmbientSpace) :
    diagSum (termZero N' s q) = shiftedInverse s q ^ 1 * (N' : ℂ) := by
  rw [termZero, diagSum_smul, diagSum_one, pow_one]
theorem diagSum_termOne (s : ℝ) (σ₁ : AmbientSpace → Matrix (Fin N') (Fin N') ℂ) (q : AmbientSpace) :
    diagSum (termOne s σ₁ q) = -(shiftedInverse s q ^ 2 * diagSum (σ₁ q)) := by
  rw [termOne, diagSum_smul, neg_mul]
theorem diagSum_termTwo (s : ℝ) (σ₁ σ₂ : AmbientSpace → Matrix (Fin N') (Fin N') ℂ)
    (q : AmbientSpace) :
    diagSum (termTwo s σ₁ σ₂ q) =
      shiftedInverse s q ^ 2 * coeffTwo σ₂ q + shiftedInverse s q ^ 3 * coeffThree σ₁ q +
        shiftedInverse s q ^ 4 * coeffFour N' q := by
  rw [termTwo, diagSum_smul, diagSum_add, diagSum_sub, diagSum_smul, diagSum_smul, diagSum_smul,
    diagSum_one]
  simp only [coeffTwo, coeffThree, coeffFour, shiftedInverseSecondDeriv]
  ring
theorem diagSum_approxInverse (s φ : ℝ) (σ₁ σ₂ : AmbientSpace → Matrix (Fin N') (Fin N') ℂ)
    (q : AmbientSpace) :
    diagSum (approxInverse s φ σ₁ σ₂ q) =
      diagSum (termZero N' s q) + (φ : ℂ) * diagSum (termOne s σ₁ q) +
        (φ : ℂ) ^ 2 * diagSum (termTwo s σ₁ σ₂ q) := by
  rw [approxInverse, diagSum_add, diagSum_add, diagSum_smul, diagSum_smul]
end Traces
theorem halfLineTraceLimits_holds : HalfLineTraceLimits := by
  intro N' _ z hz σ₁ σ₂ h₁ h₂
  have c₁ := continuous_diagSum h₁
  have c₂ := continuous_diagSum h₂
  have c₁₁ : Continuous fun q => diagSum (σ₁ q ^ 2) := continuous_diagSum (h₁.pow 2)
  have p0 := continuous_baseSymbolDeriv 0
  have p1 := continuous_baseSymbolDeriv 1
  have s0 := continuous_baseSymbolSecondDeriv 0
  have s1 := continuous_baseSymbolSecondDeriv 1
  have cA₂ : Continuous (coeffTwo σ₂) := c₂.neg
  have cA₃ : Continuous (coeffThree σ₁) :=
    c₁₁.sub (continuous_const.mul (s0.mul s1))
  have cA₄ : Continuous (coeffFour N') :=
    continuous_const.mul (((p0.pow 2).mul s1).add ((p1.pow 2).mul s0))
  have cN : Continuous fun _ : AmbientSpace => (N' : ℂ) := continuous_const
  have g₂ : ∀ w : ℝ, 0 ≤ w →
      (torusAverage fun q => diagSum (termTwo (z + w) σ₁ σ₂ q)) =
        (torusAverage fun q => shiftedInverse (z + w) q ^ 2 * coeffTwo σ₂ q) +
        (torusAverage fun q => shiftedInverse (z + w) q ^ 3 * coeffThree σ₁ q) +
        torusAverage fun q => shiftedInverse (z + w) q ^ 4 * coeffFour N' q := by
    intro w hw
    have hs : 0 < z + w := by linarith
    have a₂ := continuous_pow_mul cA₂ 2 hs
    have a₃ := continuous_pow_mul cA₃ 3 hs
    have a₄ := continuous_pow_mul cA₄ 4 hs
    have a₂₃ : Continuous fun q => shiftedInverse (z + w) q ^ 2 * coeffTwo σ₂ q +
        shiftedInverse (z + w) q ^ 3 * coeffThree σ₁ q := a₂.add a₃
    simp only [diagSum_termTwo]
    rw [average_add a₂₃ a₄, average_add a₂ a₃]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [diagSum_termZero]
    exact continuousOn_average_pow_mul hz cN 1
  · simp only [diagSum_termOne, average_neg]
    exact (continuousOn_average_pow_mul hz c₁ 2).neg
  · exact (((continuousOn_average_pow_mul hz cA₂ 2).add (continuousOn_average_pow_mul hz cA₃ 3)).add
      (continuousOn_average_pow_mul hz cA₄ 4)).congr fun w hw => g₂ w hw
  · intro w φ hw
    have hs : 0 < z + w := by linarith
    have r₀ : Continuous fun q => diagSum (termZero N' (z + w) q) := by
      simp only [diagSum_termZero]
      exact continuous_pow_mul cN 1 hs
    have r₁ : Continuous fun q => diagSum (termOne (z + w) σ₁ q) := by
      simp only [diagSum_termOne]
      exact (continuous_pow_mul c₁ 2 hs).neg
    have r₂ : Continuous fun q => diagSum (termTwo (z + w) σ₁ σ₂ q) := by
      simp only [diagSum_termTwo]
      exact ((continuous_pow_mul cA₂ 2 hs).add (continuous_pow_mul cA₃ 3 hs)).add
        (continuous_pow_mul cA₄ 4 hs)
    have m₁ : Continuous fun q => (φ : ℂ) * diagSum (termOne (z + w) σ₁ q) :=
      continuous_const.mul r₁
    have m₂ : Continuous fun q => (φ : ℂ) ^ 2 * diagSum (termTwo (z + w) σ₁ σ₂ q) :=
      continuous_const.mul r₂
    have m₀₁ : Continuous fun q => diagSum (termZero N' (z + w) q) +
        (φ : ℂ) * diagSum (termOne (z + w) σ₁ q) := r₀.add m₁
    simp only [diagSum_approxInverse]
    rw [average_add m₀₁ m₂, average_add r₀ m₁, average_const_mul, average_const_mul]
  · have h := tendsto_integral_log hz (N' : ℂ)
    have e : (torusAverage fun q => diagSum
        (Complex.log (baseSymbol q + z) • (1 : Matrix (Fin N') (Fin N') ℂ))) =
        (N' : ℂ) * torusAverage fun q => ((Real.log (baseSymbolReal q + z) : ℝ) : ℂ) := by
      rw [← average_const_mul]
      congr 1
      funext q
      rw [diagSum_smul, diagSum_one, baseSymbol_eq_ofReal, mul_comm,
        Complex.ofReal_log (baseSymbolReal_add_pos hz q).le]
      push_cast
      rfl
    rw [e]
    simp only [diagSum_termZero]
    exact h
  · have h := tendsto_integral_average_pow_mul hz c₁ 0
    simp only [diagSum_termOne, average_neg, neg_neg]
    simpa using h
  · have h2 : Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y,
        torusAverage fun q => shiftedInverse (z + w) q ^ 2 * coeffTwo σ₂ q) atTop
        (nhds ((torusAverage fun q => shiftedInverse z q ^ 1 * coeffTwo σ₂ q) /
          (((0 : ℕ) : ℂ) + 1))) :=
      tendsto_integral_average_pow_mul hz cA₂ 0
    have h3 : Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y,
        torusAverage fun q => shiftedInverse (z + w) q ^ 3 * coeffThree σ₁ q) atTop
        (nhds ((torusAverage fun q => shiftedInverse z q ^ 2 * coeffThree σ₁ q) /
          (((1 : ℕ) : ℂ) + 1))) :=
      tendsto_integral_average_pow_mul hz cA₃ 1
    have h4 : Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y,
        torusAverage fun q => shiftedInverse (z + w) q ^ 4 * coeffFour N' q) atTop
        (nhds ((torusAverage fun q => shiftedInverse z q ^ 3 * coeffFour N' q) /
          (((2 : ℕ) : ℂ) + 1))) :=
      tendsto_integral_average_pow_mul hz cA₄ 2
    have h := ((h2.add h3).add h4).neg
    have cB : Continuous fun q => shiftedInverse z q ^ 2 * diagSum (σ₁ q ^ 2) :=
      continuous_pow_mul c₁₁ 2 hz
    have cC : Continuous fun q => shiftedInverse z q ^ 1 * diagSum (σ₂ q) :=
      continuous_pow_mul c₂ 1 hz
    have cD : Continuous fun q =>
        shiftedInverse z q ^ 2 * (baseSymbolSecondDeriv 0 q * baseSymbolSecondDeriv 1 q) :=
      continuous_pow_mul (s0.mul s1) 2 hz
    have cF : Continuous fun q =>
        shiftedInverse z q ^ 3 * (baseSymbolDeriv 0 q ^ 2 * baseSymbolSecondDeriv 1 q) :=
      continuous_pow_mul ((p0.pow 2).mul s1) 3 hz
    have cG : Continuous fun q =>
        shiftedInverse z q ^ 3 * (baseSymbolDeriv 1 q ^ 2 * baseSymbolSecondDeriv 0 q) :=
      continuous_pow_mul ((p1.pow 2).mul s0) 3 hz
    have i2 : (torusAverage fun q => shiftedInverse z q ^ 1 * coeffTwo σ₂ q) =
        -torusAverage fun q => shiftedInverse z q ^ 1 * diagSum (σ₂ q) := by
      rw [← average_neg]
      simp only [coeffTwo, mul_neg]
    have i3 : (torusAverage fun q => shiftedInverse z q ^ 2 * coeffThree σ₁ q) =
        (torusAverage fun q => shiftedInverse z q ^ 2 * diagSum (σ₁ q ^ 2)) -
          (N' : ℂ) / 4 * torusAverage fun q =>
            shiftedInverse z q ^ 2 * (baseSymbolSecondDeriv 0 q * baseSymbolSecondDeriv 1 q) := by
      have cD' : Continuous fun q =>
          (N' : ℂ) / 4 *
            (shiftedInverse z q ^ 2 * (baseSymbolSecondDeriv 0 q * baseSymbolSecondDeriv 1 q)) :=
        continuous_const.mul cD
      rw [← average_const_mul, ← average_sub cB cD']
      congr 1
      funext q
      simp only [coeffThree]
      ring
    have i4 : (torusAverage fun q => shiftedInverse z q ^ 3 * coeffFour N' q) =
        (N' : ℂ) / 4 * ((torusAverage fun q =>
            shiftedInverse z q ^ 3 * (baseSymbolDeriv 0 q ^ 2 * baseSymbolSecondDeriv 1 q)) +
          torusAverage fun q =>
            shiftedInverse z q ^ 3 * (baseSymbolDeriv 1 q ^ 2 * baseSymbolSecondDeriv 0 q)) := by
      rw [← average_add cF cG, ← average_const_mul]
      congr 1
      funext q
      simp only [coeffFour]
      ring
    have t : (torusAverage fun q =>
        -(1 / 2) * shiftedInverse z q ^ 2 * diagSum (σ₁ q ^ 2) +
          shiftedInverse z q * diagSum (σ₂ q) +
          (N' : ℂ) / 24 * shiftedInverse z q ^ 2 * baseSymbolSecondDeriv 0 q *
            baseSymbolSecondDeriv 1 q) =
        -(1 / 2) * (torusAverage fun q => shiftedInverse z q ^ 2 * diagSum (σ₁ q ^ 2)) +
          (torusAverage fun q => shiftedInverse z q ^ 1 * diagSum (σ₂ q)) +
          (N' : ℂ) / 24 * torusAverage fun q =>
            shiftedInverse z q ^ 2 * (baseSymbolSecondDeriv 0 q * baseSymbolSecondDeriv 1 q) := by
      have cB' : Continuous fun q =>
          -(1 / 2) * (shiftedInverse z q ^ 2 * diagSum (σ₁ q ^ 2)) :=
        continuous_const.mul cB
      have cD' : Continuous fun q =>
          (N' : ℂ) / 24 *
            (shiftedInverse z q ^ 2 * (baseSymbolSecondDeriv 0 q * baseSymbolSecondDeriv 1 q)) :=
        continuous_const.mul cD
      have cBC : Continuous fun q =>
          -(1 / 2) * (shiftedInverse z q ^ 2 * diagSum (σ₁ q ^ 2)) +
            shiftedInverse z q ^ 1 * diagSum (σ₂ q) := cB'.add cC
      rw [← average_const_mul, ← average_const_mul, ← average_add cB' cC, ← average_add cBC cD']
      congr 1
      funext q
      ring
    have P1 := average_by_parts hz (μ := 0) (ν := 1) (by decide)
    have P2 := average_by_parts hz (μ := 1) (ν := 0) (by decide)
    have hD : (fun q =>
        shiftedInverse z q ^ 2 * (baseSymbolSecondDeriv 1 q * baseSymbolSecondDeriv 0 q)) =
        fun q => shiftedInverse z q ^ 2 * (baseSymbolSecondDeriv 0 q * baseSymbolSecondDeriv 1 q) := by
      funext q
      ring
    rw [hD] at P2
    have eqlim : -((torusAverage fun q => shiftedInverse z q ^ 1 * coeffTwo σ₂ q) /
          (((0 : ℕ) : ℂ) + 1) +
        (torusAverage fun q => shiftedInverse z q ^ 2 * coeffThree σ₁ q) / (((1 : ℕ) : ℂ) + 1) +
        (torusAverage fun q => shiftedInverse z q ^ 3 * coeffFour N' q) / (((2 : ℕ) : ℂ) + 1)) =
        torusAverage fun q =>
          -(1 / 2) * shiftedInverse z q ^ 2 * diagSum (σ₁ q ^ 2) +
            shiftedInverse z q * diagSum (σ₂ q) +
            (N' : ℂ) / 24 * shiftedInverse z q ^ 2 * baseSymbolSecondDeriv 0 q *
              baseSymbolSecondDeriv 1 q := by
      rw [t, i2, i3, i4]
      push_cast
      linear_combination (-(N' : ℂ) / 24) * P1 + (-(N' : ℂ) / 24) * P2
    rw [← eqlim]
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with y hy
    have hc₂ := intervalIntegrable_average_pow_mul hz cA₂ 2 hy
    have hc₃ := intervalIntegrable_average_pow_mul hz cA₃ 3 hy
    have hc₄ := intervalIntegrable_average_pow_mul hz cA₄ 4 hy
    rw [← intervalIntegral.integral_add hc₂ hc₃,
      ← intervalIntegral.integral_add (hc₂.add hc₃) hc₄, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [uIcc_of_le hy] at hw
    simp only [g₂ w hw.1]
end Tower.MagneticWeyl.HalfLineTrace
end YangMills.Construction
end
