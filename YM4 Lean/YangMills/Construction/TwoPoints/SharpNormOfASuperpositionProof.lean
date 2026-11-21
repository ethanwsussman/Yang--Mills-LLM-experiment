import YangMills.Construction.TwoPoints.SharpNormOfASuperposition
import Mathlib
open MeasureTheory Set
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
namespace SharpNormBounds
theorem euclidDist_nonneg (x y : AmbientSpace) : 0 ≤ TestFunctions.euclidDistR4 x y :=
  Real.sqrt_nonneg _
theorem norm_sub_le_lipConst {f : AmbientSpace → ℂ}
    (hf : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f) (x y : AmbientSpace) :
    ‖f x - f y‖ ≤ TestFunctions.lipConstR4 f * TestFunctions.euclidDistR4 x y := by
  obtain ⟨L, hL0, hL⟩ := hf
  rcases (euclidDist_nonneg x y).eq_or_lt with hzero | hpos
  · have hxy := hL x y
    rw [← hzero] at hxy ⊢
    simpa using hxy
  · rw [← div_le_iff₀ hpos]
    unfold TestFunctions.lipConstR4 TestFunctions.bestLipschitzConstant
    refine le_csInf ⟨L, hL0, hL⟩ ?_
    rintro D ⟨-, hD⟩
    rw [div_le_iff₀ hpos]
    exact hD x y
theorem lipConst_le {f : AmbientSpace → ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x - f y‖ ≤ C * TestFunctions.euclidDistR4 x y) :
    TestFunctions.lipConstR4 f ≤ C :=
  csInf_le ⟨0, fun _ hD => hD.1⟩ ⟨hC0, hC⟩
theorem norm_le_uniformNorm {f : AmbientSpace → ℂ} (hf : TestFunctions.IsBoundedFun f)
    (x : AmbientSpace) : ‖f x‖ ≤ TestFunctions.uniformNorm f := by
  obtain ⟨C, hC⟩ := hf
  exact le_ciSup (f := fun x => ‖f x‖) ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩ x
theorem sharpNorm_nonneg (s : FixedScale) (f : AmbientSpace → ℂ) : 0 ≤ s.sharpNorm f :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem norm_le_sharpNorm (s : FixedScale) {f : AmbientSpace → ℂ} (hf : IsBddLipschitz f)
    (x : AmbientSpace) : ‖f x‖ ≤ s.sharpNorm f :=
  (norm_le_uniformNorm hf.1 x).trans (le_max_left _ _)
theorem scaled_norm_sub_le_sharpNorm (s : FixedScale) {f : AmbientSpace → ℂ}
    (hf : IsBddLipschitz f) (x y : AmbientSpace) :
    40 * s.scale * ‖f x - f y‖ ≤ s.sharpNorm f * TestFunctions.euclidDistR4 x y := by
  have hs : 0 < 40 * s.scale := by have := s.scale_pos; linarith
  have e1 := mul_le_mul_of_nonneg_left (norm_sub_le_lipConst hf.2 x y) hs.le
  have e2 : 40 * s.scale * TestFunctions.lipConstR4 f ≤ s.sharpNorm f := le_max_right _ _
  have e3 := mul_le_mul_of_nonneg_right e2 (euclidDist_nonneg x y)
  linarith
theorem of_value_and_difference_bounds (s : FixedScale) {f : AmbientSpace → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hval : ∀ x, ‖f x‖ ≤ C)
    (hdiff : ∀ x y, 40 * s.scale * ‖f x - f y‖ ≤ C * TestFunctions.euclidDistR4 x y) :
    IsBddLipschitz f ∧ s.sharpNorm f ≤ C := by
  have hs : 0 < 40 * s.scale := by have := s.scale_pos; linarith
  have hq : 0 ≤ C / (40 * s.scale) := div_nonneg hC hs.le
  have hlip : ∀ x y, ‖f x - f y‖ ≤ C / (40 * s.scale) * TestFunctions.euclidDistR4 x y := by
    intro x y
    rw [div_mul_eq_mul_div, le_div_iff₀ hs]
    linarith [hdiff x y]
  refine ⟨⟨⟨C, hval⟩, ⟨_, hq, hlip⟩⟩, max_le (ciSup_le hval) ?_⟩
  have e := mul_le_mul_of_nonneg_left (lipConst_le hq hlip) hs.le
  rwa [mul_div_cancel₀ _ hs.ne'] at e
theorem sharpNorm_add_le (s : FixedScale) {F G : AmbientSpace → ℂ} (hF : IsBddLipschitz F)
    (hG : IsBddLipschitz G) :
    IsBddLipschitz (F + G) ∧ s.sharpNorm (F + G) ≤ s.sharpNorm F + s.sharpNorm G := by
  have hs : 0 < 40 * s.scale := by have := s.scale_pos; linarith
  refine of_value_and_difference_bounds s
    (add_nonneg (sharpNorm_nonneg s F) (sharpNorm_nonneg s G)) (fun x => ?_) (fun x y => ?_)
  · exact (norm_add_le _ _).trans
      (add_le_add (norm_le_sharpNorm s hF x) (norm_le_sharpNorm s hG x))
  · have e : ‖(F + G) x - (F + G) y‖ ≤ ‖F x - F y‖ + ‖G x - G y‖ := by
      have : (F + G) x - (F + G) y = (F x - F y) + (G x - G y) := by
        simp only [Pi.add_apply]; ring
      rw [this]
      exact norm_add_le _ _
    have e' := mul_le_mul_of_nonneg_left e hs.le
    linarith [scaled_norm_sub_le_sharpNorm s hF x y, scaled_norm_sub_le_sharpNorm s hG x y]
theorem sharpNorm_smul_le (s : FixedScale) (a : ℂ) {F : AmbientSpace → ℂ}
    (hF : IsBddLipschitz F) :
    IsBddLipschitz (a • F) ∧ s.sharpNorm (a • F) ≤ ‖a‖ * s.sharpNorm F := by
  refine of_value_and_difference_bounds s (mul_nonneg (norm_nonneg a) (sharpNorm_nonneg s F))
    (fun x => ?_) (fun x y => ?_)
  · rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_le_sharpNorm s hF x) (norm_nonneg a)
  · rw [Pi.smul_apply, Pi.smul_apply, ← smul_sub, norm_smul]
    have e := mul_le_mul_of_nonneg_left (scaled_norm_sub_le_sharpNorm s hF x y) (norm_nonneg a)
    linarith
theorem sharpNorm_smul_eq (s : FixedScale) (a : ℂ) {F : AmbientSpace → ℂ}
    (hF : IsBddLipschitz F) : s.sharpNorm (a • F) = ‖a‖ * s.sharpNorm F := by
  refine le_antisymm (sharpNorm_smul_le s a hF).2 ?_
  by_cases ha : a = 0
  · subst ha
    simpa using sharpNorm_nonneg s ((0 : ℂ) • F)
  · have e := (sharpNorm_smul_le s a⁻¹ (sharpNorm_smul_le s a hF).1).2
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul, norm_inv, ← div_eq_inv_mul,
      le_div_iff₀ (norm_pos_iff.2 ha)] at e
    linarith
theorem integrableOn_of_norm_le {Z : Set AmbientSpace} {g : AmbientSpace → ℂ} {B : ℝ}
    (hZ : MeasurableSet Z) (hfin : volume Z < ⊤) (hg : Measurable g)
    (hB : ∀ z ∈ Z, ‖g z‖ ≤ B) : IntegrableOn g Z volume := by
  have : IsFiniteMeasure (volume.restrict Z) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  exact Integrable.mono' (integrable_const B) hg.aestronglyMeasurable
    (ae_restrict_of_forall_mem hZ hB)
theorem norm_setIntegral_mul_le {Z : Set AmbientSpace} {w G : AmbientSpace → ℂ} {B : ℝ}
    (hZ : MeasurableSet Z) (hw : IntegrableOn (fun z => ‖w z‖) Z volume)
    (hB : ∀ z ∈ Z, ‖G z‖ ≤ B) : ‖∫ z in Z, w z * G z‖ ≤ (∫ z in Z, ‖w z‖) * B := by
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (hw.mul_const B) (ae_restrict_of_forall_mem hZ fun z hz => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB z hz) (norm_nonneg _)
theorem sharpNorm_superposition_le (s : FixedScale) {Z : Set AmbientSpace} {w : AmbientSpace → ℂ}
    {F : AmbientSpace → AmbientSpace → ℂ} {A : ℝ} (hA : 0 ≤ A) (hZ : MeasurableSet Z)
    (hbdd : Bornology.IsBounded Z) (hw : Measurable w) (hwC : ∃ C : ℝ, ∀ z ∈ Z, ‖w z‖ ≤ C)
    (hF : Continuous (Function.uncurry F)) (hFb : ∀ z ∈ Z, IsBddLipschitz (F z))
    (hFA : ∀ z ∈ Z, s.sharpNorm (F z) ≤ A) :
    IsBddLipschitz (fun x => setIntegralOf Z fun z => w z * F z x) ∧
      s.sharpNorm (fun x => setIntegralOf Z fun z => w z * F z x) ≤ (∫ z in Z, ‖w z‖) * A := by
  have hs : 0 < 40 * s.scale := by have := s.scale_pos; linarith
  obtain ⟨C, hC⟩ := hwC
  have hfin : volume Z < ⊤ := hbdd.measure_lt_top
  have hwint : IntegrableOn (fun z => ‖w z‖) Z volume :=
    (integrableOn_of_norm_le (g := fun z => ((‖w z‖ : ℝ) : ℂ)) hZ hfin
      (Complex.measurable_ofReal.comp hw.norm) (B := C) (fun z hz => by
        simpa using hC z hz)).norm.congr (by simp)
  have hI : 0 ≤ ∫ z in Z, ‖w z‖ := integral_nonneg fun _ => norm_nonneg _
  have hcont : ∀ x, Continuous fun z => F z x := fun x =>
    hF.comp (Continuous.prodMk continuous_id continuous_const)
  have hint : ∀ x, IntegrableOn (fun z => w z * F z x) Z volume := by
    intro x
    refine integrableOn_of_norm_le hZ hfin (hw.mul (hcont x).measurable) (B := C * A) ?_
    intro z hz
    rw [norm_mul]
    exact mul_le_mul (hC z hz) ((norm_le_sharpNorm s (hFb z hz) x).trans (hFA z hz))
      (norm_nonneg _) ((norm_nonneg _).trans (hC z hz))
  refine of_value_and_difference_bounds s (mul_nonneg hI hA) (fun x => ?_) (fun x y => ?_)
  · exact norm_setIntegral_mul_le hZ hwint fun z hz =>
      (norm_le_sharpNorm s (hFb z hz) x).trans (hFA z hz)
  · have hd := euclidDist_nonneg x y
    have hsub : (setIntegralOf Z fun z => w z * F z x) - (setIntegralOf Z fun z => w z * F z y) =
        ∫ z in Z, w z * (F z x - F z y) := by
      change (∫ z in Z, w z * F z x) - (∫ z in Z, w z * F z y) = _
      rw [← integral_sub (hint x) (hint y)]
      simp only [mul_sub]
    have hb : ∀ z ∈ Z, ‖F z x - F z y‖ ≤ A / (40 * s.scale) * TestFunctions.euclidDistR4 x y := by
      intro z hz
      rw [div_mul_eq_mul_div, le_div_iff₀ hs]
      have e1 := scaled_norm_sub_le_sharpNorm s (hFb z hz) x y
      have e2 := mul_le_mul_of_nonneg_right (hFA z hz) hd
      linarith
    have e := norm_setIntegral_mul_le (G := fun z => F z x - F z y) hZ hwint hb
    rw [← hsub] at e
    have e' := mul_le_mul_of_nonneg_left e hs.le
    refine e'.trans (le_of_eq ?_)
    have hs0 : s.scale ≠ 0 := s.scale_pos.ne'
    field_simp
end SharpNormBounds
open SharpNormBounds in
theorem SharpNormSuperpositionBound.holds : SharpNormSuperpositionBound.Statement := by
  intro s
  refine ⟨fun F G hF hG => sharpNorm_add_le s hF hG,
    fun a F hF => ⟨(sharpNorm_smul_le s a hF).1, sharpNorm_smul_eq s a hF⟩, ?_⟩
  intro Z w F A hZ hbdd hw hwC hF hFb hFA
  rcases Z.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
  · have e := sharpNorm_superposition_le s (F := F) (A := 0) le_rfl hZ hbdd hw hwC hF
      (fun z hz => absurd hz (notMem_empty z)) (fun z hz => absurd hz (notMem_empty z))
    simpa using e
  · exact sharpNorm_superposition_le s ((sharpNorm_nonneg s (F z)).trans (hFA z hz)) hZ hbdd hw
      hwC hF hFb hFA
end YangMills.Construction.TwoPoints
end
