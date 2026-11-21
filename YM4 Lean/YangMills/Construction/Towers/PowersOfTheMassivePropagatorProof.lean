import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Continuum.PlateauOfAFunctionOnTuples
import YangMills.Construction.PeriodicOperators.SymbolOfAProductProof
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.Tower.MassivePropagator
def resolvent (z : ℝ) (q : InfiniteLattice.AmbientSpace) : ℝ :=
  (∑ μ, (2 - 2 * Real.cos (q μ)) + z)⁻¹
def brillouinAverage (g : InfiniteLattice.AmbientSpace → ℝ) : ℝ :=
  ((2 * Real.pi) ^ 4)⁻¹ * ∫ q in Set.Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), g q
def PowerBounds : Prop :=
  ∃ C : ℝ, ∀ z : ℝ, 0 < z →
    brillouinAverage (resolvent z) ≤ C ∧
    brillouinAverage (fun q => resolvent z q ^ 2 * TorusMetric.euclidNormVec q) ≤ C ∧
    z * brillouinAverage (fun q => resolvent z q ^ 2) ≤ C ∧
    z * brillouinAverage (fun q => resolvent z q ^ 3) ≤ C ∧
    z ^ 2 * brillouinAverage (fun q => resolvent z q ^ 4) ≤ C ∧
    (z ≤ 1 → |brillouinAverage (fun q => resolvent z q ^ 2) -
      1 / (16 * Real.pi ^ 2) * Real.log (1 / z)| ≤ C)
end YangMills.Construction.Tower.MassivePropagator
end

open MeasureTheory Set
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
noncomputable section
namespace YangMills.Construction.Tower.MassivePropagator
abbrev brillouinZone : Set AmbientSpace :=
  Set.Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi)
def quadraticRatio : ℝ := Real.pi ^ 2 / 4
def latticeSymbol (q : AmbientSpace) : ℝ := ∑ μ, (2 - 2 * Real.cos (q μ))
theorem two_sub_two_cos_le_sq (t : ℝ) : 2 - 2 * Real.cos t ≤ t ^ 2 := by
  have := Real.one_sub_sq_div_two_le_cos (x := t)
  linarith
theorem jordan_le_two_sub_two_cos {t : ℝ} (ht : |t| ≤ Real.pi) :
    4 / Real.pi ^ 2 * t ^ 2 ≤ 2 - 2 * Real.cos t := by
  have := Real.cos_le_one_sub_mul_cos_sq ht
  have e : 4 / Real.pi ^ 2 * t ^ 2 = 2 * (2 / Real.pi ^ 2 * t ^ 2) := by ring
  linarith
theorem sq_sub_two_sub_two_cos_le_pow_four (t : ℝ) : t ^ 2 - (2 - 2 * Real.cos t) ≤ t ^ 4 := by
  by_cases h : |t| ≤ 1
  · have h2 := (abs_le.1 (Real.cos_bound h)).2
    have h4 : |t| ^ 4 = t ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
    rw [h4] at h2
    have : 0 ≤ t ^ 4 := by positivity
    linarith
  · have h1 : 1 < |t| := not_le.1 h
    have h3 : 1 ≤ t ^ 2 := by
      rw [← sq_abs]
      nlinarith
    have h5 : t ^ 4 = t ^ 2 * t ^ 2 := by ring
    have h6 := Real.cos_le_one t
    have h7 := Real.neg_one_le_cos t
    nlinarith
theorem euclidNormVec_nonneg (q : AmbientSpace) : 0 ≤ euclidNormVec q := Real.sqrt_nonneg _
theorem euclidNormVec_sq (q : AmbientSpace) : euclidNormVec q ^ 2 = ∑ μ, q μ ^ 2 := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_sq <;> assumption
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem continuous_latticeSymbol : Continuous latticeSymbol := by
  unfold latticeSymbol
  fun_prop
theorem latticeSymbol_nonneg (q : AmbientSpace) : 0 ≤ latticeSymbol q :=
  Finset.sum_nonneg fun μ _ => by
    have := Real.cos_le_one (q μ)
    linarith
theorem latticeSymbol_le_sq (q : AmbientSpace) : latticeSymbol q ≤ euclidNormVec q ^ 2 := by
  rw [euclidNormVec_sq]
  exact Finset.sum_le_sum fun μ _ => two_sub_two_cos_le_sq _
theorem jordan_le_latticeSymbol {q : AmbientSpace} (hq : q ∈ brillouinZone) :
    4 / Real.pi ^ 2 * euclidNormVec q ^ 2 ≤ latticeSymbol q := by
  rw [euclidNormVec_sq, Finset.mul_sum]
  exact Finset.sum_le_sum fun μ _ =>
    jordan_le_two_sub_two_cos (abs_le.2 ⟨hq.1 μ, hq.2 μ⟩)
theorem sq_sub_latticeSymbol_le (q : AmbientSpace) :
    euclidNormVec q ^ 2 - latticeSymbol q ≤ euclidNormVec q ^ 4 := by
  have h1 : euclidNormVec q ^ 2 - latticeSymbol q =
      ∑ μ, (q μ ^ 2 - (2 - 2 * Real.cos (q μ))) := by
    rw [euclidNormVec_sq, latticeSymbol]
    exact (Finset.sum_sub_distrib _ _).symm
  have h2 : ∑ μ, (q μ ^ 2 - (2 - 2 * Real.cos (q μ))) ≤ ∑ μ, q μ ^ 4 :=
    Finset.sum_le_sum fun μ _ => sq_sub_two_sub_two_cos_le_pow_four _
  have h3 : ∑ μ, q μ ^ 4 ≤ euclidNormVec q ^ 4 := by
    have e : euclidNormVec q ^ 4 = (∑ μ, q μ ^ 2) ^ 2 := by
      rw [← euclidNormVec_sq]
      ring
    rw [e, Fin.sum_univ_four, Fin.sum_univ_four]
    have a := sq_nonneg (q 0)
    have b := sq_nonneg (q 1)
    have c := sq_nonneg (q 2)
    have d := sq_nonneg (q 3)
    nlinarith [mul_nonneg a b, mul_nonneg a c, mul_nonneg a d, mul_nonneg b c, mul_nonneg b d,
      mul_nonneg c d]
  linarith
theorem abs_coord_le_euclidNormVec (q : AmbientSpace) (μ : Fin 4) : |q μ| ≤ euclidNormVec q := by apply _root_.YangMills.SharedProofs.p10398 <;> assumption
theorem euclidNormVec_eq_norm_toLp (q : AmbientSpace) :
    euclidNormVec q = ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolComp.euclidNormVec_eq_norm <;> assumption
theorem integral_radial_polar (f : ℝ → ℝ) :
    ∫ q : AmbientSpace, f (euclidNormVec q) =
      2 * Real.pi ^ 2 * ∫ y in Ioi (0 : ℝ), y ^ 3 * f y := by
  have h1 : ∫ q : AmbientSpace, f (euclidNormVec q) =
      ∫ x : EuclideanSpace ℝ (Fin 4), f ‖x‖ := by
    have h := ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 4)).symm).integral_comp'
      (fun x : EuclideanSpace ℝ (Fin 4) => f ‖x‖)
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only []
    rw [euclidNormVec_eq_norm_toLp]
    rfl
  have hv : (volume : Measure (EuclideanSpace ℝ (Fin 4))).real (Metric.ball 0 1) =
      Real.pi ^ 2 / 2 := by
    rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp)]
    simp [Nat.factorial]
    positivity
  rw [h1, integral_fun_norm_addHaar volume f, hv, finrank_euclideanSpace_fin]
  simp only [nsmul_eq_mul, smul_eq_mul]
  norm_num
  ring
theorem setIntegral_euclidNormVec_le_radial (f : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R) :
    ∫ q in {q : AmbientSpace | euclidNormVec q ≤ R}, f (euclidNormVec q) =
      2 * Real.pi ^ 2 * ∫ y in (0 : ℝ)..R, y ^ 3 * f y := by
  have hS : MeasurableSet {q : AmbientSpace | euclidNormVec q ≤ R} :=
    measurableSet_le continuous_euclidNormVec.measurable measurable_const
  rw [← integral_indicator hS]
  have h1 : ({q : AmbientSpace | euclidNormVec q ≤ R}.indicator fun q => f (euclidNormVec q)) =
      fun q => (Iic R).indicator f (euclidNormVec q) := by
    funext q
    by_cases hq : euclidNormVec q ≤ R <;> simp [indicator, hq]
  rw [h1, integral_radial_polar, intervalIntegral.integral_of_le hR]
  congr 1
  have h2 : (fun y : ℝ => y ^ 3 * (Iic R).indicator f y) =
      (Iic R).indicator fun y => y ^ 3 * f y := by
    funext y
    by_cases hy : y ≤ R <;> simp [indicator, hy]
  rw [h2, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic]
theorem measurableSet_euclidNormVec_le (R : ℝ) :
    MeasurableSet {q : AmbientSpace | euclidNormVec q ≤ R} :=
  measurableSet_le continuous_euclidNormVec.measurable measurable_const
theorem integrableOn_brillouinZone {g : AmbientSpace → ℝ} (hg : Continuous g) :
    IntegrableOn g brillouinZone :=
  hg.continuousOn.integrableOn_compact isCompact_Icc
theorem brillouinZone_subset_euclidNormVec_le :
    brillouinZone ⊆ {q : AmbientSpace | euclidNormVec q ≤ 2 * Real.pi} := by
  intro q hq
  have h : ∑ μ, q μ ^ 2 ≤ (2 * Real.pi) ^ 2 := by
    have h1 : ∀ μ, q μ ^ 2 ≤ Real.pi ^ 2 := fun μ =>
      sq_le_sq' (hq.1 μ) (hq.2 μ)
    rw [Fin.sum_univ_four]
    nlinarith [h1 0, h1 1, h1 2, h1 3]
  exact Real.sqrt_le_iff.2 ⟨by positivity, h⟩
theorem euclidNormVec_le_one_subset_brillouinZone :
    {q : AmbientSpace | euclidNormVec q ≤ 1} ⊆ brillouinZone := by
  intro q hq
  have hpi := Real.pi_gt_three
  constructor <;> intro μ <;> have h := abs_le.1 ((abs_coord_le_euclidNormVec q μ).trans hq)
  · show -Real.pi ≤ q μ
    linarith [h.1]
  · show q μ ≤ Real.pi
    linarith [h.2]
theorem setIntegral_brillouinZone_le_radial {f : ℝ → ℝ} (hf : Continuous f)
    (hnn : ∀ r, 0 ≤ r → 0 ≤ f r) :
    ∫ q in brillouinZone, f (euclidNormVec q) ≤
      2 * Real.pi ^ 2 * ∫ y in (0 : ℝ)..(2 * Real.pi), y ^ 3 * f y := by
  rw [← setIntegral_euclidNormVec_le_radial f _ (by positivity)]
  have hc : Continuous fun q : AmbientSpace => f (euclidNormVec q) :=
    hf.comp continuous_euclidNormVec
  have hb : IsCompact {q : AmbientSpace | euclidNormVec q ≤ 2 * Real.pi} := by
    refine Metric.isCompact_of_isClosed_isBounded
      (isClosed_le continuous_euclidNormVec continuous_const) ?_
    refine (Metric.isBounded_Icc (fun _ : Fin 4 => -(2 * Real.pi)) (fun _ => 2 * Real.pi)).subset ?_
    intro q hq
    constructor <;> intro μ <;> have h := abs_le.1 ((abs_coord_le_euclidNormVec q μ).trans hq)
    · exact h.1
    · exact h.2
  refine setIntegral_mono_set (hc.continuousOn.integrableOn_compact hb) ?_
    (LE.le.eventuallyLE brillouinZone_subset_euclidNormVec_le)
  exact Filter.Eventually.of_forall fun q => hnn _ (euclidNormVec_nonneg q)
theorem setIntegral_brillouinZone_le_of_majorant {f : ℝ → ℝ} {g : AmbientSpace → ℝ}
    (hf : Continuous f) (hnn : ∀ r, 0 ≤ r → 0 ≤ f r)
    (hg : Continuous g) {c I : ℝ} (hc : 0 ≤ c)
    (hI : ∫ y in (0 : ℝ)..(2 * Real.pi), y ^ 3 * f y ≤ I)
    (hle : ∀ q ∈ brillouinZone, g q ≤ c * f (euclidNormVec q)) :
    ∫ q in brillouinZone, g q ≤ c * (2 * Real.pi ^ 2 * I) := by
  have hcf : Continuous fun q : AmbientSpace => c * f (euclidNormVec q) :=
    continuous_const.mul (hf.comp continuous_euclidNormVec)
  calc ∫ q in brillouinZone, g q ≤ ∫ q in brillouinZone, c * f (euclidNormVec q) :=
        setIntegral_mono_on (integrableOn_brillouinZone hg) (integrableOn_brillouinZone hcf)
          measurableSet_Icc hle
    _ = c * ∫ q in brillouinZone, f (euclidNormVec q) := integral_const_mul _ _
    _ ≤ c * (2 * Real.pi ^ 2 * I) := by
        refine mul_le_mul_of_nonneg_left ((setIntegral_brillouinZone_le_radial hf hnn).trans ?_) hc
        exact mul_le_mul_of_nonneg_left hI (by positivity)
theorem radialIntegral_le_of_bound {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ y ∈ Icc (0 : ℝ) (2 * Real.pi), y ^ 3 * f y ≤ M) :
    ∫ y in (0 : ℝ)..(2 * Real.pi), y ^ 3 * f y ≤ M * (2 * Real.pi) := by
  have h := intervalIntegral.integral_mono_on (a := 0) (b := 2 * Real.pi) (by positivity)
    (((continuous_pow 3).mul hf).intervalIntegrable (μ := volume) _ _)
    (continuous_const.intervalIntegrable (μ := volume) _ _) hM
  simpa [mul_comm] using h
theorem quadraticRatio_pos : 0 < quadraticRatio := by
  unfold quadraticRatio
  positivity
theorem one_le_quadraticRatio : 1 ≤ quadraticRatio := by
  have := Real.pi_gt_three
  unfold quadraticRatio
  nlinarith
theorem resolvent_eq (z : ℝ) (q : AmbientSpace) : resolvent z q = (latticeSymbol q + z)⁻¹ := rfl
theorem continuous_resolvent {z : ℝ} (hz : 0 < z) : Continuous (resolvent z) := by
  exact show Continuous fun q : AmbientSpace => (latticeSymbol q + z)⁻¹ from
    (continuous_latticeSymbol.add continuous_const).inv₀ fun q =>
      (add_pos_of_nonneg_of_pos (latticeSymbol_nonneg q) hz).ne'
theorem resolvent_pos {z : ℝ} (hz : 0 < z) (q : AmbientSpace) : 0 < resolvent z q := by
  rw [resolvent_eq]
  have := latticeSymbol_nonneg q
  positivity
theorem mul_resolvent_le_one {z : ℝ} (hz : 0 < z) (q : AmbientSpace) : z * resolvent z q ≤ 1 := by
  rw [resolvent_eq, ← div_eq_mul_inv]
  have := latticeSymbol_nonneg q
  rw [div_le_one (by positivity)]
  linarith
def radialResolvent (z r : ℝ) : ℝ := (r ^ 2 + z)⁻¹
theorem radialResolvent_pos {z : ℝ} (hz : 0 < z) (r : ℝ) : 0 < radialResolvent z r := by
  unfold radialResolvent
  positivity
theorem continuous_radialResolvent {z : ℝ} (hz : 0 < z) : Continuous (radialResolvent z) := by
  exact show Continuous fun r : ℝ => (r ^ 2 + z)⁻¹ from
    (by fun_prop : Continuous fun r : ℝ => r ^ 2 + z).inv₀ fun r =>
      (add_pos_of_nonneg_of_pos (sq_nonneg r) hz).ne'
theorem sq_mul_radialResolvent_le_one {z : ℝ} (hz : 0 < z) (r : ℝ) :
    r ^ 2 * radialResolvent z r ≤ 1 := by
  unfold radialResolvent
  rw [← div_eq_mul_inv, div_le_one (by positivity)]
  linarith
theorem resolvent_le_radialResolvent {z : ℝ} (hz : 0 < z) {q : AmbientSpace}
    (hq : q ∈ brillouinZone) :
    resolvent z q ≤ quadraticRatio * radialResolvent z (euclidNormVec q) := by
  have h1 := jordan_le_latticeSymbol hq
  have hs := latticeSymbol_nonneg q
  have e : quadraticRatio * (4 / Real.pi ^ 2 * euclidNormVec q ^ 2) = euclidNormVec q ^ 2 := by
    unfold quadraticRatio
    field_simp
  have h2 : euclidNormVec q ^ 2 ≤ quadraticRatio * latticeSymbol q := by
    rw [← e]
    exact mul_le_mul_of_nonneg_left h1 quadraticRatio_pos.le
  have h3 : z ≤ quadraticRatio * z := le_mul_of_one_le_left hz.le one_le_quadraticRatio
  rw [resolvent_eq]
  unfold radialResolvent
  have hu : 0 < latticeSymbol q + z := by positivity
  have hw : 0 < euclidNormVec q ^ 2 + z := by positivity
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hu hw]
  nlinarith
theorem radialResolvent_le_resolvent {z : ℝ} (hz : 0 < z) (q : AmbientSpace) :
    radialResolvent z (euclidNormVec q) ≤ resolvent z q := by
  have hs := latticeSymbol_nonneg q
  rw [resolvent_eq]
  unfold radialResolvent
  exact inv_anti₀ (by positivity) (by linarith [latticeSymbol_le_sq q])
theorem resolvent_sq_sub_radialResolvent_sq_le {z : ℝ} (hz : 0 < z) {q : AmbientSpace}
    (hq : q ∈ brillouinZone) :
    resolvent z q ^ 2 - radialResolvent z (euclidNormVec q) ^ 2 ≤
      2 * quadraticRatio ^ 2 * (euclidNormVec q ^ 4 * radialResolvent z (euclidNormVec q) ^ 3) := by
  have hU := resolvent_pos hz q
  have hW := radialResolvent_pos hz (euclidNormVec q)
  have hUW := resolvent_le_radialResolvent hz hq
  have hWU := radialResolvent_le_resolvent hz q
  have hb := one_le_quadraticRatio
  have h4 : 0 ≤ euclidNormVec q ^ 4 := by positivity
  have hs := latticeSymbol_nonneg q
  set U := resolvent z q with hUdef
  set W := radialResolvent z (euclidNormVec q) with hWdef
  have e : U - W = U * W * (euclidNormVec q ^ 2 - latticeSymbol q) := by
    rw [hUdef, hWdef, resolvent_eq]
    unfold radialResolvent
    field_simp
    ring
  have h1 : U - W ≤ quadraticRatio * W ^ 2 * euclidNormVec q ^ 4 := by
    rw [e]
    have a : U * W * (euclidNormVec q ^ 2 - latticeSymbol q) ≤ U * W * euclidNormVec q ^ 4 :=
      mul_le_mul_of_nonneg_left (sq_sub_latticeSymbol_le q) (by positivity)
    have b : U * W * euclidNormVec q ^ 4 ≤ quadraticRatio * W * W * euclidNormVec q ^ 4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hUW hW.le) h4
    nlinarith
  have h2 : U + W ≤ 2 * quadraticRatio * W := by nlinarith
  calc U ^ 2 - W ^ 2 = (U - W) * (U + W) := by ring
    _ ≤ (quadraticRatio * W ^ 2 * euclidNormVec q ^ 4) * (2 * quadraticRatio * W) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 2 * quadraticRatio ^ 2 * (euclidNormVec q ^ 4 * W ^ 3) := by ring
def radialConstant : ℝ := 2 * Real.pi ^ 2 * (2 * Real.pi * (2 * Real.pi))
theorem radialConstant_pos : 0 < radialConstant := by
  have := Real.pi_pos
  unfold radialConstant
  positivity
theorem setIntegral_brillouinZone_le_radialConstant {f : ℝ → ℝ} {g : AmbientSpace → ℝ}
    (hf : Continuous f) (hnn : ∀ r, 0 ≤ r → 0 ≤ f r) (hg : Continuous g) {c : ℝ} (hc : 0 ≤ c)
    (hM : ∀ y ∈ Icc (0 : ℝ) (2 * Real.pi), y ^ 3 * f y ≤ 2 * Real.pi)
    (hle : ∀ q ∈ brillouinZone, g q ≤ c * f (euclidNormVec q)) :
    ∫ q in brillouinZone, g q ≤ c * radialConstant :=
  setIntegral_brillouinZone_le_of_majorant hf hnn hg hc (radialIntegral_le_of_bound hf hM) hle
theorem setIntegral_resolvent_le {z : ℝ} (hz : 0 < z) :
    ∫ q in brillouinZone, resolvent z q ≤ quadraticRatio * radialConstant := by
  refine setIntegral_brillouinZone_le_radialConstant (continuous_radialResolvent hz)
    (fun r _ => (radialResolvent_pos hz r).le)
    (continuous_resolvent hz) quadraticRatio_pos.le ?_ fun q hq => resolvent_le_radialResolvent hz hq
  intro y hy
  have h1 := sq_mul_radialResolvent_le_one hz y
  have e : y ^ 3 * radialResolvent z y = y * (y ^ 2 * radialResolvent z y) := by ring
  rw [e]
  calc y * (y ^ 2 * radialResolvent z y) ≤ y * 1 := mul_le_mul_of_nonneg_left h1 hy.1
    _ ≤ 2 * Real.pi := by linarith [hy.2]
theorem setIntegral_resolvent_sq_mul_norm_le {z : ℝ} (hz : 0 < z) :
    ∫ q in brillouinZone, resolvent z q ^ 2 * euclidNormVec q ≤
      quadraticRatio ^ 2 * radialConstant := by
  have hpi := Real.pi_gt_three
  refine setIntegral_brillouinZone_le_radialConstant (f := fun r => r * radialResolvent z r ^ 2)
    (by have := continuous_radialResolvent hz; fun_prop)
    (fun r hr => mul_nonneg hr (by positivity))
    (by have := continuous_resolvent hz; have := continuous_euclidNormVec; fun_prop)
    (by positivity) ?_ fun q hq => ?_
  · intro y hy
    have h1 := sq_mul_radialResolvent_le_one hz y
    have h2 := radialResolvent_pos hz y
    have h3 : 0 ≤ y ^ 2 * radialResolvent z y := by positivity
    have e : y ^ 3 * (y * radialResolvent z y ^ 2) = (y ^ 2 * radialResolvent z y) ^ 2 := by ring
    rw [e]
    nlinarith
  · have h1 := resolvent_le_radialResolvent hz hq
    have h2 := resolvent_pos hz q
    have h3 : resolvent z q ^ 2 ≤ (quadraticRatio * radialResolvent z (euclidNormVec q)) ^ 2 :=
      pow_le_pow_left₀ h2.le h1 2
    have h4 := mul_le_mul_of_nonneg_right h3 (euclidNormVec_nonneg q)
    calc resolvent z q ^ 2 * euclidNormVec q ≤ _ := h4
      _ = _ := by ring
theorem mul_setIntegral_resolvent_sq_le {z : ℝ} (hz : 0 < z) :
    z * ∫ q in brillouinZone, resolvent z q ^ 2 ≤ quadraticRatio * radialConstant := by
  have hY := continuous_resolvent hz
  rw [← integral_const_mul]
  refine le_trans ?_ (setIntegral_resolvent_le hz)
  refine setIntegral_mono_on (integrableOn_brillouinZone (by fun_prop))
    (integrableOn_brillouinZone hY) measurableSet_Icc fun q _ => ?_
  have h1 := mul_resolvent_le_one hz q
  have h2 := resolvent_pos hz q
  nlinarith
theorem hasDerivAt_radialResolvent {z : ℝ} (hz : 0 < z) (y : ℝ) :
    HasDerivAt (radialResolvent z) (-(2 * y) / (y ^ 2 + z) ^ 2) y := by
  have h0 : HasDerivAt (fun y : ℝ => y ^ 2 + z) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).add_const z
  have hw : y ^ 2 + z ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg y) hz).ne'
  exact h0.fun_inv hw
theorem radialIntegral_mul_radialResolvent_cube_le {z : ℝ} (hz : 0 < z) {R : ℝ} :
    ∫ y in (0 : ℝ)..R, y ^ 3 * (z * radialResolvent z y ^ 3) ≤ 1 / 4 := by
  have hM := continuous_radialResolvent hz
  have hd : ∀ y : ℝ, HasDerivAt
      (fun y => -(z / 2) * radialResolvent z y + z ^ 2 / 4 * radialResolvent z y ^ 2)
      (y ^ 3 * (z * radialResolvent z y ^ 3)) y := by
    intro y
    have hw : y ^ 2 + z ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg y) hz).ne'
    have h1 := hasDerivAt_radialResolvent hz y
    have h2 := (h1.const_mul (-(z / 2))).fun_add ((h1.fun_pow 2).const_mul (z ^ 2 / 4))
    refine h2.congr_deriv ?_
    unfold radialResolvent
    norm_num
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have h0 : z * radialResolvent z 0 = 1 := by
    unfold radialResolvent
    field_simp
    simp
  have hR : z * radialResolvent z R ≤ 1 := by
    unfold radialResolvent
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    nlinarith [sq_nonneg R]
  have hR0 : 0 ≤ z * radialResolvent z R := (mul_pos hz (radialResolvent_pos hz R)).le
  nlinarith
theorem radialIntegral_radialResolvent_sq_eq {z : ℝ} (hz : 0 < z) :
    ∫ y in (0 : ℝ)..1, y ^ 3 * radialResolvent z y ^ 2 =
      1 / 2 * (Real.log (1 + z) + z * (1 + z)⁻¹ - Real.log z - 1) := by
  have hM := continuous_radialResolvent hz
  have hd : ∀ y : ℝ, HasDerivAt
      (fun y => 1 / 2 * (Real.log (y ^ 2 + z) + z * radialResolvent z y))
      (y ^ 3 * radialResolvent z y ^ 2) y := by
    intro y
    have hw : y ^ 2 + z ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg y) hz).ne'
    have h0 : HasDerivAt (fun y : ℝ => y ^ 2 + z) (2 * y) y := by
      simpa using (hasDerivAt_pow 2 y).add_const z
    have h1 := hasDerivAt_radialResolvent hz y
    have h2 := ((h0.log hw).fun_add (h1.const_mul z)).const_mul (1 / 2 : ℝ)
    refine h2.congr_deriv ?_
    unfold radialResolvent
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have e0 : z * radialResolvent z 0 = 1 := by
    unfold radialResolvent
    field_simp
    simp
  have e1 : radialResolvent z 1 = (1 + z)⁻¹ := by
    unfold radialResolvent
    norm_num
  simp only [e0, e1]
  norm_num
  ring
theorem mul_setIntegral_resolvent_cube_le {z : ℝ} (hz : 0 < z) :
    z * ∫ q in brillouinZone, resolvent z q ^ 3 ≤
      quadraticRatio ^ 3 * (2 * Real.pi ^ 2 * (1 / 4)) := by
  have hY := continuous_resolvent hz
  have hM := continuous_radialResolvent hz
  rw [← integral_const_mul]
  refine setIntegral_brillouinZone_le_of_majorant (f := fun r => z * radialResolvent z r ^ 3)
    (by fun_prop)
    (fun r _ => mul_nonneg hz.le (pow_nonneg (radialResolvent_pos hz r).le 3))
    (by fun_prop) (by have := quadraticRatio_pos; positivity)
    (radialIntegral_mul_radialResolvent_cube_le hz) fun q hq => ?_
  have h1 := resolvent_le_radialResolvent hz hq
  have h2 := resolvent_pos hz q
  have h3 : resolvent z q ^ 3 ≤ (quadraticRatio * radialResolvent z (euclidNormVec q)) ^ 3 :=
    pow_le_pow_left₀ h2.le h1 3
  have h4 := mul_le_mul_of_nonneg_left h3 hz.le
  calc z * resolvent z q ^ 3 ≤ _ := h4
    _ = _ := by ring
theorem sq_mul_setIntegral_resolvent_pow_four_le {z : ℝ} (hz : 0 < z) :
    z ^ 2 * ∫ q in brillouinZone, resolvent z q ^ 4 ≤
      quadraticRatio ^ 3 * (2 * Real.pi ^ 2 * (1 / 4)) := by
  have hY := continuous_resolvent hz
  refine le_trans ?_ (mul_setIntegral_resolvent_cube_le hz)
  rw [← integral_const_mul, ← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_brillouinZone (by fun_prop))
    (integrableOn_brillouinZone (by fun_prop)) measurableSet_Icc fun q _ => ?_
  have h1 := mul_resolvent_le_one hz q
  have h2 := resolvent_pos hz q
  have h3 : 0 ≤ z * resolvent z q ^ 3 := by positivity
  calc z ^ 2 * resolvent z q ^ 4 = (z * resolvent z q) * (z * resolvent z q ^ 3) := by
        ring
    _ ≤ 1 * (z * resolvent z q ^ 3) := mul_le_mul_of_nonneg_right h1 h3
    _ = z * resolvent z q ^ 3 := one_mul _
theorem abs_setIntegral_resolvent_sq_sub_le {z : ℝ} (hz : 0 < z) :
    |(∫ q in brillouinZone, resolvent z q ^ 2) -
        ∫ q in brillouinZone, radialResolvent z (euclidNormVec q) ^ 2| ≤
      2 * quadraticRatio ^ 2 * radialConstant := by
  have hY := continuous_resolvent hz
  have hM := continuous_radialResolvent hz
  have hE := continuous_euclidNormVec
  have hb := quadraticRatio_pos
  have hc1 : Continuous fun q : AmbientSpace => resolvent z q ^ 2 := by fun_prop
  have hc2 : Continuous fun q : AmbientSpace => radialResolvent z (euclidNormVec q) ^ 2 := by
    fun_prop
  have key : ∀ {g : AmbientSpace → ℝ}, Continuous g →
      (∀ q ∈ brillouinZone, g q ≤
        2 * quadraticRatio ^ 2 * (euclidNormVec q ^ 4 * radialResolvent z (euclidNormVec q) ^ 3)) →
      ∫ q in brillouinZone, g q ≤ 2 * quadraticRatio ^ 2 * radialConstant := by
    intro g hg hle
    refine setIntegral_brillouinZone_le_radialConstant
      (f := fun r => r ^ 4 * radialResolvent z r ^ 3) (by fun_prop)
      (fun r _ => mul_nonneg (by positivity) (pow_nonneg (radialResolvent_pos hz r).le 3))
      hg (by positivity) ?_ hle
    intro y hy
    have h1 := sq_mul_radialResolvent_le_one hz y
    have h2 := radialResolvent_pos hz y
    have h3 : 0 ≤ y ^ 2 * radialResolvent z y := by positivity
    have h4 : (y ^ 2 * radialResolvent z y) ^ 3 ≤ 1 := pow_le_one₀ h3 h1
    have e : y ^ 3 * (y ^ 4 * radialResolvent z y ^ 3) = y * (y ^ 2 * radialResolvent z y) ^ 3 := by
      ring
    rw [e]
    calc y * (y ^ 2 * radialResolvent z y) ^ 3 ≤ y * 1 := mul_le_mul_of_nonneg_left h4 hy.1
      _ ≤ 2 * Real.pi := by linarith [hy.2]
  have hup := key (g := fun q => resolvent z q ^ 2 - radialResolvent z (euclidNormVec q) ^ 2)
    (hc1.sub hc2) fun q hq => resolvent_sq_sub_radialResolvent_sq_le hz hq
  have hlow := key (g := fun q => radialResolvent z (euclidNormVec q) ^ 2 - resolvent z q ^ 2)
    (hc2.sub hc1) fun q hq => by
    have h1 := radialResolvent_le_resolvent hz q
    have h2 := radialResolvent_pos hz (euclidNormVec q)
    have h3 : radialResolvent z (euclidNormVec q) ^ 2 ≤ resolvent z q ^ 2 :=
      pow_le_pow_left₀ h2.le h1 2
    have h4 : 0 ≤ 2 * quadraticRatio ^ 2 *
        (euclidNormVec q ^ 4 * radialResolvent z (euclidNormVec q) ^ 3) := by
      positivity
    linarith
  rw [integral_sub (integrableOn_brillouinZone hc1) (integrableOn_brillouinZone hc2)] at hup
  rw [integral_sub (integrableOn_brillouinZone hc2) (integrableOn_brillouinZone hc1)] at hlow
  exact abs_le.2 ⟨by linarith, hup⟩
theorem volume_real_brillouinZone :
    (volume : Measure AmbientSpace).real brillouinZone = (2 * Real.pi) ^ 4 := by
  rw [Measure.real, Real.volume_Icc_pi_toReal (fun _ => by linarith [Real.pi_pos])]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring
theorem abs_setIntegral_radialResolvent_sq_sub_log_le {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    |(∫ q in brillouinZone, radialResolvent z (euclidNormVec q) ^ 2) -
        Real.pi ^ 2 * Real.log (1 / z)| ≤
      (2 * Real.pi) ^ 4 + Real.pi ^ 2 := by
  have hM := continuous_radialResolvent hz
  have hE := continuous_euclidNormVec
  have hc : Continuous fun q : AmbientSpace => radialResolvent z (euclidNormVec q) ^ 2 := by
    fun_prop
  have hB := setIntegral_euclidNormVec_le_radial (fun r => radialResolvent z r ^ 2) 1 zero_le_one
  rw [radialIntegral_radialResolvent_sq_eq hz] at hB
  have hdiff := setIntegral_sdiff (measurableSet_euclidNormVec_le 1)
    (integrableOn_brillouinZone hc) euclidNormVec_le_one_subset_brillouinZone
  have hmeas : MeasurableSet (brillouinZone \ {q : AmbientSpace | euclidNormVec q ≤ 1}) :=
    measurableSet_Icc.diff (measurableSet_euclidNormVec_le 1)
  have h0 : 0 ≤ ∫ q in brillouinZone \ {q : AmbientSpace | euclidNormVec q ≤ 1},
      radialResolvent z (euclidNormVec q) ^ 2 :=
    setIntegral_nonneg hmeas fun q _ => by positivity
  have h1 : ∫ q in brillouinZone \ {q : AmbientSpace | euclidNormVec q ≤ 1},
      radialResolvent z (euclidNormVec q) ^ 2 ≤ (2 * Real.pi) ^ 4 := by
    have hfin : (volume : Measure AmbientSpace) brillouinZone ≠ ⊤ :=
      isCompact_Icc.measure_lt_top.ne
    have hfin' : (volume : Measure AmbientSpace)
        (brillouinZone \ {q : AmbientSpace | euclidNormVec q ≤ 1}) ≠ ⊤ :=
      measure_ne_top_of_subset sdiff_subset hfin
    calc ∫ q in brillouinZone \ {q : AmbientSpace | euclidNormVec q ≤ 1},
          radialResolvent z (euclidNormVec q) ^ 2
        ≤ ∫ _ in brillouinZone \ {q : AmbientSpace | euclidNormVec q ≤ 1}, (1 : ℝ) := by
          refine setIntegral_mono_on ((integrableOn_brillouinZone hc).mono_set sdiff_subset)
            (integrableOn_const hfin') hmeas fun q hq => ?_
          have hq1 : 1 < euclidNormVec q := not_le.1 hq.2
          have h2 := radialResolvent_pos hz (euclidNormVec q)
          have h3 : radialResolvent z (euclidNormVec q) ≤ 1 := by
            unfold radialResolvent
            refine inv_le_one_of_one_le₀ ?_
            nlinarith
          exact pow_le_one₀ h2.le h3
      _ = (volume : Measure AmbientSpace).real
          (brillouinZone \ {q : AmbientSpace | euclidNormVec q ≤ 1}) := by simp
      _ ≤ (volume : Measure AmbientSpace).real brillouinZone := measureReal_mono sdiff_subset hfin
      _ = (2 * Real.pi) ^ 4 := volume_real_brillouinZone
  have hl1 : 0 ≤ Real.log (1 + z) := Real.log_nonneg (by linarith)
  have hl2 : Real.log (1 + z) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + z by linarith)
    linarith
  have hi1 : 0 ≤ z * (1 + z)⁻¹ := by positivity
  have hi2 : z * (1 + z)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by linarith)]
    linarith
  have hlog : Real.log (1 / z) = -Real.log z := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  rw [abs_le]
  constructor <;> nlinarith
theorem powerBounds_holds : PowerBounds := by
  have hb := quadraticRatio_pos
  have hD := radialConstant_pos
  set c : ℝ := ((2 * Real.pi) ^ 4)⁻¹ with hcdef
  have hc : 0 < c := by positivity
  set A : ℝ := quadraticRatio * radialConstant with hA
  set B : ℝ := quadraticRatio ^ 2 * radialConstant with hB
  set E : ℝ := quadraticRatio ^ 3 * (2 * Real.pi ^ 2 * (1 / 4)) with hE
  set F : ℝ := 2 * quadraticRatio ^ 2 * radialConstant + ((2 * Real.pi) ^ 4 + Real.pi ^ 2) with hF
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hE0 : 0 ≤ E := by positivity
  have hF0 : 0 ≤ F := by positivity
  have hcT : ∀ x y : ℝ, x ≤ y → c * x ≤ c * y := fun x y h => mul_le_mul_of_nonneg_left h hc.le
  refine ⟨c * (A + B + E + F), fun z hz => ⟨?_, ?_, ?_, ?_, ?_, fun hz1 => ?_⟩⟩
  · exact hcT _ _ ((setIntegral_resolvent_le hz).trans (by linarith))
  · exact hcT _ _ ((setIntegral_resolvent_sq_mul_norm_le hz).trans (by linarith))
  · have h := mul_setIntegral_resolvent_sq_le hz
    calc z * brillouinAverage (fun q => resolvent z q ^ 2)
        = c * (z * ∫ q in brillouinZone, resolvent z q ^ 2) := by
          unfold brillouinAverage
          ring
      _ ≤ _ := hcT _ _ (h.trans (by linarith))
  · have h := mul_setIntegral_resolvent_cube_le hz
    calc z * brillouinAverage (fun q => resolvent z q ^ 3)
        = c * (z * ∫ q in brillouinZone, resolvent z q ^ 3) := by
          unfold brillouinAverage
          ring
      _ ≤ _ := hcT _ _ (h.trans (by linarith))
  · have h := sq_mul_setIntegral_resolvent_pow_four_le hz
    calc z ^ 2 * brillouinAverage (fun q => resolvent z q ^ 4)
        = c * (z ^ 2 * ∫ q in brillouinZone, resolvent z q ^ 4) := by
          unfold brillouinAverage
          ring
      _ ≤ _ := hcT _ _ (h.trans (by linarith))
  · have h1 := abs_setIntegral_resolvent_sq_sub_le hz
    have h2 := abs_setIntegral_radialResolvent_sq_sub_log_le hz hz1
    have h3 : |(∫ q in brillouinZone, resolvent z q ^ 2) - Real.pi ^ 2 * Real.log (1 / z)| ≤ F := by
      have := abs_sub_le (∫ q in brillouinZone, resolvent z q ^ 2)
        (∫ q in brillouinZone, radialResolvent z (euclidNormVec q) ^ 2)
        (Real.pi ^ 2 * Real.log (1 / z))
      linarith
    have e : brillouinAverage (fun q => resolvent z q ^ 2) -
        1 / (16 * Real.pi ^ 2) * Real.log (1 / z) =
        c * ((∫ q in brillouinZone, resolvent z q ^ 2) - Real.pi ^ 2 * Real.log (1 / z)) := by
      unfold brillouinAverage
      rw [hcdef]
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos hc]
    exact hcT _ _ (h3.trans (by linarith))
end YangMills.Construction.Tower.MassivePropagator
end
