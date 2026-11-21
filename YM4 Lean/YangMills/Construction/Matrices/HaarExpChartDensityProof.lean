import YangMills.Construction.Matrices.SpecialUnitaryAngleBoundsProof
import YangMills.Construction.Matrices.UnitaryLogarithmClosedFormProof
import YangMills.Construction.Matrices.WeylIntegrationOnGProof
import YangMills.Construction.Towers.ChartAtOneOnTheConfigurationsProof
import Mathlib
open MeasureTheory Set Filter Topology
open scoped Matrix.Norms.L2Operator ENNReal
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2.HaarExpChart
theorem sincAngle_eq_sinc (a : ℝ) : sincAngle a = Real.sinc a := by apply _root_.YangMills.SharedProofs.p10222 <;> assumption
def sincSeriesCoeff (n : ℕ) : ℝ := (-1) ^ n / ((2 * n + 1).factorial : ℝ)
def sincSeries : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ sincSeriesCoeff
theorem sincSeries_radius : sincSeries.radius = ⊤ := by
  apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto
  · exact Eventually.of_forall fun n => by
      simp [sincSeriesCoeff, Nat.factorial_ne_zero]
  · have h : ∀ n : ℕ, ‖sincSeriesCoeff n.succ‖ / ‖sincSeriesCoeff n‖ ≤ 1 / ((n : ℝ) + 1) := by
      intro n
      have e : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by ring
      simp only [sincSeriesCoeff, norm_div, norm_pow, norm_neg, norm_one, one_pow, Nat.succ_eq_add_one,
        Real.norm_natCast, e, Nat.factorial_succ]
      push_cast
      rw [div_le_div_iff₀ (by positivity) (by positivity)] <;> try positivity
      field_simp
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    refine squeeze_zero (fun n => by positivity) h tendsto_one_div_add_atTop_nhds_zero_nat
theorem contDiff_sincSeries_sum (n : WithTop ℕ∞) : ContDiff ℝ n sincSeries.sum := by
  have hpos : 0 < sincSeries.radius := by rw [sincSeries_radius]; exact WithTop.top_pos
  have h := (sincSeries.hasFPowerSeriesOnBall hpos).analyticOnNhd
  rw [sincSeries_radius] at h
  have hu : Metric.eball (0 : ℝ) ⊤ = univ := by simp
  rw [hu] at h
  exact h.contDiff
theorem sinc_eq_sincSeries_sum_sq (a : ℝ) : Real.sinc a = sincSeries.sum (a ^ 2) := by
  have app : ∀ (q : ℝ) (n : ℕ), sincSeries n (fun _ => q) = sincSeriesCoeff n * q ^ n := by
    intro q n
    simp [sincSeries, mul_comm]
  by_cases h : a = 0
  · subst h
    simp only [FormalMultilinearSeries.sum, app, Real.sinc_zero]
    rw [tsum_eq_single 0]
    · simp [sincSeriesCoeff]
    · intro n hn
      simp [hn]
  · rw [Real.sinc_of_ne_zero h]
    simp only [FormalMultilinearSeries.sum, app]
    have := ((Real.hasSum_sin a).mul_left a⁻¹).tsum_eq
    rw [div_eq_inv_mul, ← this]
    congr 1
    ext n
    simp only [sincSeriesCoeff]
    rw [pow_succ, pow_mul]
    field_simp
theorem toMatrix_entries (Y : LieElement) :
    Y.toMatrix 1 1 = -Y.toMatrix 0 0 ∧ Y.toMatrix 1 0 = star (Y.toMatrix 0 1) ∧
      Y.toMatrix 0 0 = ((Y.toMatrix 0 0).re : ℂ) := by apply _root_.YangMills.Construction.SpinHarmonics.WeylIntegration.entries_of_lieElement <;> assumption
theorem finrank_lieElement : Module.finrank ℝ LieElement = 3 := by apply _root_.YangMills.Construction.SpinHarmonics.WeylIntegration.finrank_lieElement <;> assumption
theorem lintegral_sinc_sq_ball_pi :
    ∫⁻ Y in Metric.ball (0 : LieElement) Real.pi, ENNReal.ofReal (Real.sinc ‖Y‖ ^ 2) ∂lieLebesgue =
      ENNReal.ofReal (2 * Real.pi ^ 2) := by
  have : Nontrivial LieElement :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_lieElement]; norm_num)
  set f : ℝ → ℝ := (Iio Real.pi).indicator fun a => Real.sinc a ^ 2 with hf
  have hvol : (lieLebesgue).real (Metric.ball (0 : LieElement) 1) = Real.pi * 4 / 3 := by
    have := InnerProductSpace.volume_ball_of_dim_odd (k := 1)
      (E := LieElement) (by rw [finrank_lieElement]) (0 : LieElement) 1
    simp only [Measure.real, lieLebesgue]
    rw [finrank_lieElement] at this
    rw [this]
    norm_num [Nat.doubleFactorial]
    positivity
  have hrad : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ LieElement - 1) • f y = Real.pi / 2 := by
    rw [finrank_lieElement]
    have e1 : ∀ y ∈ Ioi (0 : ℝ), y ^ (3 - 1) • f y = (Iio Real.pi).indicator (fun y => Real.sin y ^ 2) y := by
      intro y hy
      have hy0 : y ≠ 0 := ne_of_gt hy
      by_cases h : y ∈ Iio Real.pi
      · simp only [hf, indicator_of_mem h, Real.sinc_of_ne_zero hy0, smul_eq_mul]
        norm_num
        field_simp
      · simp [hf, indicator_of_notMem h]
    rw [setIntegral_congr_fun measurableSet_Ioi e1,
      setIntegral_indicator measurableSet_Iio]
    have : Ioi (0 : ℝ) ∩ Iio Real.pi = Ioo 0 Real.pi := by ext; simp [and_comm]
    rw [this, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le Real.pi_pos.le,
      integral_sin_sq]
    simp
  have hint : ∫ Y : LieElement, f ‖Y‖ ∂lieLebesgue = 2 * Real.pi ^ 2 := by
    rw [integral_fun_norm_addHaar lieLebesgue f, hrad, hvol, finrank_lieElement]
    simp only [nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring
  have hset : Metric.ball (0 : LieElement) Real.pi = (fun Y : LieElement => ‖Y‖) ⁻¹' Iio Real.pi := by
    ext Y; simp
  have hcont : Continuous fun Y : LieElement => Real.sinc ‖Y‖ ^ 2 :=
    (Real.continuous_sinc.comp continuous_norm).pow 2
  have hfun : (fun Y : LieElement => f ‖Y‖) =
      (Metric.ball (0 : LieElement) Real.pi).indicator fun Y => Real.sinc ‖Y‖ ^ 2 := by
    ext Y
    by_cases h : ‖Y‖ < Real.pi
    · rw [indicator_of_mem (by simpa using h), hf, indicator_of_mem (by simpa using h)]
    · rw [indicator_of_notMem (by simpa using h), hf, indicator_of_notMem (by simpa using h)]
  have hib : IntegrableOn (fun Y : LieElement => Real.sinc ‖Y‖ ^ 2)
      (Metric.ball (0 : LieElement) Real.pi) lieLebesgue := by
    apply Measure.integrableOn_of_bounded (M := 1) measure_ball_lt_top.ne
      hcont.aestronglyMeasurable
    refine Eventually.of_forall fun Y => ?_
    have := Real.abs_sinc_le_one ‖Y‖
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) this
  rw [← ofReal_integral_eq_lintegral_ofReal hib
    (Eventually.of_forall fun Y => by positivity),
    ← integral_indicator Metric.isOpen_ball.measurableSet, ← hfun, hint]
def quaternionEmbed : (ℝ × LieElement) →ₗ[ℝ] ComplexMatrix2 where
  toFun x := (x.1 : ℂ) • (1 : ComplexMatrix2) + Complex.I • x.2.toMatrix
  map_add' x y := by
    have : (x + y).2.toMatrix = x.2.toMatrix + y.2.toMatrix := rfl
    simp only [this, Prod.fst_add, Complex.ofReal_add, add_smul, smul_add]
    abel
  map_smul' c x := by
    have : (c • x).2.toMatrix = c • x.2.toMatrix := rfl
    simp only [this, Prod.smul_fst, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, smul_add]
    rw [mul_smul, smul_comm Complex.I c]
    simp
theorem quaternionEmbed_apply (x : ℝ × LieElement) :
    quaternionEmbed x = (x.1 : ℂ) • (1 : ComplexMatrix2) + Complex.I • x.2.toMatrix := rfl
def quatNormSq (x : ℝ × LieElement) : ℝ := x.1 ^ 2 + ‖x.2‖ ^ 2
theorem quatNormSq_smul (c : ℝ) (x : ℝ × LieElement) : quatNormSq (c • x) = c ^ 2 * quatNormSq x := by
  simp only [quatNormSq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring
theorem quatNormSq_nonneg (x : ℝ × LieElement) : 0 ≤ quatNormSq x := by
  simp only [quatNormSq]; positivity
theorem quatNormSq_eq_zero {x : ℝ × LieElement} : quatNormSq x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h1 : x.1 ^ 2 = 0 := by
      have := sq_nonneg x.1; have := sq_nonneg ‖x.2‖; simp only [quatNormSq] at h; linarith
    have h2 : ‖x.2‖ ^ 2 = 0 := by
      have := sq_nonneg x.1; have := sq_nonneg ‖x.2‖; simp only [quatNormSq] at h; linarith
    exact Prod.ext (by simpa using h1) (by simpa using h2)
  · rintro rfl; simp [quatNormSq]
theorem det_quaternionEmbed
    (hsq : ∀ Y : LieElement, Y.toMatrix ^ 2 = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2))
    (x : ℝ × LieElement) : (quaternionEmbed x).det = (quatNormSq x : ℂ) := by
  obtain ⟨e1, -, -⟩ := toMatrix_entries x.2
  have h := congrFun (congrFun (hsq x.2) 0) 0
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one] at h
  rw [Matrix.det_fin_two, quaternionEmbed_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, smul_eq_mul, mul_one, mul_zero, zero_add,
    quatNormSq, e1]
  push_cast
  linear_combination (-Complex.I ^ 2) * h - (‖x.2‖ : ℂ) ^ 2 * Complex.I_sq
theorem star_quaternionEmbed (x : ℝ × LieElement) :
    star (quaternionEmbed x) = quaternionEmbed (x.1, -x.2) := by
  have hY : star x.2.toMatrix = x.2.toMatrix := x.2.2.1.symm
  have hn : (-x.2).toMatrix = -x.2.toMatrix := rfl
  simp only [quaternionEmbed_apply, star_add, star_smul, star_one, hY, hn, Complex.conj_I,
    Complex.conj_ofReal, RCLike.star_def]
  simp
theorem star_quaternionEmbed_eq_adjugate (x : ℝ × LieElement) :
    star (quaternionEmbed x) = (quaternionEmbed x).adjugate := by
  obtain ⟨e1, -, -⟩ := toMatrix_entries x.2
  rw [star_quaternionEmbed, Matrix.adjugate_fin_two]
  have hn : (-x.2).toMatrix = -x.2.toMatrix := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionEmbed_apply, hn, e1, Matrix.add_apply, Matrix.smul_apply]
theorem exists_quaternionEmbed_eq {A : ComplexMatrix2} (h : star A = A.adjugate) :
    ∃ x, quaternionEmbed x = A := by
  rw [Matrix.adjugate_fin_two] at h
  have h00 : star (A 0 0) = A 1 1 := by simpa using congrFun (congrFun h 0) 0
  have h01 : star (A 1 0) = -A 0 1 := by simpa using congrFun (congrFun h 0) 1
  have h10 : star (A 0 1) = -A 1 0 := by simpa using congrFun (congrFun h 1) 0
  have hm : (!![((A 0 0).im : ℂ), -Complex.I * A 0 1; -Complex.I * A 1 0, -((A 0 0).im : ℂ)] :
      ComplexMatrix2) ∈ hermitianTraceless := by
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
      · rw [show (starRingEnd ℂ) (A 1 0) = -A 0 1 from h01]; ring
      · rw [show (starRingEnd ℂ) (A 0 1) = -A 1 0 from h10]; ring
    · simp [fullTrace, Matrix.trace_fin_two]
  refine ⟨((A 0 0).re, ⟨_, hm⟩), ?_⟩
  simp only [quaternionEmbed_apply]
  have hmat : (LieElement.toMatrix ⟨_, hm⟩) =
      !![((A 0 0).im : ℂ), -Complex.I * A 0 1; -Complex.I * A 1 0, -((A 0 0).im : ℂ)] := rfl
  rw [hmat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · rw [mul_comm]; exact Complex.re_add_im (A 0 0)
  · linear_combination (-(A 0 1)) * Complex.I_sq
  · linear_combination (-(A 1 0)) * Complex.I_sq
  · rw [← h00]
    apply Complex.ext <;> simp
theorem star_eq_adjugate_of_mem_specialUnitary {U : ComplexMatrix2} (hU : U ∈ specialUnitary) :
    star U = U.adjugate := by
  have h1 : U * star U = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup hU)
  have hd : U.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp hU).2
  have h2 : U.adjugate * U = 1 := by rw [Matrix.adjugate_mul, hd, one_smul]
  calc star U = (U.adjugate * U) * star U := by rw [h2, one_mul]
    _ = U.adjugate := by rw [mul_assoc, h1, mul_one]
theorem quaternionEmbed_mem_of_quatNormSq_eq_one
    (hsq : ∀ Y : LieElement, Y.toMatrix ^ 2 = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2))
    {x : ℝ × LieElement} (h : quatNormSq x = 1) : quaternionEmbed x ∈ specialUnitary := by
  have hd : (quaternionEmbed x).det = 1 := by rw [det_quaternionEmbed hsq, h]; simp
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, hd⟩
  rw [Matrix.mem_unitaryGroup_iff, star_quaternionEmbed_eq_adjugate, Matrix.mul_adjugate, hd, one_smul]
theorem ker_quaternionEmbed
    (hsq : ∀ Y : LieElement, Y.toMatrix ^ 2 = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2)) :
    LinearMap.ker quaternionEmbed = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have h := det_quaternionEmbed hsq x
  rw [hx, Matrix.det_zero] at h
  exact quatNormSq_eq_zero.mp (by exact_mod_cast h.symm)
theorem exists_isometric_lift
    (hsq : ∀ Y : LieElement, Y.toMatrix ^ 2 = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2))
    (L : ComplexMatrix2 →ₗ[ℝ] ComplexMatrix2)
    (hQ : ∀ A : ComplexMatrix2, star A = A.adjugate → star (L A) = (L A).adjugate)
    (hd : ∀ A : ComplexMatrix2, star A = A.adjugate → (L A).det = A.det) :
    ∃ T : (ℝ × LieElement) →ₗ[ℝ] (ℝ × LieElement),
      (∀ x, quaternionEmbed (T x) = L (quaternionEmbed x)) ∧ ∀ x, quatNormSq (T x) = quatNormSq x := by
  obtain ⟨g, hg⟩ := quaternionEmbed.exists_leftInverse_of_injective (ker_quaternionEmbed hsq)
  have key : ∀ x, quaternionEmbed (g (L (quaternionEmbed x))) = L (quaternionEmbed x) := by
    intro x
    obtain ⟨y, hy⟩ := exists_quaternionEmbed_eq (hQ _ (star_quaternionEmbed_eq_adjugate x))
    rw [← hy]
    have : g (quaternionEmbed y) = y := LinearMap.congr_fun hg y
    rw [this]
  refine ⟨g ∘ₗ L ∘ₗ quaternionEmbed, key, fun x => ?_⟩
  have h1 := det_quaternionEmbed hsq (g (L (quaternionEmbed x)))
  rw [key, hd _ (star_quaternionEmbed_eq_adjugate x), det_quaternionEmbed hsq] at h1
  exact_mod_cast h1.symm
theorem toSphere_mem
    (hsq : ∀ Y : LieElement, Y.toMatrix ^ 2 = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2))
    {x : ℝ × LieElement} (hx : x ≠ 0) : (√(quatNormSq x))⁻¹ • quaternionEmbed x ∈ specialUnitary := by
  rw [← map_smul]
  apply quaternionEmbed_mem_of_quatNormSq_eq_one hsq
  have hp : 0 < quatNormSq x :=
    lt_of_le_of_ne (quatNormSq_nonneg x) (fun h => hx (quatNormSq_eq_zero.mp h.symm))
  rw [quatNormSq_smul, inv_pow, Real.sq_sqrt hp.le, inv_mul_cancel₀ hp.ne']
open Classical in
def toSphere (x : ℝ × LieElement) : specialUnitary :=
  if h : (√(quatNormSq x))⁻¹ • quaternionEmbed x ∈ specialUnitary then ⟨_, h⟩ else 1
theorem coe_toSphere
    (hsq : ∀ Y : LieElement, Y.toMatrix ^ 2 = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2))
    {x : ℝ × LieElement} (hx : x ≠ 0) :
    (toSphere x : ComplexMatrix2) = (√(quatNormSq x))⁻¹ • quaternionEmbed x := by
  simp only [toSphere, dif_pos (toSphere_mem hsq hx)]
theorem continuous_quatNormSq : Continuous quatNormSq :=
  (continuous_fst.pow 2).add ((continuous_norm.comp continuous_snd).pow 2)
theorem continuous_quaternionEmbed : Continuous quaternionEmbed :=
  LinearMap.continuous_of_finiteDimensional _
theorem measurable_toSphere
    (hsq : ∀ Y : LieElement, Y.toMatrix ^ 2 = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2)) :
    Measurable toSphere := by
  apply measurable_of_continuousOn_compl_singleton (0 : ℝ × LieElement)
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous fun x : ({0}ᶜ : Set (ℝ × LieElement)) =>
      (√(quatNormSq x.1))⁻¹ • quaternionEmbed x.1 := by
    have h1 : Continuous fun x : ({0}ᶜ : Set (ℝ × LieElement)) => (√(quatNormSq x.1))⁻¹ := by
      refine Continuous.inv₀ ((continuous_quatNormSq.comp continuous_subtype_val).sqrt) ?_
      intro x
      have hx : x.1 ≠ 0 := x.2
      have hp : 0 < quatNormSq x.1 :=
        lt_of_le_of_ne (quatNormSq_nonneg _) (fun h => hx (quatNormSq_eq_zero.mp h.symm))
      exact (Real.sqrt_pos.mpr hp).ne'
    exact h1.smul (continuous_quaternionEmbed.comp continuous_subtype_val)
  have hm : ∀ x : ({0}ᶜ : Set (ℝ × LieElement)),
      (√(quatNormSq x.1))⁻¹ • quaternionEmbed x.1 ∈ specialUnitary :=
    fun x => toSphere_mem hsq x.2
  convert hc.subtype_mk hm using 1
  ext1 x
  apply Subtype.ext
  exact coe_toSphere hsq x.2
open scoped InnerProductSpace
def rankTwoPerturb (α β γ δ ε : ℝ) (Y : LieElement) : (ℝ × LieElement) →L[ℝ] (ℝ × LieElement) :=
  (α • ContinuousLinearMap.fst ℝ ℝ LieElement +
      β • (innerSL ℝ Y).comp (ContinuousLinearMap.snd ℝ ℝ LieElement)).prod
    ((ContinuousLinearMap.toSpanSingleton ℝ Y).comp
        (γ • ContinuousLinearMap.fst ℝ ℝ LieElement +
          ε • (innerSL ℝ Y).comp (ContinuousLinearMap.snd ℝ ℝ LieElement)) +
      δ • ContinuousLinearMap.snd ℝ ℝ LieElement)
theorem rankTwoPerturb_apply (α β γ δ ε : ℝ) (Y : LieElement) (x : ℝ × LieElement) :
    rankTwoPerturb α β γ δ ε Y x =
      (α * x.1 + β * ⟪Y, x.2⟫_ℝ, (γ * x.1 + ε * ⟪Y, x.2⟫_ℝ) • Y + δ • x.2) := by
  simp [rankTwoPerturb, add_smul, mul_smul]
theorem det_rankTwoPerturb_matrix (α β γ δ ε y₀ y₁ y₂ : ℝ) :
    (!![α, β * y₀, β * y₁, β * y₂;
        γ * y₀, ε * y₀ * y₀ + δ, ε * y₀ * y₁, ε * y₀ * y₂;
        γ * y₁, ε * y₁ * y₀, ε * y₁ * y₁ + δ, ε * y₁ * y₂;
        γ * y₂, ε * y₂ * y₀, ε * y₂ * y₁, ε * y₂ * y₂ + δ] : Matrix (Fin 4) (Fin 4) ℝ).det =
      δ ^ 2 * (α * (δ + ε * (y₀ ^ 2 + y₁ ^ 2 + y₂ ^ 2)) - β * γ * (y₀ ^ 2 + y₁ ^ 2 + y₂ ^ 2)) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring
theorem det_rankTwoPerturb (α β γ δ ε : ℝ) (Y : LieElement) :
    (rankTwoPerturb α β γ δ ε Y).det = δ ^ 2 * (α * (δ + ε * ‖Y‖ ^ 2) - β * γ * ‖Y‖ ^ 2) := by
  let o : OrthonormalBasis (Fin 3) ℝ LieElement :=
    (stdOrthonormalBasis ℝ LieElement).reindex (finCongr finrank_lieElement)
  let e : (ℝ × LieElement) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
    (LinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ)
      (o.repr.toLinearEquiv ≪≫ₗ WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ))) ≪≫ₗ
      Fin.consLinearEquiv ℝ (fun _ : Fin 4 => ℝ)
  have e0 : ∀ x, e x 0 = x.1 := fun x => rfl
  have es : ∀ x (i : Fin 3), e x i.succ = ⟪o i, x.2⟫_ℝ := fun x i => by
    change o.repr x.2 i = _
    simp [OrthonormalBasis.repr_apply_apply]
  set y : Fin 3 → ℝ := fun i => ⟪o i, Y⟫_ℝ with hy
  have hin : ∀ v : LieElement, ⟪Y, v⟫_ℝ = y 0 * ⟪o 0, v⟫_ℝ + y 1 * ⟪o 1, v⟫_ℝ + y 2 * ⟪o 2, v⟫_ℝ := by
    intro v
    have := o.sum_inner_mul_inner Y v
    rw [Fin.sum_univ_three] at this
    rw [← this]
    simp only [hy, real_inner_comm]
  have hq : ‖Y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    have := hin Y
    rw [real_inner_self_eq_norm_sq] at this
    rw [this]
    simp only [hy]
    ring
  set M : Matrix (Fin 4) (Fin 4) ℝ :=
    !![α, β * y 0, β * y 1, β * y 2;
        γ * y 0, ε * y 0 * y 0 + δ, ε * y 0 * y 1, ε * y 0 * y 2;
        γ * y 1, ε * y 1 * y 0, ε * y 1 * y 1 + δ, ε * y 1 * y 2;
        γ * y 2, ε * y 2 * y 0, ε * y 2 * y 1, ε * y 2 * y 2 + δ] with hM
  have hconj : (e : (ℝ × LieElement) →ₗ[ℝ] (Fin 4 → ℝ)) ∘ₗ
      ((rankTwoPerturb α β γ δ ε Y : (ℝ × LieElement) →L[ℝ] (ℝ × LieElement)) :
        (ℝ × LieElement) →ₗ[ℝ] (ℝ × LieElement)) ∘ₗ
      (e.symm : (Fin 4 → ℝ) →ₗ[ℝ] (ℝ × LieElement)) = Matrix.toLin' M := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := e.surjective z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe, Matrix.toLin'_apply, rankTwoPerturb_apply]
    have e1 : ∀ x, e x 1 = ⟪o 0, x.2⟫_ℝ := fun x => es x 0
    have e2 : ∀ x, e x 2 = ⟪o 1, x.2⟫_ℝ := fun x => es x 1
    have e3 : ∀ x, e x 3 = ⟪o 2, x.2⟫_ℝ := fun x => es x 2
    funext i
    fin_cases i
    · change e _ 0 = _
      rw [e0]
      simp [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_four, e0, e1, e2, e3, hin]
      ring
    · change e _ 1 = _
      rw [e1]
      simp [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_four, e0, e1, e2, e3, hin,
        inner_add_right, inner_smul_right]
      ring
    · change e _ 2 = _
      rw [e2]
      simp [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_four, e0, e1, e2, e3, hin,
        inner_add_right, inner_smul_right]
      ring
    · change e _ 3 = _
      rw [e3]
      simp [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_four, e0, e1, e2, e3, hin,
        inner_add_right, inner_smul_right]
      ring
  rw [ContinuousLinearMap.det, ← LinearMap.det_conj _ e, hconj, LinearMap.det_toLin', hM,
    det_rankTwoPerturb_matrix, hq]
theorem sinc_mul_self_eq_sin (a : ℝ) : Real.sinc a * a = Real.sin a := by apply _root_.YangMills.Construction.PeriodicLattice.ElementaryStepFacts.sinc_mul_self_eq_sin <;> assumption
def polarExpMap (x : ℝ × LieElement) : ℝ × LieElement :=
  (x.1 * Real.cos ‖x.2‖, (x.1 * Real.sinc ‖x.2‖) • x.2)
theorem quatNormSq_polarExpMap (x : ℝ × LieElement) : quatNormSq (polarExpMap x) = x.1 ^ 2 := by
  simp only [quatNormSq, polarExpMap, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h1 := Real.sin_sq_add_cos_sq ‖x.2‖
  rw [← sinc_mul_self_eq_sin] at h1
  linear_combination (x.1 ^ 2) * h1
theorem sinc_pos_of_nonneg_of_lt_pi {a : ℝ} (h0 : 0 ≤ a) (h1 : a < Real.pi) : 0 < Real.sinc a := by apply _root_.YangMills.SharedProofs.p1819 <;> assumption
def polarSource : Set (ℝ × LieElement) :=
  Ioo 0 1 ×ˢ (Metric.ball (0 : LieElement) Real.pi \ {0})
theorem polarExpMap_injOn : InjOn polarExpMap polarSource := by
  rintro ⟨r, Y⟩ ⟨⟨hr0, hr1⟩, hY, hY0⟩ ⟨r', Y'⟩ ⟨⟨hr0', hr1'⟩, hY', hY0'⟩ h
  simp only [mem_singleton_iff, Metric.mem_ball, dist_zero_right] at *
  have hsq := congrArg quatNormSq h
  rw [quatNormSq_polarExpMap, quatNormSq_polarExpMap] at hsq
  have hrr : r = r' := by
    have := (sq_eq_sq₀ hr0.le hr0'.le).mp hsq
    exact this
  subst hrr
  have h1 : r * Real.cos ‖Y‖ = r * Real.cos ‖Y'‖ := congrArg Prod.fst h
  have h2 : (r * Real.sinc ‖Y‖) • Y = (r * Real.sinc ‖Y'‖) • Y' := congrArg Prod.snd h
  have hc : Real.cos ‖Y‖ = Real.cos ‖Y'‖ := mul_left_cancel₀ hr0.ne' h1
  have ha : ‖Y‖ = ‖Y'‖ :=
    Real.injOn_cos ⟨norm_nonneg _, hY.le⟩ ⟨norm_nonneg _, hY'.le⟩ hc
  rw [ha] at h2
  have hs : r * Real.sinc ‖Y'‖ ≠ 0 :=
    (mul_pos hr0 (sinc_pos_of_nonneg_of_lt_pi (norm_nonneg _) hY')).ne'
  have : Y = Y' := smul_right_injective _ hs h2
  rw [this]
theorem polarExpMap_image :
    polarExpMap '' polarSource = {x | x.2 ≠ 0 ∧ quatNormSq x < 1} := by
  ext ⟨t, Z⟩
  constructor
  · rintro ⟨⟨r, Y⟩, ⟨⟨hr0, hr1⟩, hY, hY0⟩, h⟩
    simp only [mem_singleton_iff, Metric.mem_ball, dist_zero_right] at hY hY0
    rw [← h]
    refine ⟨?_, ?_⟩
    · change (r * Real.sinc ‖Y‖) • Y ≠ 0
      exact smul_ne_zero (mul_pos hr0 (sinc_pos_of_nonneg_of_lt_pi (norm_nonneg _) hY)).ne' hY0
    · rw [quatNormSq_polarExpMap]
      change r ^ 2 < 1
      nlinarith
  · rintro ⟨hZ, hN⟩
    change Z ≠ 0 at hZ
    have hZp : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
    have hNp : 0 < quatNormSq (t, Z) := by
      simp only [quatNormSq]; positivity
    set r := √(quatNormSq (t, Z)) with hr
    have hr0 : 0 < r := Real.sqrt_pos.mpr hNp
    have hr2 : r ^ 2 = t ^ 2 + ‖Z‖ ^ 2 := Real.sq_sqrt hNp.le
    have hr1 : r < 1 := by
      rw [hr, Real.sqrt_lt' one_pos]; simpa using hN
    have hlt : |t / r| < 1 := by
      rw [abs_div, abs_of_pos hr0, div_lt_one hr0]
      apply abs_lt_of_sq_lt_sq _ hr0.le
      nlinarith
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hlt
    set a := Real.arccos (t / r) with ha
    have ha0 : 0 < a := Real.arccos_pos.mpr hhi
    have haπ : a < Real.pi := by
      rcases (Real.arccos_le_pi (t / r)).eq_or_lt with h | h
      · exact absurd (Real.arccos_eq_pi.mp h) (by linarith)
      · exact h
    have hcos : Real.cos a = t / r := Real.cos_arccos hlo.le hhi.le
    have hsin : r * Real.sin a = ‖Z‖ := by
      have hs : 0 ≤ Real.sin a := (Real.sin_pos_of_pos_of_lt_pi ha0 haπ).le
      have h1 := Real.sin_sq_add_cos_sq a
      rw [hcos] at h1
      have h2 : (r * Real.sin a) ^ 2 = ‖Z‖ ^ 2 := by
        field_simp at h1
        nlinarith
      exact (sq_eq_sq₀ (by positivity) (norm_nonneg _)).mp h2
    have hYn : ‖(a / ‖Z‖) • Z‖ = a := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      field_simp
    refine ⟨(r, (a / ‖Z‖) • Z), ⟨⟨hr0, hr1⟩, ?_, ?_⟩, ?_⟩
    · change (a / ‖Z‖) • Z ∈ Metric.ball (0 : LieElement) Real.pi
      simpa [hYn] using haπ
    · change (a / ‖Z‖) • Z ∉ ({0} : Set LieElement)
      simp only [mem_singleton_iff]
      exact smul_ne_zero (by positivity) hZ
    · simp only [polarExpMap, hYn, hcos]
      refine Prod.ext ?_ ?_
      · change r * (t / r) = t
        field_simp
      · change (r * Real.sinc a) • (a / ‖Z‖) • Z = Z
        rw [smul_smul]
        have : r * Real.sinc a * (a / ‖Z‖) = 1 := by
          have h3 := sinc_mul_self_eq_sin a
          calc r * Real.sinc a * (a / ‖Z‖) = r * (Real.sinc a * a) / ‖Z‖ := by ring
            _ = 1 := by rw [h3, hsin]; field_simp
        rw [this, one_smul]
theorem hasDerivAt_sinc_of_ne_zero {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt Real.sinc ((a * Real.cos a - Real.sin a) / a ^ 2) a := by
  have h : HasDerivAt (fun t => Real.sin t / t) ((Real.cos a * a - Real.sin a * 1) / a ^ 2) a :=
    (Real.hasDerivAt_sin a).div (hasDerivAt_id a) ha
  have e : Real.sinc =ᶠ[𝓝 a] fun t => Real.sin t / t := by
    filter_upwards [isOpen_ne.mem_nhds ha] with t ht
    exact Real.sinc_of_ne_zero ht
  exact (h.congr_of_eventuallyEq e).congr_deriv (by ring)
theorem hasFDerivAt_norm_of_ne_zero {Y : LieElement} (h : Y ≠ 0) :
    HasFDerivAt (fun Z : LieElement => ‖Z‖) (‖Y‖⁻¹ • innerSL ℝ Y) Y := by
  have hp : 0 < ‖Y‖ := norm_pos_iff.mpr h
  have h1 := (hasStrictFDerivAt_norm_sq Y).hasFDerivAt.sqrt (pow_ne_zero 2 hp.ne')
  simp only [Real.sqrt_sq (norm_nonneg _)] at h1
  refine h1.congr_fderiv ?_
  ext v
  simp
  field_simp
def polarExpDeriv (x : ℝ × LieElement) : (ℝ × LieElement) →L[ℝ] (ℝ × LieElement) :=
  rankTwoPerturb (Real.cos ‖x.2‖) (-x.1 * Real.sin ‖x.2‖ / ‖x.2‖) (Real.sinc ‖x.2‖)
    (x.1 * Real.sinc ‖x.2‖)
    (x.1 * ((‖x.2‖ * Real.cos ‖x.2‖ - Real.sin ‖x.2‖) / ‖x.2‖ ^ 2) / ‖x.2‖) x.2
theorem hasFDerivAt_polarExpMap {x : ℝ × LieElement} (hx : x.2 ≠ 0) :
    HasFDerivAt polarExpMap (polarExpDeriv x) x := by
  have ha : ‖x.2‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hn : HasFDerivAt (fun z : ℝ × LieElement => ‖z.2‖)
      ((‖x.2‖⁻¹ • innerSL ℝ x.2).comp (ContinuousLinearMap.snd ℝ ℝ LieElement)) x :=
    (hasFDerivAt_norm_of_ne_zero hx).comp x hasFDerivAt_snd
  have hcos := (Real.hasDerivAt_cos ‖x.2‖).comp_hasFDerivAt x hn
  have hsinc := (hasDerivAt_sinc_of_ne_zero ha).comp_hasFDerivAt x hn
  have hfst : HasFDerivAt (fun z : ℝ × LieElement => z.1)
      (ContinuousLinearMap.fst ℝ ℝ LieElement) x := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun z : ℝ × LieElement => z.2)
      (ContinuousLinearMap.snd ℝ ℝ LieElement) x := hasFDerivAt_snd
  have h1 := hfst.mul hcos
  have h2 := (hfst.mul hsinc).smul hsnd
  refine (h1.prodMk h2).congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro z
  rw [polarExpDeriv, rankTwoPerturb_apply]
  refine Prod.ext ?_ ?_
  · simp
    field_simp
    ring
  · simp
    module
theorem det_polarExpDeriv {x : ℝ × LieElement} (hx : x.2 ≠ 0) :
    (polarExpDeriv x).det = x.1 ^ 3 * Real.sinc ‖x.2‖ ^ 2 := by
  have ha : ‖x.2‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [polarExpDeriv, det_rankTwoPerturb]
  set a := ‖x.2‖
  have hS : Real.sin a = Real.sinc a * a := (sinc_mul_self_eq_sin a).symm
  have h1 := Real.sin_sq_add_cos_sq a
  rw [hS] at h1 ⊢
  set S := Real.sinc a
  set c := Real.cos a
  have e1 : x.1 * S + x.1 * ((a * c - S * a) / a ^ 2) / a * a ^ 2 = x.1 * c := by
    field_simp
    ring
  have e2 : -x.1 * (S * a) / a * S * a ^ 2 = -x.1 * (S * a) ^ 2 := by
    field_simp
  rw [e1, e2]
  linear_combination (x.1 ^ 3 * S ^ 2) * h1
def punctUnitBall : Set (ℝ × LieElement) := {x | x ≠ 0 ∧ quatNormSq x < 1}
theorem isOpen_punctUnitBall : IsOpen punctUnitBall :=
  isOpen_ne.inter (isOpen_lt continuous_quatNormSq continuous_const)
theorem punctUnitBall_subset_closedBall : punctUnitBall ⊆ Metric.closedBall 0 1 := by
  rintro x ⟨-, h⟩
  simp only [quatNormSq] at h
  rw [mem_closedBall_zero_iff, Prod.norm_def]
  apply max_le
  · rw [Real.norm_eq_abs]
    exact (sq_le_one_iff_abs_le_one _).mp (by nlinarith [sq_nonneg ‖x.2‖])
  · exact (sq_le_one_iff₀ (norm_nonneg _)).mp (by nlinarith [sq_nonneg x.1])
theorem volume_punctUnitBall_lt_top : volume punctUnitBall < ∞ :=
  (measure_mono punctUnitBall_subset_closedBall).trans_lt measure_closedBall_lt_top
theorem volume_punctUnitBall_pos : 0 < volume punctUnitBall := by
  refine isOpen_punctUnitBall.measure_pos _ ⟨((1 / 2 : ℝ), 0), ?_, ?_⟩
  · intro h
    have := congrArg Prod.fst h
    norm_num at this
  · simp only [quatNormSq]
    norm_num
instance instIsAddHaarVolumeProdLie : (volume : Measure (ℝ × LieElement)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance
theorem map_volume_restrict_punctUnitBall (T : (ℝ × LieElement) →ₗ[ℝ] (ℝ × LieElement))
    (hT : ∀ x, quatNormSq (T x) = quatNormSq x) :
    Measure.map T (volume.restrict punctUnitBall) = volume.restrict punctUnitBall := by
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h := hT x
    rw [hx, quatNormSq_eq_zero.mpr rfl] at h
    exact quatNormSq_eq_zero.mp h.symm
  have hdet : LinearMap.det T ≠ 0 := by
    have h := (LinearEquiv.ofInjectiveEndo T hinj).isUnit_det'
    have e : ((LinearEquiv.ofInjectiveEndo T hinj : _ ≃ₗ[ℝ] _) :
        (ℝ × LieElement) →ₗ[ℝ] (ℝ × LieElement)) = T := LinearMap.ext fun x => rfl
    rw [e] at h
    exact h.ne_zero
  have hpre : T ⁻¹' punctUnitBall = punctUnitBall := by
    ext x
    simp [punctUnitBall, hT, map_eq_zero_iff T hinj]
  have hc : ENNReal.ofReal |(LinearMap.det T)⁻¹| = 1 := by
    have h := Measure.addHaar_preimage_linearMap (volume : Measure (ℝ × LieElement)) hdet punctUnitBall
    rw [hpre] at h
    have h' : 1 * volume punctUnitBall =
        ENNReal.ofReal |(LinearMap.det T)⁻¹| * volume punctUnitBall := by rw [one_mul]; exact h
    exact ((ENNReal.mul_left_inj volume_punctUnitBall_pos.ne'
      volume_punctUnitBall_lt_top.ne).mp h').symm
  have hm : Measurable T := (LinearMap.continuous_of_finiteDimensional T).measurable
  ext s hs
  rw [Measure.map_apply hm hs, Measure.restrict_apply (hm hs), Measure.restrict_apply hs]
  have : T ⁻¹' s ∩ punctUnitBall = T ⁻¹' (s ∩ punctUnitBall) := by rw [preimage_inter, hpre]
  rw [this, Measure.addHaar_preimage_linearMap volume hdet, hc, one_mul]
def sphereMeasure : Measure specialUnitary := Measure.map toSphere (volume.restrict punctUnitBall)
theorem map_sphereMeasure
    (hsq : ∀ Y : LieElement, Y.toMatrix ^ 2 = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2))
    (L : ComplexMatrix2 →ₗ[ℝ] ComplexMatrix2)
    (hQ : ∀ A : ComplexMatrix2, star A = A.adjugate → star (L A) = (L A).adjugate)
    (hd : ∀ A : ComplexMatrix2, star A = A.adjugate → (L A).det = A.det)
    (g : specialUnitary → specialUnitary) (hg : Measurable g)
    (hgL : ∀ U : specialUnitary, (g U : ComplexMatrix2) = L U) :
    Measure.map g sphereMeasure = sphereMeasure := by
  obtain ⟨T, hT1, hT2⟩ := exists_isometric_lift hsq L hQ hd
  have hr := measurable_toSphere hsq
  have hTm : Measurable T := (LinearMap.continuous_of_finiteDimensional T).measurable
  have hpt : ∀ x, x ≠ 0 → toSphere (T x) = g (toSphere x) := by
    intro x hx
    have hTx : T x ≠ 0 := fun h => hx (quatNormSq_eq_zero.mp (by
      rw [← hT2, h]; exact quatNormSq_eq_zero.mpr rfl))
    apply Subtype.ext
    rw [hgL, coe_toSphere hsq hx, coe_toSphere hsq hTx, hT2, hT1, map_smul]
  rw [sphereMeasure, Measure.map_map hg hr]
  have hae : g ∘ toSphere =ᵐ[volume.restrict punctUnitBall] toSphere ∘ T := by
    filter_upwards [ae_restrict_mem isOpen_punctUnitBall.measurableSet] with x hx
    exact (hpt x hx.1).symm
  rw [Measure.map_congr hae, ← Measure.map_map hr hTm, map_volume_restrict_punctUnitBall T hT2]
def twoSidedMul (T T' : ComplexMatrix2) : ComplexMatrix2 →ₗ[ℝ] ComplexMatrix2 where
  toFun A := T * A * T'
  map_add' A B := by simp [mul_add, add_mul]
  map_smul' c A := by simp
def conjTransposeRLinear : ComplexMatrix2 →ₗ[ℝ] ComplexMatrix2 where
  toFun A := star A
  map_add' A B := star_add A B
  map_smul' c A := by simp [star_smul]
theorem map_sphereMeasure_twoSidedMul
    (hsq : ∀ Y : LieElement, Y.toMatrix ^ 2 = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2))
    (T T' : specialUnitary) :
    Measure.map (fun U : specialUnitary => T * U * T') sphereMeasure = sphereMeasure := by
  have hT := star_eq_adjugate_of_mem_specialUnitary T.2
  have hT' := star_eq_adjugate_of_mem_specialUnitary T'.2
  have dT : (T : ComplexMatrix2).det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp T.2).2
  have dT' : (T' : ComplexMatrix2).det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp T'.2).2
  refine map_sphereMeasure hsq (twoSidedMul T T') ?_ ?_ _ ?_ (fun U => rfl)
  · intro A hA
    change star ((T : ComplexMatrix2) * A * T') = ((T : ComplexMatrix2) * A * T').adjugate
    rw [star_mul, star_mul, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hA, hT, hT']
  · intro A _
    change ((T : ComplexMatrix2) * A * T').det = A.det
    rw [Matrix.det_mul, Matrix.det_mul, dT, dT', one_mul, mul_one]
  · exact ((continuous_const.mul continuous_id).mul continuous_const).measurable
theorem map_sphereMeasure_inv
    (hsq : ∀ Y : LieElement, Y.toMatrix ^ 2 = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2)) :
    Measure.map (fun U : specialUnitary => U⁻¹) sphereMeasure = sphereMeasure := by
  refine map_sphereMeasure hsq conjTransposeRLinear ?_ ?_ _ continuous_inv.measurable (fun U => rfl)
  · intro A hA
    change star (star A) = (star A).adjugate
    rw [star_star, hA, Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro A hA
    change (star A).det = A.det
    rw [hA, Matrix.det_adjugate]
    simp
theorem coe_expChart (hmem : ∀ Y : LieElement, matExp (Complex.I • Y.toMatrix) ∈ specialUnitary)
    (Y : LieElement) : (expChart Y : ComplexMatrix2) = matExp (Complex.I • Y.toMatrix) := by
  simp only [expChart, dif_pos (hmem Y)]
theorem continuous_toMatrix : Continuous LieElement.toMatrix := by apply _root_.YangMills.Construction.Tower.IdentityChart.continuous_toMatrix <;> assumption
theorem measurable_expChart
    (hmem : ∀ Y : LieElement, matExp (Complex.I • Y.toMatrix) ∈ specialUnitary)
    (hexp : ∀ Y : LieElement, matExp (Complex.I • Y.toMatrix) =
      (Real.cos ‖Y‖ : ℂ) • (1 : ComplexMatrix2) + (Complex.I * (Real.sinc ‖Y‖ : ℂ)) • Y.toMatrix) :
    Measurable expChart := by
  have hc : Continuous fun Y : LieElement => matExp (Complex.I • Y.toMatrix) := by
    simp only [hexp]
    have c1 : Continuous fun Y : LieElement => ((Real.cos ‖Y‖ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_norm)
    have c2 : Continuous fun Y : LieElement => ((Real.sinc ‖Y‖ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_sinc.comp continuous_norm)
    exact (c1.smul continuous_const).add ((continuous_const.mul c2).smul continuous_toMatrix)
  have : Continuous expChart := by
    convert hc.subtype_mk hmem using 1
    ext1 Y
    exact Subtype.ext (coe_expChart hmem Y)
  exact this.measurable
theorem toSphere_polarExpMap
    (hsq : ∀ Y : LieElement, Y.toMatrix ^ 2 = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2))
    (hmem : ∀ Y : LieElement, matExp (Complex.I • Y.toMatrix) ∈ specialUnitary)
    (hexp : ∀ Y : LieElement, matExp (Complex.I • Y.toMatrix) =
      (Real.cos ‖Y‖ : ℂ) • (1 : ComplexMatrix2) + (Complex.I * (Real.sinc ‖Y‖ : ℂ)) • Y.toMatrix)
    {x : ℝ × LieElement} (hr : 0 < x.1) : toSphere (polarExpMap x) = expChart x.2 := by
  have hne : polarExpMap x ≠ 0 := by
    intro h
    have h1 := quatNormSq_polarExpMap x
    rw [h, quatNormSq_eq_zero.mpr rfl] at h1
    have : x.1 ^ 2 > 0 := by positivity
    linarith
  apply Subtype.ext
  rw [coe_toSphere hsq hne, quatNormSq_polarExpMap, Real.sqrt_sq hr.le, coe_expChart hmem, hexp,
    quaternionEmbed_apply]
  have hm : ((polarExpMap x).2).toMatrix = (x.1 * Real.sinc ‖x.2‖) • x.2.toMatrix := rfl
  have h1 : (polarExpMap x).1 = x.1 * Real.cos ‖x.2‖ := rfl
  rw [hm, h1]
  have hx : (x.1 : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  field_simp
def expChartMeasure : Measure specialUnitary :=
  Measure.map expChart
    ((lieLebesgue.restrict (Metric.ball (0 : LieElement) Real.pi)).withDensity
      fun Y => ENNReal.ofReal (Real.sinc ‖Y‖ ^ 2))
theorem measurable_ofReal_sinc_sq :
    Measurable fun Y : LieElement => ENNReal.ofReal (Real.sinc ‖Y‖ ^ 2) :=
  ENNReal.measurable_ofReal.comp
    ((Real.continuous_sinc.comp continuous_norm).pow 2).measurable
theorem lintegral_cube_Ioo_zero_one :
    ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ 3) = ENNReal.ofReal (1 / 4) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
    norm_num
  · exact (continuous_pow 3).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  · exact (ae_restrict_iff' measurableSet_Ioo).mpr
      (Eventually.of_forall fun r hr => by have := hr.1; positivity)
theorem volume_setOf_snd_eq_zero : volume {x : ℝ × LieElement | x.2 = 0} = 0 := by
  have : Nontrivial LieElement :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_lieElement]; norm_num)
  have h : {x : ℝ × LieElement | x.2 = 0} = univ ×ˢ {0} := by ext x; simp
  rw [h, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, mul_zero]
theorem sphereMeasure_apply
    (hsq : ∀ Y : LieElement, Y.toMatrix ^ 2 = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2))
    (hmem : ∀ Y : LieElement, matExp (Complex.I • Y.toMatrix) ∈ specialUnitary)
    (hexp : ∀ Y : LieElement, matExp (Complex.I • Y.toMatrix) =
      (Real.cos ‖Y‖ : ℂ) • (1 : ComplexMatrix2) + (Complex.I * (Real.sinc ‖Y‖ : ℂ)) • Y.toMatrix)
    (A : Set specialUnitary) (hA : MeasurableSet A) :
    sphereMeasure A = ENNReal.ofReal (1 / 4) * expChartMeasure A := by
  have : Nontrivial LieElement :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_lieElement]; norm_num)
  have hr := measurable_toSphere hsq
  have hge := measurable_expChart hmem hexp
  have hB : MeasurableSet (toSphere ⁻¹' A) := hr hA
  have hD : MeasurableSet polarSource :=
    measurableSet_Ioo.prod (Metric.isOpen_ball.measurableSet.diff (measurableSet_singleton _))
  have hset : polarExpMap '' polarSource = punctUnitBall \ {x | x.2 = 0} := by
    rw [polarExpMap_image]
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨fun h => h1 (by rw [h]; rfl), h2⟩, h1⟩
    · rintro ⟨⟨-, h2⟩, h1⟩
      exact ⟨h1, h2⟩
  have hres : volume.restrict punctUnitBall = volume.restrict (polarExpMap '' polarSource) := by
    rw [hset]
    exact Measure.restrict_congr_set (sdiff_null_ae_eq_self volume_setOf_snd_eq_zero).symm
  have hind : MeasurableSet (expChart ⁻¹' A) := hge hA
  rw [sphereMeasure, Measure.map_apply hr hA, hres, ← lintegral_indicator_one hB,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD
      (fun x hx => (hasFDerivAt_polarExpMap (x := x) (by
        have := hx.2.2; simpa using this)).hasFDerivWithinAt) polarExpMap_injOn]
  have hcongr : ∀ x ∈ polarSource,
      ENNReal.ofReal |(polarExpDeriv x).det| * (toSphere ⁻¹' A).indicator 1 (polarExpMap x) =
        ENNReal.ofReal (x.1 ^ 3) * (ENNReal.ofReal (Real.sinc ‖x.2‖ ^ 2) *
          (expChart ⁻¹' A).indicator 1 x.2) := by
    intro x hx
    have h0 : x.2 ≠ 0 := by have := hx.2.2; simpa using this
    have hp : 0 < x.1 := hx.1.1
    rw [det_polarExpDeriv h0, abs_of_nonneg (by positivity), ENNReal.ofReal_mul (by positivity),
      mul_assoc]
    congr 2
    have hiff : polarExpMap x ∈ toSphere ⁻¹' A ↔ x.2 ∈ expChart ⁻¹' A := by
      simp only [mem_preimage, toSphere_polarExpMap hsq hmem hexp hp]
    by_cases h : x.2 ∈ expChart ⁻¹' A
    · rw [indicator_of_mem h, indicator_of_mem (hiff.mpr h)]; rfl
    · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hiff.mp h'))]
  rw [setLIntegral_congr_fun hD hcongr, polarSource, Measure.volume_eq_prod,
    ← Measure.prod_restrict]
  rw [lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal (r ^ 3))
    (g := fun Y : LieElement => ENNReal.ofReal (Real.sinc ‖Y‖ ^ 2) *
      (expChart ⁻¹' A).indicator 1 Y), lintegral_cube_Ioo_zero_one]
  · congr 1
    rw [expChartMeasure, Measure.map_apply hge hA,
      withDensity_apply _ hind,
      Measure.restrict_congr_set (sdiff_null_ae_eq_self (s := Metric.ball (0 : LieElement) Real.pi)
        (measure_singleton (0 : LieElement)))]
    rw [← lintegral_indicator hind]
    refine lintegral_congr fun Y => ?_
    by_cases h : Y ∈ expChart ⁻¹' A
    · rw [indicator_of_mem h, indicator_of_mem h]; simp
    · rw [indicator_of_notMem h, indicator_of_notMem h]; simp
  · exact (ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable
  · exact (measurable_ofReal_sinc_sq.mul (measurable_one.indicator hind)).aemeasurable
instance instIsHaarMeasureHaarProb : haarProb.IsHaarMeasure := by
  unfold haarProb
  infer_instance
theorem expChartMeasure_univ
    (hmem : ∀ Y : LieElement, matExp (Complex.I • Y.toMatrix) ∈ specialUnitary)
    (hexp : ∀ Y : LieElement, matExp (Complex.I • Y.toMatrix) =
      (Real.cos ‖Y‖ : ℂ) • (1 : ComplexMatrix2) + (Complex.I * (Real.sinc ‖Y‖ : ℂ)) • Y.toMatrix) :
    expChartMeasure univ = ENNReal.ofReal (2 * Real.pi ^ 2) := by
  rw [expChartMeasure, Measure.map_apply (measurable_expChart hmem hexp) MeasurableSet.univ,
    preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact lintegral_sinc_sq_ball_pi
theorem exists_sphereMeasure_eq_smul
    (hsq : ∀ Y : LieElement, Y.toMatrix ^ 2 = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2)) :
    ∃ c : NNReal, sphereMeasure = c • haarProb := by
  have hfin : IsFiniteMeasure (volume.restrict punctUnitBall) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_punctUnitBall_lt_top⟩
  have hfin' : IsFiniteMeasure sphereMeasure := by
    rw [sphereMeasure]; infer_instance
  have hleft : sphereMeasure.IsMulLeftInvariant := ⟨fun g => by
    simpa using map_sphereMeasure_twoSidedMul hsq g 1⟩
  exact ⟨_, Measure.isMulLeftInvariant_eq_smul sphereMeasure haarProb⟩
theorem ofReal_quarter_mul_ofReal_two_pi_sq_ne_zero :
    ENNReal.ofReal (1 / 4) * ENNReal.ofReal (2 * Real.pi ^ 2) ≠ 0 := by
  have h1 : (0 : ℝ) < 1 / 4 := by norm_num
  have h2 : (0 : ℝ) < 2 * Real.pi ^ 2 := by positivity
  exact mul_ne_zero (ENNReal.ofReal_pos.mpr h1).ne' (ENNReal.ofReal_pos.mpr h2).ne'
theorem expChartMeasure_apply
    (hsq : ∀ Y : LieElement, Y.toMatrix ^ 2 = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2))
    (hmem : ∀ Y : LieElement, matExp (Complex.I • Y.toMatrix) ∈ specialUnitary)
    (hexp : ∀ Y : LieElement, matExp (Complex.I • Y.toMatrix) =
      (Real.cos ‖Y‖ : ℂ) • (1 : ComplexMatrix2) + (Complex.I * (Real.sinc ‖Y‖ : ℂ)) • Y.toMatrix)
    (A : Set specialUnitary) (hA : MeasurableSet A) :
    expChartMeasure A = ENNReal.ofReal (2 * Real.pi ^ 2) * haarProb A := by
  obtain ⟨c, hc⟩ := exists_sphereMeasure_eq_smul hsq
  have hu := sphereMeasure_apply hsq hmem hexp univ MeasurableSet.univ
  rw [expChartMeasure_univ hmem hexp, hc] at hu
  have hcv : (c : ℝ≥0∞) = ENNReal.ofReal (1 / 4) * ENNReal.ofReal (2 * Real.pi ^ 2) := by
    simpa using hu
  have h1 := sphereMeasure_apply hsq hmem hexp A hA
  rw [hc] at h1
  have h2 : (c : ℝ≥0∞) * haarProb A = ENNReal.ofReal (1 / 4) * expChartMeasure A := by simpa using h1
  rw [hcv, mul_assoc] at h2
  have h4 : ENNReal.ofReal (1 / 4) ≠ 0 := (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  exact ((ENNReal.mul_right_inj h4 ENNReal.ofReal_ne_top).mp h2).symm
theorem map_haarProb_of_map_sphereMeasure
    (hsq : ∀ Y : LieElement, Y.toMatrix ^ 2 = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2))
    (hmem : ∀ Y : LieElement, matExp (Complex.I • Y.toMatrix) ∈ specialUnitary)
    (hexp : ∀ Y : LieElement, matExp (Complex.I • Y.toMatrix) =
      (Real.cos ‖Y‖ : ℂ) • (1 : ComplexMatrix2) + (Complex.I * (Real.sinc ‖Y‖ : ℂ)) • Y.toMatrix)
    (g : specialUnitary → specialUnitary) (hg : Measurable g)
    (h : Measure.map g sphereMeasure = sphereMeasure) :
    Measure.map g haarProb = haarProb := by
  obtain ⟨c, hc⟩ := exists_sphereMeasure_eq_smul hsq
  have hu := sphereMeasure_apply hsq hmem hexp univ MeasurableSet.univ
  rw [expChartMeasure_univ hmem hexp, hc] at hu
  have hcv : (c : ℝ≥0∞) = ENNReal.ofReal (1 / 4) * ENNReal.ofReal (2 * Real.pi ^ 2) := by
    simpa using hu
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by rw [hcv]; exact ofReal_quarter_mul_ofReal_two_pi_sq_ne_zero
  ext s hs
  have h1 := congrArg (fun m : Measure specialUnitary => m s) h
  simp only [Measure.map_apply hg hs, hc] at h1
  have h2 : (c : ℝ≥0∞) * haarProb (g ⁻¹' s) = c * haarProb s := by simpa using h1
  rw [Measure.map_apply hg hs]
  exact (ENNReal.mul_right_inj hc0 ENNReal.coe_ne_top).mp h2
theorem haarExpChartProperties_of (hI : UnitaryLogConjugationProperties)
    (hN : LieAlgebraNormAdjointIsometry) :
    HaarExpChartProperties := by
  obtain ⟨-, -, hnorm, -, -, hAdn, hAdim, -⟩ := hN
  have hsq : ∀ Y : LieElement, Y.toMatrix ^ 2 = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2) := fun Y => by
    rw [hnorm]; exact (hI.1 _ Y.2).1
  have hmem : ∀ Y : LieElement, matExp (Complex.I • Y.toMatrix) ∈ specialUnitary :=
    fun Y => (hI.1 _ Y.2).2.2
  have hexp : ∀ Y : LieElement, matExp (Complex.I • Y.toMatrix) =
      (Real.cos ‖Y‖ : ℂ) • (1 : ComplexMatrix2) + (Complex.I * (Real.sinc ‖Y‖ : ℂ)) • Y.toMatrix :=
    fun Y => by
      rw [hnorm, ← sincAngle_eq_sinc]; exact (hI.1 _ Y.2).2.1
  have hge := measurable_expChart hmem hexp
  have hdens : ∀ Y : LieElement, haarExpDensity Y.toMatrix =
      (2 * Real.pi ^ 2)⁻¹ * Real.sinc ‖Y‖ ^ 2 := fun Y => by
    rw [haarExpDensity, ← hnorm, sincAngle_eq_sinc]
  have hball : lieBallPi = Metric.ball (0 : LieElement) Real.pi := by
    ext Y
    simp [lieBallPi, ← hnorm]
  have hdm : Measurable fun Y : LieElement => ENNReal.ofReal (haarExpDensity Y.toMatrix) := by
    simp only [hdens]
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((Real.continuous_sinc.comp continuous_norm).pow 2).measurable)
  have hp2 : (0 : ℝ) < 2 * Real.pi ^ 2 := by positivity
  have hdnn : ∀ Y : LieElement, 0 ≤ haarExpDensity Y.toMatrix := fun Y => by
    rw [hdens]; positivity
  have hhaar : haarProb = Measure.map expChart
      ((lieLebesgue.restrict lieBallPi).withDensity
        fun Y => ENNReal.ofReal (haarExpDensity Y.toMatrix)) := by
    ext A hA
    rw [Measure.map_apply hge hA, withDensity_apply _ (hge hA)]
    have e1 : ∀ Y : LieElement, ENNReal.ofReal (haarExpDensity Y.toMatrix) =
        ENNReal.ofReal (2 * Real.pi ^ 2)⁻¹ * ENNReal.ofReal (Real.sinc ‖Y‖ ^ 2) := fun Y => by
      rw [hdens, ENNReal.ofReal_mul (by positivity)]
    simp only [e1]
    rw [lintegral_const_mul _ measurable_ofReal_sinc_sq, hball]
    have e2 := expChartMeasure_apply hsq hmem hexp A hA
    rw [expChartMeasure, Measure.map_apply hge hA, withDensity_apply _ (hge hA)] at e2
    rw [e2, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hp2.ne',
      ENNReal.ofReal_one, one_mul]
  refine ⟨⟨?_, ?_, hhaar, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro f hf _
    calc ∫ U, f U ∂haarProb
        = ∫ U, f U ∂(Measure.map expChart
            ((lieLebesgue.restrict lieBallPi).withDensity
              fun Y => ENNReal.ofReal (haarExpDensity Y.toMatrix))) := by rw [← hhaar]
      _ = ∫ Y, f (expChart Y) ∂((lieLebesgue.restrict lieBallPi).withDensity
              fun Y => ENNReal.ofReal (haarExpDensity Y.toMatrix)) :=
          integral_map hge.aemeasurable hf.aestronglyMeasurable
      _ = ∫ Y in lieBallPi, (ENNReal.ofReal (haarExpDensity Y.toMatrix)).toReal •
            f (expChart Y) ∂lieLebesgue :=
          integral_withDensity_eq_integral_toReal_smul hdm
            (Eventually.of_forall fun Y => ENNReal.ofReal_lt_top) _
      _ = _ := by
          refine integral_congr_ae (Eventually.of_forall fun Y => ?_)
          simp only [ENNReal.toReal_ofReal (hdnn Y), Complex.real_smul]
          rw [mul_comm]
  · have hS : MeasurableSet {U : specialUnitary | (U : ComplexMatrix2) = -1} :=
      (isClosed_eq continuous_subtype_val continuous_const).measurableSet
    rw [hhaar, Measure.map_apply hge hS]
    apply withDensity_absolutelyContinuous
    have hemp : expChart ⁻¹' {U : specialUnitary | (U : ComplexMatrix2) = -1} ∩ lieBallPi = ∅ := by
      ext Y
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      rw [coe_expChart hmem, hexp] at h1
      have ht : fullTrace Y.toMatrix = 0 := Y.2.2
      have h3 := congrArg Matrix.trace h1
      simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_neg, Matrix.trace_one,
        show Matrix.trace Y.toMatrix = 0 from ht, Fintype.card_fin,
        smul_eq_mul] at h3
      have hc : Real.cos ‖Y‖ = -1 := by
        have : ((Real.cos ‖Y‖ : ℝ) : ℂ) = ((-1 : ℝ) : ℂ) := by
          push_cast
          push_cast at h3
          linear_combination (1 / 2 : ℂ) * h3
        exact_mod_cast this
      have h4 : ‖Y‖ < Real.pi := by rw [hnorm]; exact h2
      have := Real.injOn_cos ⟨norm_nonneg Y, h4.le⟩ ⟨Real.pi_pos.le, le_refl _⟩
        (hc.trans Real.cos_pi.symm)
      linarith
    rw [Measure.restrict_apply (hge hS), hemp, measure_empty]
  · simp [haarExpDensity, sincAngle]
  · have e : (fun Y : LieElement => haarExpDensity Y.toMatrix) = fun Y =>
        (2 * Real.pi ^ 2)⁻¹ * sincSeries.sum (‖Y‖ ^ 2) ^ 2 := by
      ext Y
      rw [hdens, sinc_eq_sincSeries_sum_sq]
    rw [e]
    exact contDiff_const.mul
      (((contDiff_sincSeries_sum _).comp (contDiff_norm_sq ℝ)).pow 2)
  · intro Y hY
    rw [hball] at hY
    have hlt : ‖Y‖ < Real.pi := by simpa using hY
    rw [hdens]
    have := sinc_pos_of_nonneg_of_lt_pi (norm_nonneg Y) hlt
    positivity
  · intro Y hY T hT
    refine ⟨?_, ?_, ?_⟩
    · rw [← SetLike.mem_coe, ← hAdim T hT]
      exact ⟨Y, hY, rfl⟩
    · simp only [haarExpDensity]
      rw [hAdn T hT]
    · simp only [haarExpDensity, norm_neg]
  · intro T T'
    exact map_haarProb_of_map_sphereMeasure hsq hmem hexp _
      ((continuous_const.mul continuous_id).mul continuous_const).measurable
      (map_sphereMeasure_twoSidedMul hsq T T')
  · exact map_haarProb_of_map_sphereMeasure hsq hmem hexp _ continuous_inv.measurable
      (map_sphereMeasure_inv hsq)
end YangMills.Construction.Matrices.ComplexMatrix2.HaarExpChart
