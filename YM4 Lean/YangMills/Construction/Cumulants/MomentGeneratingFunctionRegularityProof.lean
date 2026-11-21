import YangMills.Construction.Cumulants.MomentGeneratingFunctionStatement
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Topology
namespace YangMills.Construction.Cumulants
variable {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν] {n : ℕ}
  {X : Fin n → Ω → ℝ}
private noncomputable def weightedTransform (ν : Measure Ω) (X : Fin n → Ω → ℝ) (Z : Ω → ℂ)
    (t : Fin n → ℂ) : ℂ :=
  ∫ ω, Z ω * Complex.exp (∑ i, t i * (X i ω : ℂ)) ∂ν
private theorem measurable_expLinear (hXm : ∀ i, Measurable (X i)) (t : Fin n → ℂ) :
    Measurable fun ω => Complex.exp (∑ i, t i * (X i ω : ℂ)) := by
  refine Complex.measurable_exp.comp (Finset.measurable_sum _ fun i _ => ?_)
  exact measurable_const.mul (Complex.measurable_ofReal.comp (hXm i))
omit [MeasurableSpace Ω] in
private theorem norm_expLinear_le {C : Fin n → ℝ} (hC : ∀ i ω, |X i ω| ≤ C i) {R : ℝ}
    {t : Fin n → ℂ} (ht : ‖t‖ ≤ R) (ω : Ω) :
    ‖Complex.exp (∑ i, t i * (X i ω : ℂ))‖ ≤ Real.exp (∑ i, R * C i) := by
  refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hti : ‖t i‖ ≤ R := (norm_le_pi_norm t i).trans ht
  exact mul_le_mul hti (hC i ω) (abs_nonneg _) ((norm_nonneg _).trans hti)
private theorem integrable_weightedIntegrand {C : Fin n → ℝ} (hXm : ∀ i, Measurable (X i))
    (hC : ∀ i ω, |X i ω| ≤ C i) {Z : Ω → ℂ} (hZm : Measurable Z) {D : ℝ}
    (hZ : ∀ ω, ‖Z ω‖ ≤ D) (t : Fin n → ℂ) :
    Integrable (fun ω => Z ω * Complex.exp (∑ i, t i * (X i ω : ℂ))) ν := by
  refine Integrable.of_bound (hZm.mul (measurable_expLinear hXm t)).aestronglyMeasurable
    (D * Real.exp (∑ i, ‖t‖ * C i)) (ae_of_all _ fun ω => ?_)
  rw [norm_mul]
  exact mul_le_mul (hZ ω) (norm_expLinear_le hC le_rfl ω) (norm_nonneg _)
    ((norm_nonneg _).trans (hZ ω))
private theorem hasFDerivAt_weightedTransform {C : Fin n → ℝ} (hXm : ∀ i, Measurable (X i))
    (hC : ∀ i ω, |X i ω| ≤ C i) {Z : Ω → ℂ} (hZm : Measurable Z) {D : ℝ}
    (hZ : ∀ ω, ‖Z ω‖ ≤ D) (x₀ : Fin n → ℂ) :
    HasFDerivAt (weightedTransform ν X Z)
      (∑ i, weightedTransform ν X (fun ω => Z ω * (X i ω : ℂ)) x₀ •
        (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ)) x₀ := by
  let p : Fin n → ((Fin n → ℂ) →L[ℂ] ℂ) := fun i => ContinuousLinearMap.proj i
  let F' : (Fin n → ℂ) → Ω → ((Fin n → ℂ) →L[ℂ] ℂ) := fun t ω =>
    ∑ i, (Z ω * (X i ω : ℂ) * Complex.exp (∑ j, t j * (X j ω : ℂ))) • p i
  have hZXm : ∀ i, Measurable fun ω => Z ω * (X i ω : ℂ) := fun i =>
    hZm.mul (Complex.measurable_ofReal.comp (hXm i))
  have hZXb : ∀ i ω, ‖Z ω * (X i ω : ℂ)‖ ≤ D * C i := fun i ω => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hZ ω) (hC i ω) (abs_nonneg _) ((norm_nonneg _).trans (hZ ω))
  have hI : ∀ i, Integrable
      (fun ω => Z ω * (X i ω : ℂ) * Complex.exp (∑ j, x₀ j * (X j ω : ℂ))) ν := fun i =>
    integrable_weightedIntegrand hXm hC (hZXm i) (hZXb i) x₀
  have hint : ∫ ω, F' x₀ ω ∂ν = ∑ i, weightedTransform ν X (fun ω => Z ω * (X i ω : ℂ)) x₀ • p i := by
    simp only [F']
    rw [integral_finsetSum _ fun i _ => (hI i).smul_const _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_const]
    rfl
  have hdiff : ∀ (ω : Ω) (t : Fin n → ℂ),
      HasFDerivAt (fun s : Fin n → ℂ => Z ω * Complex.exp (∑ i, s i * (X i ω : ℂ))) (F' t ω) t := by
    intro ω t
    have hlin : HasFDerivAt (fun s : Fin n → ℂ => ∑ i, s i * (X i ω : ℂ))
        (∑ i, (X i ω : ℂ) • p i) t := by
      have h := (∑ i, (X i ω : ℂ) • p i).hasFDerivAt (x := t)
      convert h using 1
      ext s
      simp [p, mul_comm]
    have h := hlin.cexp.const_mul (Z ω)
    have e : F' t ω =
        Z ω • Complex.exp (∑ i, t i * (X i ω : ℂ)) • ∑ i, (X i ω : ℂ) • p i := by
      simp only [F', Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      ring
    rw [e]
    exact h
  have hbound : ∀ ω, ∀ t ∈ Metric.ball x₀ 1, ‖F' t ω‖ ≤
      ∑ i, D * C i * Real.exp (∑ j, (‖x₀‖ + 1) * C j) * ‖p i‖ := by
    intro ω t ht
    have hnorm : ‖t‖ ≤ ‖x₀‖ + 1 := by
      have h1 : ‖t - x₀‖ < 1 := by simpa [dist_eq_norm] using ht
      have h2 : ‖t‖ ≤ ‖t - x₀‖ + ‖x₀‖ := by simpa using norm_add_le (t - x₀) x₀
      linarith
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, norm_mul]
    have hDC : 0 ≤ D * C i := (norm_nonneg _).trans (hZXb i ω)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hZXb i ω) (norm_expLinear_le hC hnorm ω) (norm_nonneg _) hDC) (norm_nonneg _)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (𝕜 := ℂ)
    (F := fun (t : Fin n → ℂ) ω => Z ω * Complex.exp (∑ i, t i * (X i ω : ℂ))) (F' := F')
    (x₀ := x₀) (s := Metric.ball x₀ 1)
    (bound := fun _ => ∑ i, D * C i * Real.exp (∑ j, (‖x₀‖ + 1) * C j) * ‖p i‖)
    (Metric.ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun t =>
      (hZm.mul (measurable_expLinear hXm t)).aestronglyMeasurable)
    (integrable_weightedIntegrand hXm hC hZm hZ x₀)
    (by
      have : F' x₀ = fun ω => ∑ i, (Z ω * (X i ω : ℂ) * Complex.exp (∑ j, x₀ j * (X j ω : ℂ))) • p i :=
        rfl
      rw [this]
      exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        (hI i).aestronglyMeasurable.smul_const _)
    (ae_of_all _ hbound) (integrable_const _) (ae_of_all _ fun ω t _ => hdiff ω t)
  rw [hint] at key
  exact key
private theorem contDiff_weightedTransform {C : Fin n → ℝ} (hXm : ∀ i, Measurable (X i))
    (hC : ∀ i ω, |X i ω| ≤ C i) (k : ℕ) :
    ∀ (Z : Ω → ℂ), Measurable Z → (∃ D, ∀ ω, ‖Z ω‖ ≤ D) →
      ContDiff ℂ k (weightedTransform ν X Z) := by
  induction k with
  | zero =>
    rintro Z hZm ⟨D, hZ⟩
    have : Continuous (weightedTransform ν X Z) := continuous_iff_continuousAt.2 fun t =>
      (hasFDerivAt_weightedTransform hXm hC hZm hZ t).continuousAt
    have h0 : ContDiff ℂ 0 (weightedTransform ν X Z) := contDiff_zero.2 this
    simpa using h0
  | succ k ih =>
    rintro Z hZm ⟨D, hZ⟩
    have hd := fun t => hasFDerivAt_weightedTransform (ν := ν) hXm hC hZm hZ t
    have hf : fderiv ℂ (weightedTransform ν X Z) = fun t =>
        ∑ i, weightedTransform ν X (fun ω => Z ω * (X i ω : ℂ)) t •
          (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ) := funext fun t => (hd t).fderiv
    push_cast
    rw [contDiff_succ_iff_fderiv]
    refine ⟨fun t => (hd t).differentiableAt, by simp, ?_⟩
    rw [hf]
    refine ContDiff.sum fun i _ => ContDiff.fun_smul ?_ contDiff_const
    refine ih _ (hZm.mul (Complex.measurable_ofReal.comp (hXm i))) ⟨D * C i, fun ω => ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hZ ω) (hC i ω) (abs_nonneg _) ((norm_nonneg _).trans (hZ ω))
omit [IsProbabilityMeasure ν] in
private theorem momentGeneratingFunction_eq_weightedTransform :
    momentGeneratingFunction ν X = weightedTransform ν X fun _ => 1 := by
  funext t
  simp [momentGeneratingFunction, weightedTransform]
omit [IsProbabilityMeasure ν] in
private theorem weightedTransform_zero (Z : Ω → ℂ) : weightedTransform ν X Z 0 = ∫ ω, Z ω ∂ν := by
  simp [weightedTransform]
private theorem contDiff_momentGeneratingFunction {C : Fin n → ℝ} (hXm : ∀ i, Measurable (X i))
    (hC : ∀ i ω, |X i ω| ≤ C i) (k : ℕ) : ContDiff ℂ k (momentGeneratingFunction ν X) := by
  rw [momentGeneratingFunction_eq_weightedTransform]
  exact contDiff_weightedTransform hXm hC k _ measurable_const ⟨1, fun _ => by simp⟩
private theorem momentGeneratingFunction_zero : momentGeneratingFunction ν X 0 = 1 := by
  rw [momentGeneratingFunction_eq_weightedTransform, weightedTransform_zero]
  simp
omit [IsProbabilityMeasure ν] in
private theorem momentGeneratingFunction_ofReal (s : Fin n → ℝ) :
    ∃ r : ℝ, 0 ≤ r ∧ momentGeneratingFunction ν X (fun i => (s i : ℂ)) = r := by
  refine ⟨∫ ω, Real.exp (∑ i, s i * X i ω) ∂ν, integral_nonneg fun _ => (Real.exp_pos _).le, ?_⟩
  rw [← integral_complex_ofReal]
  unfold momentGeneratingFunction
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp
private theorem mixedCumulant_im {C : Fin n → ℝ} (hXm : ∀ i, Measurable (X i))
    (hC : ∀ i ω, |X i ω| ≤ C i) : (mixedCumulant ν X).im = 0 := by
  have hΓ : ContDiff ℂ n (momentGeneratingFunction ν X) :=
    contDiff_momentGeneratingFunction hXm hC n
  let F : (Fin n → ℂ) → ℂ := fun t => Complex.log (momentGeneratingFunction ν X t)
  let U : Set (Fin n → ℂ) := momentGeneratingFunction ν X ⁻¹' Complex.slitPlane
  have hUo : IsOpen U := Complex.isOpen_slitPlane.preimage hΓ.continuous
  have h0 : (0 : Fin n → ℂ) ∈ U := by
    simp [U, momentGeneratingFunction_zero]
  have hFat : ∀ t ∈ U, ContDiffAt ℂ n F t := fun t ht =>
    (Complex.contDiffAt_log ht).comp t hΓ.contDiffAt
  have hFon : ContDiffOn ℝ n F U := fun t ht =>
    ((hFat t ht).restrict_scalars ℝ).contDiffWithinAt
  let Q : (Fin n → ℂ) → ℝ := Complex.imCLM ∘ F
  have hQ : ContDiffOn ℝ n Q U := Complex.imCLM.contDiff.comp_contDiffOn hFon
  let ι : (Fin n → ℝ) →L[ℝ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i => Complex.ofRealCLM ∘L ContinuousLinearMap.proj i
  have hι0 : ι 0 = 0 := map_zero ι
  have hzero : Q ∘ ι = fun _ => (0 : ℝ) := by
    funext s
    obtain ⟨r, hr, h⟩ := momentGeneratingFunction_ofReal (ν := ν) (X := X) s
    have : ι s = fun i => (s i : ℂ) := rfl
    simp only [Function.comp_apply, Q, F, this, h]
    rw [← Complex.ofReal_log hr]
    simp
  have hVo : IsOpen (ι ⁻¹' U) := hUo.preimage ι.continuous
  have hV0 : (0 : Fin n → ℝ) ∈ ι ⁻¹' U := by simpa [hι0] using h0
  have hright := ι.iteratedFDerivWithin_comp_right hQ hUo.uniqueDiffOn hVo.uniqueDiffOn
    (x := 0) (by simpa [hι0] using h0) (i := n) le_rfl
  rw [hzero, iteratedFDerivWithin_of_isOpen n hVo hV0, hι0,
    iteratedFDerivWithin_of_isOpen n hUo h0] at hright
  have hleft : iteratedFDeriv ℝ n Q 0 =
      Complex.imCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ n F 0) :=
    Complex.imCLM.iteratedFDeriv_comp_left ((hFat 0 h0).restrict_scalars ℝ) le_rfl
  have hres := (hFat 0 h0).restrictScalars_iteratedFDeriv (𝕜 := ℝ)
  have happ := congrArg
    (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℝ) ℝ =>
      A fun i => Pi.single i 1) hright
  have hιe : ∀ i, ι (Pi.single i 1) = Pi.single i 1 := by
    intro i
    funext j
    by_cases h : j = i
    · subst h
      simp [ι]
    · simp [ι, Pi.single_eq_of_ne h]
  simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, zero_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, hιe, hleft,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, ← hres] at happ
  simpa [mixedCumulant, F] using happ.symm
private theorem mixedCumulant_pair {A B : Ω → ℝ} (hA : Measurable A) (hB : Measurable B)
    (hAb : ∃ c, ∀ ω, |A ω| ≤ c) (hBb : ∃ c, ∀ ω, |B ω| ≤ c) :
    mixedCumulant ν ![A, B] = (((∫ ω, A ω * B ω ∂ν) - (∫ ω, A ω ∂ν) * ∫ ω, B ω ∂ν : ℝ) : ℂ) := by
  obtain ⟨a, ha⟩ := hAb
  obtain ⟨b, hb⟩ := hBb
  set V : Fin 2 → Ω → ℝ := ![A, B] with hV
  have hVm : ∀ i, Measurable (V i) := by
    intro i
    fin_cases i
    exacts [hA, hB]
  let C : Fin 2 → ℝ := ![a, b]
  have hC : ∀ i ω, |V i ω| ≤ C i := by
    intro i ω
    fin_cases i
    exacts [ha ω, hb ω]
  have hAb' : ∀ ω, ‖((1 : ℂ) * (A ω : ℂ))‖ ≤ 1 * a := fun ω => by simpa using ha ω
  have hBb' : ∀ ω, ‖((1 : ℂ) * (B ω : ℂ))‖ ≤ 1 * b := fun ω => by simpa using hb ω
  have hAm' : Measurable fun ω => (1 : ℂ) * (A ω : ℂ) :=
    measurable_const.mul (Complex.measurable_ofReal.comp hA)
  have hBm' : Measurable fun ω => (1 : ℂ) * (B ω : ℂ) :=
    measurable_const.mul (Complex.measurable_ofReal.comp hB)
  let G : (Fin 2 → ℂ) → ℂ := weightedTransform ν V fun _ => 1
  let WA : (Fin 2 → ℂ) → ℂ := weightedTransform ν V fun ω => 1 * (A ω : ℂ)
  let WB : (Fin 2 → ℂ) → ℂ := weightedTransform ν V fun ω => 1 * (B ω : ℂ)
  let p : Fin 2 → ((Fin 2 → ℂ) →L[ℂ] ℂ) := fun i => ContinuousLinearMap.proj i
  have hG : ∀ t, HasFDerivAt G (WA t • p 0 + WB t • p 1) t := fun t => by
    have h := hasFDerivAt_weightedTransform (ν := ν) hVm hC (Z := fun _ => 1) measurable_const
      (D := 1) (fun _ => by simp) t
    simpa [Fin.sum_univ_two, hV, WA, WB, p] using h
  have hWA : HasFDerivAt WA _ 0 :=
    hasFDerivAt_weightedTransform (ν := ν) hVm hC hAm' hAb' 0
  have hWB : HasFDerivAt WB _ 0 :=
    hasFDerivAt_weightedTransform (ν := ν) hVm hC hBm' hBb' 0
  have hG0 : G 0 = 1 := by
    simp [G, weightedTransform_zero]
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun t => (hG t).continuousAt
  have hGne : G 0 ≠ 0 := by simp [hG0]
  let H : (Fin 2 → ℂ) → ((Fin 2 → ℂ) →L[ℂ] ℂ) := fun t =>
    (G t)⁻¹ • (WA t • p 0 + WB t • p 1)
  have hFd : (fderiv ℂ fun t => Complex.log (momentGeneratingFunction ν V t)) =ᶠ[𝓝 0] H := by
    have hU : ∀ᶠ t in 𝓝 (0 : Fin 2 → ℂ), G t ∈ Complex.slitPlane :=
      hGc.continuousAt.eventually_mem
        (Complex.isOpen_slitPlane.mem_nhds (by simp [hG0]))
    filter_upwards [hU] with t ht
    have hΓ : momentGeneratingFunction ν V = G := momentGeneratingFunction_eq_weightedTransform
    rw [hΓ]
    exact ((hG t).clog ht).fderiv
  have hJ : mixedCumulant ν V = fderiv ℂ H 0 (Pi.single 0 1) (Pi.single 1 1) := by
    unfold mixedCumulant
    rw [iteratedFDeriv_two_apply, hFd.fderiv_eq]
  have hWAd : DifferentiableAt ℂ WA 0 := hWA.differentiableAt
  have hWBd : DifferentiableAt ℂ WB 0 := hWB.differentiableAt
  have hGd : DifferentiableAt ℂ G 0 := (hG 0).differentiableAt
  have hHd : DifferentiableAt ℂ H 0 :=
    (hGd.inv hGne).smul ((hWAd.smul_const _).add (hWBd.smul_const _))
  let e₀ : Fin 2 → ℂ := Pi.single 0 1
  let e₁ : Fin 2 → ℂ := Pi.single 1 1
  have hev : HasFDerivAt (fun t => H t e₁)
      ((ContinuousLinearMap.apply ℂ ℂ e₁).comp (fderiv ℂ H 0)) 0 :=
    (ContinuousLinearMap.apply ℂ ℂ e₁).hasFDerivAt.comp 0 hHd.hasFDerivAt
  have hHe : (fun t => H t e₁) = fun t => (G t)⁻¹ * WB t := by
    funext t
    simp [H, p, e₁]
  rw [hHe] at hev
  have hinv : HasFDerivAt (fun t => (G t)⁻¹) _ 0 :=
    (hasDerivAt_inv hGne).comp_hasFDerivAt (0 : Fin 2 → ℂ) (hG 0)
  have hprod := hinv.mul hWB
  have hval := congrArg (fun L : (Fin 2 → ℂ) →L[ℂ] ℂ => L e₀) (hev.unique hprod)
  have hI1 : WA 0 = ((∫ ω, A ω ∂ν : ℝ) : ℂ) := by
    simp only [WA, weightedTransform_zero, one_mul]
    exact integral_complex_ofReal
  have hI2 : WB 0 = ((∫ ω, B ω ∂ν : ℝ) : ℂ) := by
    simp only [WB, weightedTransform_zero, one_mul]
    exact integral_complex_ofReal
  have hI3 : weightedTransform ν V (fun ω => 1 * (B ω : ℂ) * (V 0 ω : ℂ)) 0 =
      ((∫ ω, A ω * B ω ∂ν : ℝ) : ℂ) := by
    rw [weightedTransform_zero, ← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp [hV, mul_comm]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    add_apply, smul_apply, sum_apply, ContinuousLinearMap.proj_apply, Fin.sum_univ_two, smul_eq_mul, hG0, e₀, p] at hval
  rw [hJ]
  simp only [e₁] at hval
  rw [hval, hI3, hI1, hI2]
  simp
  ring
theorem momentGeneratingFunctionRegularity_holds : MomentGeneratingFunctionRegularity := by
  intro Ω _ ν _
  refine ⟨fun n X hXm hXb => ?_, fun A B hA hB hAb hBb => mixedCumulant_pair hA hB hAb hBb⟩
  choose C hC using hXb
  have hΓ := contDiff_momentGeneratingFunction (ν := ν) hXm hC 1
  have hd : Differentiable ℂ (momentGeneratingFunction ν X) := hΓ.differentiable (by simp)
  refine ⟨hd, momentGeneratingFunction_zero, ?_, mixedCumulant_im hXm hC⟩
  refine ⟨momentGeneratingFunction ν X ⁻¹' Complex.slitPlane, ?_, fun t ht => ht, ?_⟩
  · exact (Complex.isOpen_slitPlane.preimage hΓ.continuous).mem_nhds
      (by simp [momentGeneratingFunction_zero])
  · exact fun t ht => ((hd t).clog ht).differentiableWithinAt
end YangMills.Construction.Cumulants
