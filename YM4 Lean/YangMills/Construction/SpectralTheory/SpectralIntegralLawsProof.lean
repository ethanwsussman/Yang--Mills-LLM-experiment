import YangMills.Construction.EuclideanSpectral.FunctionalCalculusTransport
import YangMills.Construction.SpectralTheory.SpectralMeasureConcentratedOnSupportProof
import YangMills.Construction.SpectralTheory.SpectralPushforwardLemmas
import YangMills.Construction.SpectralTheory.UnitaryGroupSemigroupCorrespondence
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.SpectralTheory.IntegralLawsProof
open YangMills.Construction.SpectralTheory YangMills.Construction.SpectralTheory.ProjectionMeasure
variable {n : ℕ} [NeZero n] {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
  [CompleteSpace ℋ]
structure Ingredients (E : ProjectionMeasure n ℋ) : Prop where
  diag : E.SpectralValueMeasureRules
  simple : E.SimpleIntegralRules
  limits : ∀ f : (Fin n → ℝ) → ℂ, Measurable f → E.ApproximantLimitsExist f
theorem diagonalMeasure_of_measurableSet (E : ProjectionMeasure n ℋ) (ψ : ℋ)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    E.spectralValueMeasure ψ A = ENNReal.ofReal (‖E ⟨A, hA⟩ ψ‖ ^ 2) :=
  E.spectralValueMeasure_apply ψ ⟨A, hA⟩
theorem diagonalMeasure_univ (E : ProjectionMeasure n ℋ) (ψ : ℋ) :
    E.spectralValueMeasure ψ univ = ENNReal.ofReal (‖ψ‖ ^ 2) := by apply _root_.YangMills.Construction.SpectralSupport.diagonalMeasure_univ_eq <;> assumption
instance diagonalMeasure_isFinite (E : ProjectionMeasure n ℋ) (ψ : ℋ) :
    IsFiniteMeasure (E.spectralValueMeasure ψ) :=
  ⟨by rw [diagonalMeasure_univ]; exact ENNReal.ofReal_lt_top⟩
theorem mem_functionalDomain_iff_integrable (E : ProjectionMeasure n ℋ) {f : (Fin n → ℝ) → ℂ}
    (hf : Measurable f) {ψ : ℋ} :
    ψ ∈ functionalDomain E f ↔ Integrable (fun x => ‖f x‖ ^ 2) (E.spectralValueMeasure ψ) := by
  have e : ∀ x, ‖‖f x‖ ^ 2‖ₑ = ‖f x‖ₑ ^ 2 := fun x => by rw [enorm_pow, enorm_norm]
  constructor
  · intro h
    refine ⟨(hf.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp only [e]
    exact h
  · intro h
    have h' := h.2
    rw [hasFiniteIntegral_iff_enorm] at h'
    simp only [e] at h'
    exact h'
theorem mem_functionalDomain_iff_memLp (E : ProjectionMeasure n ℋ) {f : (Fin n → ℝ) → ℂ}
    (hf : Measurable f) {ψ : ℋ} :
    ψ ∈ functionalDomain E f ↔ MemLp f 2 (E.spectralValueMeasure ψ) := by
  rw [mem_functionalDomain_iff_integrable E hf,
    memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable]
theorem integrable_of_mem_functionalDomain (E : ProjectionMeasure n ℋ) {f : (Fin n → ℝ) → ℂ}
    (hf : Measurable f) {ψ : ℋ} (hψ : ψ ∈ functionalDomain E f) :
    Integrable f (E.spectralValueMeasure ψ) :=
  ((mem_functionalDomain_iff_memLp E hf).1 hψ).integrable one_le_two
theorem mem_functionalDomain_of_enorm_le (E : ProjectionMeasure n ℋ) {f g : (Fin n → ℝ) → ℂ}
    {ψ : ℋ} (hf : Measurable f) (hψ : ψ ∈ functionalDomain E f) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (h : ∀ x, ‖g x‖ₑ ≤ c * ‖f x‖ₑ) : ψ ∈ functionalDomain E g := by
  have h₁ : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) ≤
      c ^ 2 * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) := by
    rw [← lintegral_const_mul _ (hf.enorm.pow_const 2)]
    refine lintegral_mono fun x => ?_
    rw [← mul_pow]
    exact pow_le_pow_left' (h x) 2
  exact h₁.trans_lt (ENNReal.mul_lt_top (ENNReal.pow_lt_top hc.lt_top) hψ)
theorem exists_enorm_bound_of_isBounded {g : (Fin n → ℝ) → ℂ} (hg : IsBoundedComplexFn g) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ x, ‖g x‖ₑ ≤ c := by
  obtain ⟨C, hC⟩ := hg
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun x => ?_⟩
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hC x)
theorem isBoundedComplexFn_of_isSimpleBorel {h : (Fin n → ℝ) → ℂ} (hh : IsSimpleBorel h) :
    IsBoundedComplexFn h := by
  obtain ⟨C, hC⟩ := hh.2.isBounded.exists_norm_le
  exact ⟨C, fun x => hC _ ⟨x, rfl⟩⟩
theorem mem_functionalDomain_of_isBounded (E : ProjectionMeasure n ℋ) {g : (Fin n → ℝ) → ℂ}
    (hg : IsBoundedComplexFn g) (ψ : ℋ) : ψ ∈ functionalDomain E g := by
  obtain ⟨c, hc, h⟩ := exists_enorm_bound_of_isBounded hg
  have h₁ : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) ≤
      c ^ 2 * E.spectralValueMeasure ψ univ := by
    rw [← lintegral_const]
    exact lintegral_mono fun x => pow_le_pow_left' (h x) 2
  exact h₁.trans_lt (ENNReal.mul_lt_top (ENNReal.pow_lt_top hc.lt_top) (measure_lt_top _ _))
theorem tendsto_lintegral_enorm_sub_sq {μ : Measure (Fin n → ℝ)} {u : ℕ → (Fin n → ℝ) → ℂ}
    {f : (Fin n → ℝ) → ℂ} {b : (Fin n → ℝ) → ℝ≥0∞} (hu : ∀ r, Measurable (u r))
    (hf : Measurable f) (hfin : ∫⁻ x, b x ^ 2 ∂μ < ∞) (hdom : ∀ r x, ‖u r x - f x‖ₑ ≤ b x)
    (hlim : ∀ x, Tendsto (fun r => u r x) atTop (𝓝 (f x))) :
    Tendsto (fun r => ∫⁻ x, ‖u r x - f x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
  have h0 : ∫⁻ _, (0 : ℝ≥0∞) ∂μ = 0 := by simp
  rw [← h0]
  refine tendsto_lintegral_of_dominated_convergence (fun x => b x ^ 2)
    (fun r => ((hu r).sub hf).enorm.pow_const 2)
    (fun r => ae_of_all _ fun x => pow_le_pow_left' (hdom r x) 2) hfin.ne
    (ae_of_all _ fun x => ?_)
  have h₁ : Tendsto (fun r => u r x - f x) atTop (𝓝 0) := by
    simpa using (hlim x).sub_const (f x)
  have h₂ : Tendsto (fun r => ‖u r x - f x‖ₑ) atTop (𝓝 0) := by
    simpa using h₁.enorm
  simpa using ENNReal.Tendsto.pow (n := 2) h₂
theorem lintegral_const_mul_enorm_sq_lt_top {μ : Measure (Fin n → ℝ)} {f : (Fin n → ℝ) → ℂ}
    (hf : Measurable f) {c : ℝ≥0∞} (hc : c ≠ ∞) (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ < ∞) :
    ∫⁻ x, (c * ‖f x‖ₑ) ^ 2 ∂μ < ∞ := by
  simp_rw [mul_pow]
  rw [lintegral_const_mul _ (hf.enorm.pow_const 2)]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top hc.lt_top) h
theorem ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 4 * a ^ 2 + 4 * b ^ 2 := by apply _root_.YangMills.Construction.EuclideanSpectral.FunctionalCalculus.ennreal_add_sq_le <;> assumption
theorem lintegral_sum_sq_lt_top {μ : Measure (Fin n → ℝ)} {a b : (Fin n → ℝ) → ℝ≥0∞}
    (ha : Measurable a) (h₁ : ∫⁻ x, a x ^ 2 ∂μ < ∞) (h₂ : ∫⁻ x, b x ^ 2 ∂μ < ∞) :
    ∫⁻ x, (a x + b x) ^ 2 ∂μ < ∞ := by
  have h : ∫⁻ x, (a x + b x) ^ 2 ∂μ ≤ ∫⁻ x, (4 * a x ^ 2 + 4 * b x ^ 2) ∂μ :=
    lintegral_mono fun x => ennreal_add_sq_le _ _
  rw [lintegral_add_left ((ha.pow_const 2).const_mul 4),
    lintegral_const_mul _ (ha.pow_const 2), lintegral_const_mul' _ _ (by simp)] at h
  exact h.trans_lt (ENNReal.add_lt_top.2
    ⟨ENNReal.mul_lt_top (by simp) h₁, ENNReal.mul_lt_top (by simp) h₂⟩)
def simpleApprox (f : (Fin n → ℝ) → ℂ) (hf : Measurable f) (r : ℕ) : (Fin n → ℝ) → ℂ :=
  SimpleFunc.approxOn f hf univ 0 (mem_univ _) r
theorem isSimpleBorel_simpleApprox (f : (Fin n → ℝ) → ℂ) (hf : Measurable f) (r : ℕ) :
    IsSimpleBorel (simpleApprox f hf r) :=
  ⟨(SimpleFunc.approxOn f hf univ 0 (mem_univ _) r).measurable,
    (SimpleFunc.approxOn f hf univ 0 (mem_univ _) r).finite_range⟩
theorem tendsto_simpleApprox (f : (Fin n → ℝ) → ℂ) (hf : Measurable f) (x : Fin n → ℝ) :
    Tendsto (fun r => simpleApprox f hf r x) atTop (𝓝 (f x)) :=
  SimpleFunc.tendsto_approxOn hf (mem_univ _) (subset_closure (mem_univ _))
theorem enorm_simpleApprox_le (f : (Fin n → ℝ) → ℂ) (hf : Measurable f) (r : ℕ)
    (x : Fin n → ℝ) : ‖simpleApprox f hf r x‖ₑ ≤ 2 * ‖f x‖ₑ := by
  calc ‖simpleApprox f hf r x‖ₑ = ENNReal.ofReal ‖simpleApprox f hf r x‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (‖f x‖ + ‖f x‖) :=
        ENNReal.ofReal_le_ofReal (SimpleFunc.norm_approxOn_zero_le hf (mem_univ _) x r)
    _ = 2 * ‖f x‖ₑ := by
        rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm, two_mul]
theorem enorm_simpleApprox_sub_le (f : (Fin n → ℝ) → ℂ) (hf : Measurable f) (r : ℕ)
    (x : Fin n → ℝ) : ‖simpleApprox f hf r x - f x‖ₑ ≤ 3 * ‖f x‖ₑ := by
  calc ‖simpleApprox f hf r x - f x‖ₑ ≤ ‖simpleApprox f hf r x‖ₑ + ‖f x‖ₑ := enorm_sub_le
    _ ≤ 2 * ‖f x‖ₑ + ‖f x‖ₑ := by gcongr; exact enorm_simpleApprox_le f hf r x
    _ = 3 * ‖f x‖ₑ := by ring
section Vectors
variable {E : ProjectionMeasure n ℋ} {f g : (Fin n → ℝ) → ℂ} {ψ : ℋ}
theorem spectralIntegral_spec (G : Ingredients E) (hf : Measurable f) :
    E.IsApproximantLimitOperator f (E.functionalCalculus f) :=
  E.functionalCalculus_isApproximantLimitOperator (G.limits f hf).isLinear
theorem mem_spectralIntegral_domain (G : Ingredients E) (hf : Measurable f) :
    ψ ∈ (E.functionalCalculus f).domain ↔ ψ ∈ functionalDomain E f := by
  rw [← (spectralIntegral_spec G hf).1]
  rfl
theorem spectralIntegral_apply_eq (G : Ingredients E) (hf : Measurable f)
    (ψ : (E.functionalCalculus f).domain) :
    E.functionalCalculus f ψ = E.approximantLimit f ψ :=
  (spectralIntegral_spec G hf).2 ψ
theorem tendsto_limitVector (G : Ingredients E) (hf : Measurable f)
    (hψ : ψ ∈ functionalDomain E f)
    {u : ℕ → (Fin n → ℝ) → ℂ} (hu : ∀ r, IsSimpleBorel (u r)) {b : (Fin n → ℝ) → ℝ≥0∞}
    (hfin : ∫⁻ x, b x ^ 2 ∂(E.spectralValueMeasure ψ) < ∞) (hdom : ∀ r x, ‖u r x - f x‖ₑ ≤ b x)
    (hlim : ∀ x, Tendsto (fun r => u r x) atTop (𝓝 (f x))) :
    Tendsto (fun r => simpleIntegral E (u r) (hu r) ψ) atTop (𝓝 (E.approximantLimit f ψ)) :=
  (G.limits f hf).isApproximantLimit ψ hψ u hu
    (tendsto_lintegral_enorm_sub_sq (fun r => (hu r).1) hf hfin hdom hlim)
theorem tendsto_simpleApprox_limitVector (G : Ingredients E) (hf : Measurable f)
    (hψ : ψ ∈ functionalDomain E f) :
    Tendsto (fun r => simpleIntegral E (simpleApprox f hf r) (isSimpleBorel_simpleApprox f hf r) ψ)
      atTop (𝓝 (E.approximantLimit f ψ)) :=
  tendsto_limitVector G hf hψ (isSimpleBorel_simpleApprox f hf)
    (lintegral_const_mul_enorm_sq_lt_top hf (by simp) hψ) (enorm_simpleApprox_sub_le f hf)
    (tendsto_simpleApprox f hf)
theorem norm_sq_limitVector (G : Ingredients E) (hf : Measurable f)
    (hψ : ψ ∈ functionalDomain E f) :
    ‖E.approximantLimit f ψ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(E.spectralValueMeasure ψ) := by
  have h₁ := ((tendsto_simpleApprox_limitVector G hf hψ).norm).pow 2
  have hint := (mem_functionalDomain_iff_integrable E hf).1 hψ
  have h₂ : Tendsto (fun r => ∫ x, ‖simpleApprox f hf r x‖ ^ 2 ∂(E.spectralValueMeasure ψ))
      atTop (𝓝 (∫ x, ‖f x‖ ^ 2 ∂(E.spectralValueMeasure ψ))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => 4 * ‖f x‖ ^ 2)
      (fun r => (((isSimpleBorel_simpleApprox f hf r).1.norm).pow_const 2).aestronglyMeasurable)
      (hint.const_mul 4) (fun r => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => ((tendsto_simpleApprox f hf x).norm).pow 2)
    have hb : ‖simpleApprox f hf r x‖ ≤ ‖f x‖ + ‖f x‖ :=
      SimpleFunc.norm_approxOn_zero_le hf (mem_univ _) x r
    have hn : 0 ≤ ‖simpleApprox f hf r x‖ := norm_nonneg _
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith
  refine tendsto_nhds_unique h₁ (h₂.congr fun r => ?_)
  exact (G.simple.norm_sq (isSimpleBorel_simpleApprox f hf r) ψ).symm
theorem enorm_sq_limitVector (G : Ingredients E) (hf : Measurable f)
    (hψ : ψ ∈ functionalDomain E f) :
    ‖E.approximantLimit f ψ‖ₑ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) := by
  have hint := (mem_functionalDomain_iff_integrable E hf).1 hψ
  have h₁ := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => by positivity)
  rw [← norm_sq_limitVector G hf hψ] at h₁
  have e : ∀ v : ℂ, ENNReal.ofReal (‖v‖ ^ 2) = ‖v‖ₑ ^ 2 := fun v => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp only [e] at h₁
  rw [← h₁, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
theorem pairIntegral_self (G : Ingredients E) (ψ : ℋ) (h : (Fin n → ℝ) → ℂ) :
    E.polarizedIntegral ψ ψ h = ∫ x, h x ∂(E.spectralValueMeasure ψ) := by
  have key : ∀ z : ℂ, ∫ x, h x ∂(E.spectralValueMeasure (ψ + z • ψ)) =
      ((Complex.normSq (1 + z) : ℝ) : ℂ) * ∫ x, h x ∂(E.spectralValueMeasure ψ) := fun z => by
    have e : ψ + z • ψ = (1 + z) • ψ := by rw [add_smul, one_smul]
    rw [e, G.diag.smul, integral_smul_measure]
    have e₂ : (‖1 + z‖ₑ ^ 2).toReal = Complex.normSq (1 + z) := by
      rw [ENNReal.toReal_pow, toReal_enorm, Complex.normSq_eq_norm_sq]
    rw [e₂, Complex.real_smul]
  unfold polarizedIntegral
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, key, zero_add]
  have h2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have h3 : Complex.I ^ 3 = -Complex.I := Complex.I_pow_three
  simp only [pow_zero, pow_one, h2, h3]
  have n0 : Complex.normSq (1 + 1) = 4 := by norm_num [Complex.normSq_apply]
  have n1 : Complex.normSq (1 + Complex.I) = 2 := by norm_num [Complex.normSq_apply]
  have n2 : Complex.normSq (1 + -1) = 0 := by norm_num [Complex.normSq_apply]
  have n3 : Complex.normSq (1 + -Complex.I) = 2 := by norm_num [Complex.normSq_apply]
  rw [n0, n1, n2, n3]
  push_cast
  ring
theorem inner_limitVector (G : Ingredients E) (hf : Measurable f)
    (hψ : ψ ∈ functionalDomain E f) :
    ⟪ψ, E.approximantLimit f ψ⟫_ℂ = ∫ x, f x ∂(E.spectralValueMeasure ψ) := by
  have h₁ : Tendsto (fun r =>
      ⟪ψ, simpleIntegral E (simpleApprox f hf r) (isSimpleBorel_simpleApprox f hf r) ψ⟫_ℂ)
      atTop (𝓝 ⟪ψ, E.approximantLimit f ψ⟫_ℂ) :=
    tendsto_const_nhds.inner (tendsto_simpleApprox_limitVector G hf hψ)
  have hint : Integrable (fun x => 2 * ‖f x‖) (E.spectralValueMeasure ψ) :=
    (integrable_of_mem_functionalDomain E hf hψ).norm.const_mul 2
  have h₂ : Tendsto (fun r => ∫ x, simpleApprox f hf r x ∂(E.spectralValueMeasure ψ)) atTop
      (𝓝 (∫ x, f x ∂(E.spectralValueMeasure ψ))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => 2 * ‖f x‖)
      (fun r => (isSimpleBorel_simpleApprox f hf r).1.aestronglyMeasurable) hint
      (fun r => ae_of_all _ fun x => ?_) (ae_of_all _ (tendsto_simpleApprox f hf))
    have hb : ‖simpleApprox f hf r x‖ ≤ ‖f x‖ + ‖f x‖ :=
      SimpleFunc.norm_approxOn_zero_le hf (mem_univ _) x r
    linarith
  refine tendsto_nhds_unique h₁ (h₂.congr fun r => ?_)
  rw [G.simple.inner (isSimpleBorel_simpleApprox f hf r), pairIntegral_self G]
theorem mem_functionalDomain_add (hf : Measurable f) (hg : Measurable g) (z : ℂ)
    (hψf : ψ ∈ functionalDomain E f) (hψg : ψ ∈ functionalDomain E g) :
    ψ ∈ functionalDomain E (fun x => f x + z * g x) := by
  have hm : Measurable fun x => f x + z * g x := hf.add (hg.const_mul z)
  rw [mem_functionalDomain_iff_memLp E hm]
  exact ((mem_functionalDomain_iff_memLp E hf).1 hψf).add
    (((mem_functionalDomain_iff_memLp E hg).1 hψg).const_mul z)
theorem limitVector_add (G : Ingredients E) (hf : Measurable f) (hg : Measurable g) (z : ℂ)
    (hψf : ψ ∈ functionalDomain E f) (hψg : ψ ∈ functionalDomain E g) :
    E.approximantLimit (fun x => f x + z * g x) ψ =
      E.approximantLimit f ψ + z • E.approximantLimit g ψ := by
  have hs : ∀ r, IsSimpleBorel fun x => simpleApprox f hf r x + z * simpleApprox g hg r x :=
    fun r => (isSimpleBorel_simpleApprox f hf r).add_const_mul (isSimpleBorel_simpleApprox g hg r) z
  have hm : Measurable fun x => f x + z * g x := hf.add (hg.const_mul z)
  have hb : ∫⁻ x, (3 * ‖f x‖ₑ + ‖z‖ₑ * 3 * ‖g x‖ₑ) ^ 2 ∂(E.spectralValueMeasure ψ) < ∞ :=
    lintegral_sum_sq_lt_top (hf.enorm.const_mul 3)
      (lintegral_const_mul_enorm_sq_lt_top hf (by simp) hψf)
      (lintegral_const_mul_enorm_sq_lt_top hg (ENNReal.mul_ne_top enorm_ne_top (by simp)) hψg)
  have h₁ := tendsto_limitVector G hm (mem_functionalDomain_add hf hg z hψf hψg) hs hb
    (fun r x => by
      have e : simpleApprox f hf r x + z * simpleApprox g hg r x - (f x + z * g x) =
          (simpleApprox f hf r x - f x) + z * (simpleApprox g hg r x - g x) := by ring
      rw [e, mul_assoc]
      refine (enorm_add_le _ _).trans ?_
      rw [enorm_mul]
      gcongr
      · exact enorm_simpleApprox_sub_le f hf r x
      · exact enorm_simpleApprox_sub_le g hg r x)
    (fun x => (tendsto_simpleApprox f hf x).add ((tendsto_simpleApprox g hg x).const_mul z))
  have h₂ : Tendsto (fun r => simpleIntegral E _ (hs r) ψ) atTop
      (𝓝 (E.approximantLimit f ψ + z • E.approximantLimit g ψ)) := by
    have h₃ := (tendsto_simpleApprox_limitVector G hf hψf).add
      ((tendsto_simpleApprox_limitVector G hg hψg).const_smul z)
    refine h₃.congr fun r => ?_
    rw [G.simple.add_const_mul (isSimpleBorel_simpleApprox f hf r)
      (isSimpleBorel_simpleApprox g hg r) z]
    rfl
  exact tendsto_nhds_unique h₁ h₂
end Vectors
section Products
variable {E : ProjectionMeasure n ℋ} {f g : (Fin n → ℝ) → ℂ} {ψ : ℋ}
theorem tendsto_limitVector_of_lintegral (G : Ingredients E) {u : ℕ → (Fin n → ℝ) → ℂ}
    {w : (Fin n → ℝ) → ℂ} (hu : ∀ r, Measurable (u r)) (hw : Measurable w)
    (hψu : ∀ r, ψ ∈ functionalDomain E (u r)) (hψw : ψ ∈ functionalDomain E w)
    (hlim : Tendsto (fun r => ∫⁻ x, ‖u r x - w x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ)) atTop (𝓝 0)) :
    Tendsto (fun r => E.approximantLimit (u r) ψ) atTop (𝓝 (E.approximantLimit w ψ)) := by
  have key : ∀ r, ‖E.approximantLimit (u r) ψ - E.approximantLimit w ψ‖ₑ ^ 2 =
      ∫⁻ x, ‖u r x - w x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) := fun r => by
    have hm : Measurable fun x => u r x + (-1 : ℂ) * w x := (hu r).add (hw.const_mul _)
    have h₁ := limitVector_add G (hu r) hw (-1) (hψu r) hψw
    have h₂ := enorm_sq_limitVector G hm (mem_functionalDomain_add (hu r) hw (-1) (hψu r) hψw)
    rw [h₁] at h₂
    simpa [sub_eq_add_neg] using h₂
  rw [tendsto_iff_edist_tendsto_0]
  simp only [edist_eq_enorm_sub]
  have h₃ := ((ENNReal.continuous_rpow_const (y := ((2 : ℕ) : ℝ)⁻¹)).tendsto 0).comp hlim
  have e0 : (0 : ℝ≥0∞) ^ (((2 : ℕ) : ℝ)⁻¹) = 0 := by simp
  rw [e0] at h₃
  refine h₃.congr fun r => ?_
  simp only [Function.comp_apply, ← key]
  exact ENNReal.pow_rpow_inv_natCast (by norm_num) _
theorem simpleIntegral_limitVector (G : Ingredients E) {h : (Fin n → ℝ) → ℂ}
    (hh : IsSimpleBorel h) (hg : Measurable g) (hψ : ψ ∈ functionalDomain E g) :
    ψ ∈ functionalDomain E (fun x => h x * g x) ∧
      simpleIntegral E h hh (E.approximantLimit g ψ) =
        E.approximantLimit (fun x => h x * g x) ψ := by
  obtain ⟨c, hc, hb⟩ := exists_enorm_bound_of_isBounded (isBoundedComplexFn_of_isSimpleBorel hh)
  have hm : Measurable fun x => h x * g x := hh.1.mul hg
  have hd : ψ ∈ functionalDomain E (fun x => h x * g x) :=
    mem_functionalDomain_of_enorm_le E hg hψ hc fun x => by
      rw [enorm_mul]
      gcongr
      exact hb x
  refine ⟨hd, ?_⟩
  have hs : ∀ r, IsSimpleBorel fun x => h x * simpleApprox g hg r x := fun r =>
    hh.mul (isSimpleBorel_simpleApprox g hg r)
  have h₁ := tendsto_limitVector G hm hd hs (b := fun x => (c * 3) * ‖g x‖ₑ)
    (lintegral_const_mul_enorm_sq_lt_top hg (ENNReal.mul_ne_top hc (by simp)) hψ)
    (fun r x => by
      rw [← mul_sub, enorm_mul, mul_assoc]
      gcongr
      · exact hb x
      · exact enorm_simpleApprox_sub_le g hg r x)
    (fun x => (tendsto_simpleApprox g hg x).const_mul (h x))
  have h₂ : Tendsto (fun r => simpleIntegral E _ (hs r) ψ) atTop
      (𝓝 (simpleIntegral E h hh (E.approximantLimit g ψ))) := by
    have h₃ := ((simpleIntegral E h hh).continuous.tendsto _).comp
      (tendsto_simpleApprox_limitVector G hg hψ)
    refine h₃.congr fun r => ?_
    rw [G.simple.mul hh (isSimpleBorel_simpleApprox g hg r)]
    rfl
  exact tendsto_nhds_unique h₂ h₁
theorem diagonalMeasure_limitVector (G : Ingredients E) (hg : Measurable g)
    (hψ : ψ ∈ functionalDomain E g) :
    E.spectralValueMeasure (E.approximantLimit g ψ) =
      (E.spectralValueMeasure ψ).withDensity fun x => ‖g x‖ₑ ^ 2 := by
  refine Measure.ext fun A hA => ?_
  rw [withDensity_apply _ hA, diagonalMeasure_of_measurableSet E _ hA]
  have hi := IsSimpleBorel.indicator_one (⟨A, hA⟩ : BorelSets n)
  have h₁ := simpleIntegral_limitVector G hi hg hψ
  rw [G.simple.indicator ⟨A, hA⟩] at h₁
  have hm : Measurable fun x =>
      (⟨A, hA⟩ : BorelSets n).1.indicator (fun _ => (1 : ℂ)) x * g x :=
    hi.1.mul hg
  rw [h₁.2, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_sq_limitVector G hm h₁.1,
    ← lintegral_indicator hA]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ A <;> simp [hx]
theorem limitVector_mem_functionalDomain (G : Ingredients E) (hf : Measurable f)
    (hg : Measurable g) (hgb : IsBoundedComplexFn g) (hψ : ψ ∈ functionalDomain E f) :
    E.approximantLimit g ψ ∈ functionalDomain E f := by
  obtain ⟨c, hc, hb⟩ := exists_enorm_bound_of_isBounded hgb
  change ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(E.spectralValueMeasure (E.approximantLimit g ψ)) < ∞
  rw [diagonalMeasure_limitVector G hg (mem_functionalDomain_of_isBounded E hgb ψ),
    lintegral_withDensity_eq_lintegral_mul _ (hg.enorm.pow_const 2) (hf.enorm.pow_const 2)]
  have h₁ : ∫⁻ x, ((fun x => ‖g x‖ₑ ^ 2) * fun x => ‖f x‖ₑ ^ 2) x ∂(E.spectralValueMeasure ψ) ≤
      ∫⁻ x, (c * ‖f x‖ₑ) ^ 2 ∂(E.spectralValueMeasure ψ) := by
    refine lintegral_mono fun x => ?_
    simp only [Pi.mul_apply]
    rw [mul_pow]
    gcongr
    exact hb x
  exact h₁.trans_lt (lintegral_const_mul_enorm_sq_lt_top hf hc hψ)
theorem norm_limitVector_le (G : Ingredients E) (hf : Measurable f) {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ∀ x, ‖f x‖ ≤ C) (hψ : ψ ∈ functionalDomain E f) :
    ‖E.approximantLimit f ψ‖ ≤ C * ‖ψ‖ := by
  have h₁ : ∫ x, ‖f x‖ ^ 2 ∂(E.spectralValueMeasure ψ) ≤
      ∫ _, C ^ 2 ∂(E.spectralValueMeasure ψ) :=
    integral_mono ((mem_functionalDomain_iff_integrable E hf).1 hψ) (integrable_const _)
      fun x => pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
  have h₂ : ∫ _, C ^ 2 ∂(E.spectralValueMeasure ψ) = (C * ‖ψ‖) ^ 2 := by
    rw [integral_const, measureReal_def, diagonalMeasure_univ,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    ring
  rw [← norm_sq_limitVector G hf hψ, h₂] at h₁
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 h₁
theorem apply_of_eq_toUnboundedOperator {A : UnboundedOperator ℋ} {B : ℋ →L[ℂ] ℋ}
    (h : A = toUnboundedOperator B) (ψ : A.domain) : A ψ = B ψ := by apply _root_.YangMills.Construction.GeneratorsAndFlows.apply_of_eq_toUnboundedOperator <;> assumption
theorem exists_hasBoundedIntegral (G : Ingredients E) (hf : Measurable f)
    (hb : IsBoundedComplexFn f) : ∃ B, E.IsBoundedCalculusOf f B := by
  have hdom : ∀ ψ, ψ ∈ (E.functionalCalculus f).domain := fun ψ =>
    (mem_spectralIntegral_domain G hf).2 (mem_functionalDomain_of_isBounded E hb ψ)
  let L : ℋ →ₗ[ℂ] ℋ :=
    (E.functionalCalculus f).toFun ∘ₗ
      LinearMap.codRestrict (E.functionalCalculus f).domain LinearMap.id hdom
  have hL : ∀ ψ, L ψ = E.approximantLimit f ψ := fun ψ =>
    spectralIntegral_apply_eq G hf ⟨ψ, hdom ψ⟩
  obtain ⟨C, hC⟩ := hb
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨L.mkContinuous C fun ψ => ?_, ?_⟩
  · rw [hL]
    exact norm_limitVector_le G hf hC₀ hC (mem_functionalDomain_of_isBounded E ⟨C, hC⟩ ψ)
  · refine LinearPMap.ext ?_ ?_
    · exact top_unique fun ψ _ => hdom ψ
    · intro ψ h₁ h₂
      exact (spectralIntegral_apply_eq G hf ⟨ψ, h₁⟩).trans (hL ψ).symm
theorem boundedIntegralOp_spec (G : Ingredients E) (hf : Measurable f)
    (hb : IsBoundedComplexFn f) : E.IsBoundedCalculusOf f (E.boundedCalculus f) :=
  Classical.epsilon_spec (exists_hasBoundedIntegral G hf hb)
theorem boundedIntegralOp_apply_eq (G : Ingredients E) (hf : Measurable f)
    (hb : IsBoundedComplexFn f) (ψ : ℋ) : E.boundedCalculus f ψ = E.approximantLimit f ψ := by
  have hd : ψ ∈ (E.functionalCalculus f).domain :=
    (mem_spectralIntegral_domain G hf).2 (mem_functionalDomain_of_isBounded E hb ψ)
  exact (apply_of_eq_toUnboundedOperator (boundedIntegralOp_spec G hf hb) ⟨ψ, hd⟩).symm.trans
    (spectralIntegral_apply_eq G hf ⟨ψ, hd⟩)
theorem limitVector_simpleIntegral (G : Ingredients E) {h : (Fin n → ℝ) → ℂ}
    (hh : IsSimpleBorel h) (hg : Measurable g) (hgb : IsBoundedComplexFn g) (ψ : ℋ) :
    E.approximantLimit g (simpleIntegral E h hh ψ) =
      E.approximantLimit (fun x => h x * g x) ψ := by
  obtain ⟨c, hc, hb⟩ := exists_enorm_bound_of_isBounded (isBoundedComplexFn_of_isSimpleBorel hh)
  have hψ := mem_functionalDomain_of_isBounded E hgb ψ
  have hd := (simpleIntegral_limitVector G hh hg hψ).1
  have hm : Measurable fun x => h x * g x := hh.1.mul hg
  have hs : ∀ r, IsSimpleBorel fun x => simpleApprox g hg r x * h x := fun r =>
    (isSimpleBorel_simpleApprox g hg r).mul hh
  have h₁ := tendsto_limitVector G hm hd hs (b := fun x => (3 * c) * ‖g x‖ₑ)
    (lintegral_const_mul_enorm_sq_lt_top hg (ENNReal.mul_ne_top (by simp) hc) hψ)
    (fun r x => by
      have e : simpleApprox g hg r x * h x - h x * g x =
          h x * (simpleApprox g hg r x - g x) := by ring
      rw [e, enorm_mul, mul_comm 3 c, mul_assoc]
      gcongr
      · exact hb x
      · exact enorm_simpleApprox_sub_le g hg r x)
    (fun x => by
      simpa [mul_comm] using (tendsto_simpleApprox g hg x).mul_const (h x))
  have h₂ := tendsto_simpleApprox_limitVector G hg
    (mem_functionalDomain_of_isBounded E hgb (simpleIntegral E h hh ψ))
  refine tendsto_nhds_unique (h₂.congr fun r => ?_) h₁
  rw [G.simple.mul (isSimpleBorel_simpleApprox g hg r) hh]
  rfl
theorem limitVector_comp (G : Ingredients E) (hf : Measurable f) (hg : Measurable g)
    (hgb : IsBoundedComplexFn g) (hψ : ψ ∈ functionalDomain E f) :
    ψ ∈ functionalDomain E (fun x => f x * g x) ∧
      E.approximantLimit f (E.approximantLimit g ψ) =
        E.approximantLimit (fun x => f x * g x) ψ ∧
      E.approximantLimit (fun x => f x * g x) ψ =
        E.approximantLimit g (E.approximantLimit f ψ) := by
  obtain ⟨c, hc, hb⟩ := exists_enorm_bound_of_isBounded hgb
  have hψg := mem_functionalDomain_of_isBounded E hgb ψ
  have hχ := limitVector_mem_functionalDomain G hf hg hgb hψ
  have hm : Measurable fun x => f x * g x := hf.mul hg
  have hd : ψ ∈ functionalDomain E (fun x => f x * g x) :=
    mem_functionalDomain_of_enorm_le E hf hψ hc fun x => by
      rw [enorm_mul, mul_comm]
      gcongr
      exact hb x
  have hsm : ∀ r, Measurable fun x => simpleApprox f hf r x * g x := fun r =>
    (isSimpleBorel_simpleApprox f hf r).1.mul hg
  have hsd := fun r => (simpleIntegral_limitVector G (isSimpleBorel_simpleApprox f hf r) hg hψg).1
  have hlim : Tendsto (fun r => E.approximantLimit (fun x => simpleApprox f hf r x * g x) ψ)
      atTop (𝓝 (E.approximantLimit (fun x => f x * g x) ψ)) := by
    refine tendsto_limitVector_of_lintegral G hsm hm hsd hd
      (tendsto_lintegral_enorm_sub_sq (b := fun x => (c * 3) * ‖f x‖ₑ) hsm hm
        (lintegral_const_mul_enorm_sq_lt_top hf (ENNReal.mul_ne_top hc (by simp)) hψ)
        (fun r x => ?_) fun x => (tendsto_simpleApprox f hf x).mul_const (g x))
    rw [← sub_mul, enorm_mul, mul_comm, mul_assoc]
    gcongr
    · exact hb x
    · exact enorm_simpleApprox_sub_le f hf r x
  refine ⟨hd, ?_, ?_⟩
  · refine tendsto_nhds_unique (tendsto_simpleApprox_limitVector G hf hχ) (hlim.congr fun r => ?_)
    exact (simpleIntegral_limitVector G (isSimpleBorel_simpleApprox f hf r) hg hψg).2.symm
  · have hc₁ : Continuous fun v => E.approximantLimit g v := by
      have e : (fun v => E.approximantLimit g v) = fun v => E.boundedCalculus g v :=
        funext fun v => (boundedIntegralOp_apply_eq G hg hgb v).symm
      rw [e]
      exact (E.boundedCalculus g).continuous
    refine tendsto_nhds_unique hlim ?_
    refine ((hc₁.tendsto _).comp (tendsto_simpleApprox_limitVector G hf hψ)).congr fun r => ?_
    exact limitVector_simpleIntegral G (isSimpleBorel_simpleApprox f hf r) hg hgb ψ
theorem inner_limitVector_conj (G : Ingredients E) (hf : Measurable f)
    (hb : IsBoundedComplexFn f) (φ ψ : ℋ) :
    ⟪E.approximantLimit f φ, ψ⟫_ℂ = ⟪φ, E.approximantLimit (fun x => conj (f x)) ψ⟫_ℂ := by
  have hm : Measurable fun x => conj (f x) := Complex.continuous_conj.measurable.comp hf
  have hbc : IsBoundedComplexFn fun x => conj (f x) := by
    obtain ⟨C, hC⟩ := hb
    exact ⟨C, fun x => by simpa using hC x⟩
  have hs : ∀ r, IsSimpleBorel fun x => conj (simpleApprox f hf r x) := fun r =>
    (isSimpleBorel_simpleApprox f hf r).conjugate
  have h₁ := tendsto_limitVector G hm (mem_functionalDomain_of_isBounded E hbc ψ) hs
    (b := fun x => 3 * ‖f x‖ₑ)
    (lintegral_const_mul_enorm_sq_lt_top hf (by simp) (mem_functionalDomain_of_isBounded E hb ψ))
    (fun r x => by
      rw [← map_sub, ← ofReal_norm, RCLike.norm_conj, ofReal_norm]
      exact enorm_simpleApprox_sub_le f hf r x)
    (fun x => (Complex.continuous_conj.tendsto _).comp (tendsto_simpleApprox f hf x))
  have h₂ := tendsto_simpleApprox_limitVector G hf (mem_functionalDomain_of_isBounded E hb φ)
  refine tendsto_nhds_unique (h₂.inner tendsto_const_nhds)
    ((tendsto_const_nhds.inner h₁).congr fun r => ?_)
  rw [G.simple.conjugate (isSimpleBorel_simpleApprox f hf r), ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
end Products
section Rules
variable {E : ProjectionMeasure n ℋ} {f g : (Fin n → ℝ) → ℂ} {ψ : ℋ}
theorem unboundedOperator_ext {ℋ₀ : Type} [NormedAddCommGroup ℋ₀] [InnerProductSpace ℂ ℋ₀]
    [CompleteSpace ℋ₀] {A B : UnboundedOperator ℋ₀} (hd : ∀ v, v ∈ A.domain ↔ v ∈ B.domain)
    (hv : ∀ (x : A.domain) (y : B.domain), (x : ℋ₀) = y → A x = B y) : A = B :=
  (unboundedOperator_eq_iff A B).2 ⟨SetLike.ext hd, hv⟩
theorem spectralIntegral_congr (G : Ingredients E) (hf : Measurable f) (hg : Measurable g)
    (hN : E ⟨{x | f x ≠ g x}, (measurableSet_eq_fun hf hg).compl⟩ = 0) :
    E.functionalCalculus f = E.functionalCalculus g := by
  have hae : ∀ ψ, f =ᵐ[E.spectralValueMeasure ψ] g := fun ψ => by
    refine ae_iff.2 ?_
    have hm := (measurableSet_eq_fun hf hg).compl
    have h₀ : E ⟨{x | f x = g x}ᶜ, hm⟩ = 0 := hN
    exact show E.spectralValueMeasure ψ {x | f x = g x}ᶜ = 0 from by
      rw [diagonalMeasure_of_measurableSet E ψ hm, h₀]
      simp
  have hdom : ∀ ψ, ψ ∈ functionalDomain E f ↔ ψ ∈ functionalDomain E g := fun ψ => by
    have e : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) =
        ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) :=
      lintegral_congr_ae ((hae ψ).mono fun x hx => by simp only [hx])
    change ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) < ∞ ↔
      ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) < ∞
    rw [e]
  refine unboundedOperator_ext (fun v => ?_) fun x y hxy => ?_
  · rw [mem_spectralIntegral_domain G hf, mem_spectralIntegral_domain G hg, hdom]
  · rw [spectralIntegral_apply_eq G hf, spectralIntegral_apply_eq G hg, ← hxy]
    have hx : (x : ℋ) ∈ functionalDomain E f := (mem_spectralIntegral_domain G hf).1 x.2
    have hl : Tendsto (fun r =>
        ∫⁻ y, ‖simpleApprox f hf r y - g y‖ₑ ^ 2 ∂(E.spectralValueMeasure x)) atTop (𝓝 0) := by
      have h₁ := tendsto_lintegral_enorm_sub_sq (isSimpleBorel_simpleApprox f hf · |>.1) hf
        (lintegral_const_mul_enorm_sq_lt_top hf (c := 3) (by simp) hx)
        (enorm_simpleApprox_sub_le f hf) (tendsto_simpleApprox f hf)
      refine h₁.congr fun r => lintegral_congr_ae ((hae x).mono fun y hy => ?_)
      simp only [hy]
    exact tendsto_nhds_unique (tendsto_simpleApprox_limitVector G hf hx)
      ((G.limits g hg).isApproximantLimit x ((hdom x).1 hx) _ (isSimpleBorel_simpleApprox f hf) hl)
theorem spectralIntegral_simple (G : Ingredients E) {h : (Fin n → ℝ) → ℂ}
    (hh : IsSimpleBorel h) :
    E.functionalCalculus h = toUnboundedOperator (simpleIntegral E h hh) := by
  have hb := isBoundedComplexFn_of_isSimpleBorel hh
  have hv : ∀ ψ, E.approximantLimit h ψ = simpleIntegral E h hh ψ := fun ψ => by
    have h₁ := (G.limits h hh.1).isApproximantLimit ψ (mem_functionalDomain_of_isBounded E hb ψ)
      (fun _ => h) (fun _ => hh) (by simp)
    exact tendsto_nhds_unique h₁ tendsto_const_nhds
  refine LinearPMap.ext ?_ ?_
  · exact top_unique fun ψ _ =>
      (mem_spectralIntegral_domain G hh.1).2 (mem_functionalDomain_of_isBounded E hb ψ)
  · intro ψ h₁ h₂
    exact (spectralIntegral_apply_eq G hh.1 ⟨ψ, h₁⟩).trans (hv ψ)
theorem norm_boundedIntegralOp_le (G : Ingredients E) (hf : Measurable f)
    (hb : IsBoundedComplexFn f) : ‖E.boundedCalculus f‖ ≤ ⨆ x, ‖f x‖ := by
  have hbdd : BddAbove (range fun x => ‖f x‖) := by
    obtain ⟨C, hC⟩ := hb
    exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  have h₀ : 0 ≤ ⨆ x, ‖f x‖ := (norm_nonneg (f 0)).trans (le_ciSup hbdd 0)
  refine ContinuousLinearMap.opNorm_le_bound _ h₀ fun ψ => ?_
  rw [boundedIntegralOp_apply_eq G hf hb]
  exact norm_limitVector_le G hf h₀ (fun x => le_ciSup hbdd x)
    (mem_functionalDomain_of_isBounded E hb ψ)
theorem inner_eq_polarization_sum {S : Submodule ℂ ℋ} (T : S →ₗ[ℂ] ℋ) (φ ψ : S) :
    ⟪(φ : ℋ), T ψ⟫_ℂ = (1 / 4 : ℂ) * ∑ r ∈ Finset.range 4,
      Complex.I ^ r * ⟪((ψ + Complex.I ^ r • φ : S) : ℋ), T (ψ + Complex.I ^ r • φ)⟫_ℂ := by
  have h2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have h3 : Complex.I ^ 3 = -Complex.I := Complex.I_pow_three
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, h2, h3, map_add,
    map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Submodule.coe_add, Submodule.coe_smul, map_neg, Complex.conj_I, map_one, zero_add]
  linear_combination ((⟪(φ : ℋ), T ψ⟫_ℂ - ⟪(ψ : ℋ), T φ⟫_ℂ) / 2) * Complex.I_sq
theorem clm_ext_of_inner_self {ℋ₀ : Type} [NormedAddCommGroup ℋ₀] [InnerProductSpace ℂ ℋ₀]
    {S T : ℋ₀ →L[ℂ] ℋ₀} (h : ∀ ψ, ⟪ψ, S ψ⟫_ℂ = ⟪ψ, T ψ⟫_ℂ) : S = T := by apply _root_.YangMills.Construction.SpectralPushforward.ext_of_inner_self <;> assumption
theorem inner_boundedIntegralOp (G : Ingredients E) (hf : Measurable f)
    (hb : IsBoundedComplexFn f) (φ ψ : ℋ) :
    ⟪φ, E.boundedCalculus f ψ⟫_ℂ = E.polarizedIntegral φ ψ f := by
  have h₁ := inner_eq_polarization_sum (S := ⊤)
    ((E.boundedCalculus f : ℋ →ₗ[ℂ] ℋ) ∘ₗ (⊤ : Submodule ℂ ℋ).subtype) ⟨φ, trivial⟩ ⟨ψ, trivial⟩
  unfold polarizedIntegral
  refine h₁.trans ?_
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  have hd := mem_functionalDomain_of_isBounded E hb (ψ + Complex.I ^ r • φ)
  have h₂ := inner_limitVector G hf hd
  rw [← boundedIntegralOp_apply_eq G hf hb] at h₂
  exact h₂
end Rules
section Sign
variable {E : ProjectionMeasure n ℋ} {f : (Fin n → ℝ) → ℂ}
theorem boundedIntegralOp_nonneg_iff (G : Ingredients E) (hf : Measurable f)
    (hre : ∀ x, (f x).im = 0) (hb : IsBoundedComplexFn f) :
    LoewnerGe (E.boundedCalculus f) 0 ↔
      E ⟨{x | (f x).re < 0}, measurableSet_lt (Complex.measurable_re.comp hf) measurable_const⟩ =
        0 := by
  have hN : MeasurableSet {x | (f x).re < 0} :=
    measurableSet_lt (Complex.measurable_re.comp hf) measurable_const
  have hI : ∀ ψ, Integrable (fun x => (f x).re) (E.spectralValueMeasure ψ) := fun ψ =>
    (integrable_of_mem_functionalDomain E hf (mem_functionalDomain_of_isBounded E hb ψ)).re
  have hval : ∀ ψ, ⟪ψ, (E.boundedCalculus f - 0) ψ⟫_ℂ =
      ((∫ x, (f x).re ∂(E.spectralValueMeasure ψ) : ℝ) : ℂ) := fun ψ => by
    rw [sub_zero, boundedIntegralOp_apply_eq G hf hb,
      inner_limitVector G hf (mem_functionalDomain_of_isBounded E hb ψ), ← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact Complex.ext (by simp) (by simp [hre x])
  constructor
  · intro h
    refine ContinuousLinearMap.ext fun ψ => ?_
    have hr : E.spectralValueMeasure (E ⟨_, hN⟩ ψ) =
        (E.spectralValueMeasure ψ).restrict {x | (f x).re < 0} := by
      refine Measure.ext fun A hA => ?_
      rw [Measure.restrict_apply hA, diagonalMeasure_of_measurableSet E _ hA,
        diagonalMeasure_of_measurableSet E _ (hA.inter hN)]
      have e := E.map_inter ⟨A, hA⟩ ⟨_, hN⟩
      have e' : E ⟨A ∩ {x | (f x).re < 0}, hA.inter hN⟩ = E ⟨A, hA⟩ * E ⟨_, hN⟩ := e
      rw [e']
      rfl
    have h₁ := h (E ⟨_, hN⟩ ψ)
    rw [hval, hr, Complex.zero_le_real] at h₁
    have hneg : 0 ≤ᵐ[(E.spectralValueMeasure ψ).restrict {x | (f x).re < 0}] fun x => -(f x).re :=
      (ae_restrict_iff' hN).2 (ae_of_all _ fun x hx => by
        have hx' : (f x).re < 0 := hx
        simp only [Pi.zero_apply]
        linarith)
    have hint := ((hI ψ).restrict (s := {x | (f x).re < 0})).neg
    have h₂ : ∫ x, -(f x).re ∂((E.spectralValueMeasure ψ).restrict {x | (f x).re < 0}) = 0 := by
      refine le_antisymm ?_ (integral_nonneg_of_ae hneg)
      rw [integral_neg]
      linarith
    have h₃ := (integral_eq_zero_iff_of_nonneg_ae hneg hint).1 h₂
    have h₄ : (E.spectralValueMeasure ψ).restrict {x | (f x).re < 0} = 0 := by
      have h₅ : ∀ᵐ x ∂((E.spectralValueMeasure ψ).restrict {x | (f x).re < 0}), False := by
        filter_upwards [h₃, ae_restrict_mem hN] with x hx hx'
        have hx'' : (f x).re < 0 := hx'
        simp only [Pi.zero_apply] at hx
        linarith
      simpa using ae_iff.1 h₅
    have h₆ : E.spectralValueMeasure ψ {x | (f x).re < 0} = 0 := by
      rw [← Measure.restrict_apply_univ, h₄]
      rfl
    rw [diagonalMeasure_of_measurableSet E ψ hN] at h₆
    have h₇ : ‖E ⟨_, hN⟩ ψ‖ ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.1 h₆
    have h₈ : ‖E ⟨_, hN⟩ ψ‖ = 0 := by
      have := norm_nonneg (E ⟨_, hN⟩ ψ)
      nlinarith
    simpa using h₈
  · intro h ψ
    rw [hval, Complex.zero_le_real]
    refine integral_nonneg_of_ae ?_
    have h₁ : E.spectralValueMeasure ψ {x | (f x).re < 0} = 0 := by
      rw [diagonalMeasure_of_measurableSet E ψ hN, h]
      simp
    have h₂ : ∀ᵐ x ∂(E.spectralValueMeasure ψ), ¬ (f x).re < 0 := ae_iff.2 (by simpa using h₁)
    filter_upwards [h₂] with x hx
    exact not_lt.1 hx
end Sign
section Image
variable {E : ProjectionMeasure n ℋ} {n' : ℕ} [NeZero n']
  {π : (Fin n → ℝ) → Fin n' → ℝ} {h : (Fin n' → ℝ) → ℂ}
theorem diagonalMeasure_pushforward (hπ : Measurable π) (ψ : ℋ) :
    (E.imageMeasure π hπ).spectralValueMeasure ψ = (E.spectralValueMeasure ψ).map π := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply hπ hA, diagonalMeasure_of_measurableSet _ _ hA,
    diagonalMeasure_of_measurableSet E _ (hπ hA)]
  rfl
theorem isSimpleBorel_comp (hπ : Measurable π) (hh : IsSimpleBorel h) : IsSimpleBorel (h ∘ π) :=
  ⟨hh.1.comp hπ, hh.2.subset (range_comp_subset_range π h)⟩
theorem simpleIntegral_pushforward (G : Ingredients E) (hπ : Measurable π)
    (G' : Ingredients (E.imageMeasure π hπ)) (hh : IsSimpleBorel h) :
    simpleIntegral (E.imageMeasure π hπ) h hh =
      simpleIntegral E (h ∘ π) (isSimpleBorel_comp hπ hh) := by
  refine clm_ext_of_inner_self fun ψ => ?_
  rw [G'.simple.inner hh, G.simple.inner (isSimpleBorel_comp hπ hh), pairIntegral_self G',
    pairIntegral_self G, diagonalMeasure_pushforward,
    integral_map hπ.aemeasurable hh.1.aestronglyMeasurable]
  rfl
theorem spectralIntegral_pushforward (G : Ingredients E) (hπ : Measurable π)
    (G' : Ingredients (E.imageMeasure π hπ)) (hh : Measurable h) :
    (E.imageMeasure π hπ).functionalCalculus h = E.functionalCalculus (h ∘ π) := by
  have hc : Measurable (h ∘ π) := hh.comp hπ
  have hdom : ∀ ψ, ψ ∈ functionalDomain (E.imageMeasure π hπ) h ↔
      ψ ∈ functionalDomain E (h ∘ π) :=
    fun ψ => by
      change _ < ∞ ↔ _ < ∞
      rw [diagonalMeasure_pushforward, lintegral_map (hh.enorm.pow_const 2) hπ]
      rfl
  refine unboundedOperator_ext (fun v => ?_) fun x y hxy => ?_
  · rw [mem_spectralIntegral_domain G' hh, mem_spectralIntegral_domain G hc, hdom]
  · rw [spectralIntegral_apply_eq G' hh, spectralIntegral_apply_eq G hc, ← hxy]
    have hx := (mem_spectralIntegral_domain G' hh).1 x.2
    have hs : ∀ r, IsSimpleBorel (simpleApprox h hh r ∘ π) := fun r =>
      isSimpleBorel_comp hπ (isSimpleBorel_simpleApprox h hh r)
    have h₁ := tendsto_limitVector G hc ((hdom x).1 hx) hs (b := fun y => 3 * ‖(h ∘ π) y‖ₑ)
      (lintegral_const_mul_enorm_sq_lt_top hc (by simp) ((hdom x).1 hx))
      (fun r y => enorm_simpleApprox_sub_le h hh r (π y)) (fun y => tendsto_simpleApprox h hh (π y))
    refine tendsto_nhds_unique ((tendsto_simpleApprox_limitVector G' hh hx).congr fun r => ?_) h₁
    rw [simpleIntegral_pushforward G hπ G' (isSimpleBorel_simpleApprox h hh r)]
end Image
section Transport
variable {E : ProjectionMeasure n ℋ} {ℋ' : Type} [NormedAddCommGroup ℋ']
  [InnerProductSpace ℂ ℋ'] [CompleteSpace ℋ'] {f : (Fin n → ℝ) → ℂ}
theorem conjUnitary_apply_eq (V : ℋ ≃ₗᵢ[ℂ] ℋ') (A : BorelSets n) (ψ : ℋ') :
    E.unitaryTransport V A ψ = V (E A (V.symm ψ)) :=
  rfl
theorem conjUnitary_isNullOn_iff (V : ℋ ≃ₗᵢ[ℂ] ℋ') (A : BorelSets n) :
    (E.unitaryTransport V).VanishesOn A ↔ E.VanishesOn A := by
  constructor
  · intro h
    refine ContinuousLinearMap.ext fun ψ => ?_
    have h₁ : E.unitaryTransport V A (V ψ) = 0 := by
      have h₂ : E.unitaryTransport V A = 0 := h
      rw [h₂]
      rfl
    rw [conjUnitary_apply_eq] at h₁
    simpa using h₁
  · intro h
    refine ContinuousLinearMap.ext fun ψ => ?_
    have h₂ : E A = 0 := h
    rw [conjUnitary_apply_eq, h₂]
    simp
theorem diagonalMeasure_conjUnitary (V : ℋ ≃ₗᵢ[ℂ] ℋ') (ψ : ℋ) :
    (E.unitaryTransport V).spectralValueMeasure (V ψ) = E.spectralValueMeasure ψ := by
  refine Measure.ext fun A hA => ?_
  rw [diagonalMeasure_of_measurableSet _ _ hA, diagonalMeasure_of_measurableSet E _ hA,
    conjUnitary_apply_eq]
  simp
theorem simpleIntegral_conjUnitary (V : ℋ ≃ₗᵢ[ℂ] ℋ') {h : (Fin n → ℝ) → ℂ}
    (hh : IsSimpleBorel h) (ψ : ℋ) :
    simpleIntegral (E.unitaryTransport V) h hh (V ψ) = V (simpleIntegral E h hh ψ) := by
  unfold simpleIntegral
  simp [map_sum, conjUnitary_apply_eq]
theorem spectralIntegral_conjUnitary (G : Ingredients E) (V : ℋ ≃ₗᵢ[ℂ] ℋ')
    (G' : Ingredients (E.unitaryTransport V)) (hf : Measurable f) :
    (E.unitaryTransport V).functionalCalculus f = unitaryConj V (E.functionalCalculus f) := by
  have hdom : ∀ ψ, V ψ ∈ functionalDomain (E.unitaryTransport V) f ↔
      ψ ∈ functionalDomain E f :=
    fun ψ => by
      change _ < ∞ ↔ _ < ∞
      rw [diagonalMeasure_conjUnitary]
  have hval : ∀ ψ (hψ : ψ ∈ functionalDomain E f),
      (E.unitaryTransport V).approximantLimit f (V ψ) = V (E.approximantLimit f ψ) :=
    fun ψ hψ => by
      have h₁ := tendsto_simpleApprox_limitVector G' hf ((hdom ψ).2 hψ)
      have h₂ := (V.continuous.tendsto _).comp (tendsto_simpleApprox_limitVector G hf hψ)
      refine tendsto_nhds_unique h₁ (h₂.congr fun r => ?_)
      exact (simpleIntegral_conjUnitary V (isSimpleBorel_simpleApprox f hf r) ψ).symm
  refine unboundedOperator_ext (fun v => ?_) fun x y hxy => ?_
  · rw [mem_spectralIntegral_domain G' hf]
    constructor
    · intro hv
      refine ⟨V.symm v, ?_, by simp⟩
      refine (mem_spectralIntegral_domain G hf).2 ((hdom _).1 ?_)
      simpa using hv
    · rintro ⟨ψ, hψ, rfl⟩
      exact (hdom ψ).2 ((mem_spectralIntegral_domain G hf).1 hψ)
  · obtain ⟨y, hy⟩ := y
    obtain ⟨ψ, hψ, rfl⟩ := hy
    have h₁ := unitaryConj_apply V (E.functionalCalculus f) ⟨ψ, hψ⟩ ⟨ψ, hψ, rfl⟩
    rw [spectralIntegral_apply_eq G' hf, hxy]
    refine Eq.trans ?_ h₁.symm
    rw [spectralIntegral_apply_eq G hf]
    exact hval ψ ((mem_spectralIntegral_domain G hf).1 hψ)
end Transport
section Uniqueness
variable {E E' : ProjectionMeasure n ℋ}
theorem eq_of_diagonalMeasure (h : ∀ ψ, E'.spectralValueMeasure ψ = E.spectralValueMeasure ψ) :
    E' = E := by
  have h₁ : E'.toFun = E.toFun := funext fun A => clm_ext_of_inner_self fun ψ => by
    have h₂ := E'.spectralValue_eq_spectralValueMeasure ψ A
    have h₃ := E.spectralValue_eq_spectralValueMeasure ψ A
    rw [h ψ] at h₂
    exact h₂.trans h₃.symm
  cases E'
  cases E
  cases h₁
  rfl
theorem diagonalMeasure_eq_of_boxes
    (h : ∀ (Δ : Fin n → Set ℝ) (hΔ : ∀ i, MeasurableSet (Δ i)),
      E' ⟨Set.pi univ Δ, MeasurableSet.univ_pi hΔ⟩ = E ⟨Set.pi univ Δ, MeasurableSet.univ_pi hΔ⟩)
    (ψ : ℋ) : E'.spectralValueMeasure ψ = E.spectralValueMeasure ψ := by
  refine ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi ?_ ?_
  · rintro _ ⟨Δ, hΔ, rfl⟩
    have hΔ' : ∀ i, MeasurableSet (Δ i) := fun i => hΔ i (mem_univ i)
    rw [diagonalMeasure_of_measurableSet E' ψ (MeasurableSet.univ_pi hΔ'),
      diagonalMeasure_of_measurableSet E ψ (MeasurableSet.univ_pi hΔ'), h Δ hΔ']
  · rw [diagonalMeasure_univ, diagonalMeasure_univ]
theorem measurable_expCharacter (x : Fin n → ℝ) :
    Measurable fun ξ : Fin n → ℝ => Complex.exp (Complex.I * ((∑ i, x i * ξ i : ℝ) : ℂ)) := by
  fun_prop
theorem isBoundedComplexFn_expCharacter (x : Fin n → ℝ) :
    IsBoundedComplexFn fun ξ : Fin n → ℝ =>
      Complex.exp (Complex.I * ((∑ i, x i * ξ i : ℝ) : ℂ)) :=
  ⟨1, fun ξ => by
    change ‖Complex.exp (Complex.I * ((∑ i, x i * ξ i : ℝ) : ℂ))‖ ≤ 1
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]⟩
theorem diagonalMeasure_eq_of_characters (G : Ingredients E) (G' : Ingredients E')
    (h : ∀ x : Fin n → ℝ,
      (E'.functionalCalculus fun ξ => Complex.exp (Complex.I * ((∑ i, x i * ξ i : ℝ) : ℂ))) =
        E.functionalCalculus fun ξ => Complex.exp (Complex.I * ((∑ i, x i * ξ i : ℝ) : ℂ)))
    (ψ : ℋ) : E'.spectralValueMeasure ψ = E.spectralValueMeasure ψ := by
  have key : ∀ x : Fin n → ℝ,
      ∫ ξ, Complex.exp (Complex.I * ((∑ i, x i * ξ i : ℝ) : ℂ)) ∂(E'.spectralValueMeasure ψ) =
        ∫ ξ, Complex.exp (Complex.I * ((∑ i, x i * ξ i : ℝ) : ℂ)) ∂(E.spectralValueMeasure ψ) :=
      fun x => by
    have hm := measurable_expCharacter x
    have hb := isBoundedComplexFn_expCharacter x
    have d' := mem_functionalDomain_of_isBounded E' hb ψ
    have d := mem_functionalDomain_of_isBounded E hb ψ
    rw [← inner_limitVector G' hm d', ← inner_limitVector G hm d]
    have m' := (mem_spectralIntegral_domain G' hm).2 d'
    have m := (mem_spectralIntegral_domain G hm).2 d
    have e := (unboundedOperator_eq_iff _ _).1 (h x) |>.2 ⟨ψ, m'⟩ ⟨ψ, m⟩ rfl
    rw [spectralIntegral_apply_eq G' hm, spectralIntegral_apply_eq G hm] at e
    rw [e]
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [charFunDual_apply, charFunDual_apply]
  have e : ∀ v : Fin n → ℝ, Complex.exp ((L v : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((∑ i, (L (Pi.single i 1)) * v i : ℝ) : ℂ)) := fun v => by
    have h₁ : L v = ∑ i, L (Pi.single i 1) * v i := by
      conv_lhs => rw [pi_eq_sum_univ' v]
      simp [map_sum, mul_comm]
    rw [h₁, mul_comm]
  simp only [e]
  exact key _
theorem eq_of_characters_or_boxes (G : Ingredients E) (G' : Ingredients E')
    (h : (∀ x : Fin n → ℝ,
        (E'.functionalCalculus fun ξ => Complex.exp (Complex.I * ((∑ i, x i * ξ i : ℝ) : ℂ))) =
          E.functionalCalculus fun ξ => Complex.exp (Complex.I * ((∑ i, x i * ξ i : ℝ) : ℂ))) ∨
      ∀ (Δ : Fin n → Set ℝ) (hΔ : ∀ i, MeasurableSet (Δ i)),
        E' ⟨Set.pi univ Δ, MeasurableSet.univ_pi hΔ⟩ =
          E ⟨Set.pi univ Δ, MeasurableSet.univ_pi hΔ⟩) : E' = E := by
  rcases h with h | h
  · exact eq_of_diagonalMeasure (diagonalMeasure_eq_of_characters G G' h)
  · exact eq_of_diagonalMeasure (diagonalMeasure_eq_of_boxes h)
theorem eq_spectralIntegral_of_diagonal {f : (Fin n → ℝ) → ℂ} (G : Ingredients E)
    (hf : Measurable f) (B : UnboundedOperator ℋ)
    (hd : (B.domain : Set ℋ) = functionalDomain E f)
    (hq : ∀ ψ : B.domain, ⟪(ψ : ℋ), B ψ⟫_ℂ = ∫ x, f x ∂(E.spectralValueMeasure ψ)) :
    B = E.functionalCalculus f := by
  have hS : B.domain = (E.functionalCalculus f).domain := by
    refine SetLike.coe_injective ?_
    rw [hd, (spectralIntegral_spec G hf).1]
  have hdense : Dense (B.domain : Set ℋ) := hd ▸ (G.limits f hf).dense
  let A' : B.domain →ₗ[ℂ] ℋ :=
    (E.functionalCalculus f).toFun ∘ₗ Submodule.inclusion hS.le
  have hA : ∀ ψ : B.domain, A' ψ = E.approximantLimit f ψ := fun ψ =>
    spectralIntegral_apply_eq G hf ⟨ψ, hS ▸ ψ.2⟩
  let R : B.domain →ₗ[ℂ] ℋ := B.toFun - A'
  have hR : ∀ ψ : B.domain, ⟪(ψ : ℋ), R ψ⟫_ℂ = 0 := fun ψ => by
    have hψ : (ψ : ℋ) ∈ functionalDomain E f := by
      rw [← hd]
      exact ψ.2
    change ⟪(ψ : ℋ), B ψ - A' ψ⟫_ℂ = 0
    rw [inner_sub_right, hq, hA, inner_limitVector G hf hψ, sub_self]
  have hR₀ : ∀ ψ : B.domain, R ψ = 0 := fun ψ => by
    refine hdense.eq_zero_of_inner_right ℂ fun v hv => ?_
    have h₁ := inner_eq_polarization_sum R ⟨v, hv⟩ ψ
    simpa only [hR, mul_zero, Finset.sum_const_zero] using h₁
  refine unboundedOperator_ext (fun v => ?_) fun x y hxy => ?_
  · exact SetLike.ext_iff.1 hS v
  · have h₁ : B x - A' x = 0 := hR₀ x
    rw [sub_eq_zero] at h₁
    rw [h₁, hA, spectralIntegral_apply_eq G hf, hxy]
end Uniqueness
theorem spectralIntegralLaws_holds (hC : IntegralConstruction.IntegralConstructionHolds) :
    SpectralIntegralLawsHold := by
  intro n _ ℋ _ _ _ E
  have given : ∀ {m : ℕ} [NeZero m] {ℋ₀ : Type} [NormedAddCommGroup ℋ₀]
      [InnerProductSpace ℂ ℋ₀] [CompleteSpace ℋ₀] (F : ProjectionMeasure m ℋ₀),
      Ingredients F := by
    intro m _ ℋ₀ _ _ _ F
    obtain ⟨h₁, h₂, h₃⟩ := hC m ℋ₀ F
    exact ⟨h₁, h₂, h₃⟩
  have G := given E
  refine
    { isOperator := fun f hf => spectralIntegral_spec G hf
      norm_sq := fun f hf ψ => ?_
      inner_self := fun f hf ψ => ?_
      add_const_mul := fun f g hf hg z ψ h₁ h₂ => ?_
      calculus_congr := fun f g hf hg hN => spectralIntegral_congr G hf hg hN
      calculus_simple := fun h hh => spectralIntegral_simple G hh
      functionalDomain_eq_univ := fun f _ hb =>
        eq_univ_of_forall (mem_functionalDomain_of_isBounded E hb)
      isBoundedCalculusOf := fun f hf hb => boundedIntegralOp_spec G hf hb
      norm_boundedCalculus_le := fun f hf hb => norm_boundedIntegralOp_le G hf hb
      inner_boundedCalculus := fun f hf hb φ ψ => inner_boundedIntegralOp G hf hb φ ψ
      boundedCalculus_mul := fun f g hf hg hfb hgb => ?_
      star_boundedCalculus := fun f hf hb => ?_
      spectralValueMeasure_boundedCalculus := fun f g _ hg hgb ψ _ A => ?_
      calculus_boundedCalculus := fun f g hf hg hgb ψ hψ => ?_
      loewnerGe_zero_iff := fun f hf hre hb => boundedIntegralOp_nonneg_iff G hf hre hb
      imageMeasure_apply := fun n' _ π hπ B => rfl
      calculus_imageMeasure := fun n' _ π hπ h hh =>
        spectralIntegral_pushforward G hπ (given _) hh
      unitaryTransport_apply := fun ℋ' _ _ _ V A ψ => rfl
      unitaryTransport_vanishesOn := fun ℋ' _ _ _ V A => conjUnitary_isNullOn_iff V A
      calculus_unitaryTransport := fun ℋ' _ _ _ V f hf =>
        spectralIntegral_conjUnitary G V (given _) hf
      ext_of_fourier_or_boxes := fun E' h => eq_of_characters_or_boxes G (given E') h
      eq_functionalCalculus_iff := fun f hf B => ?_
      eq_boundedCalculus_iff := fun f hf hb B => ?_ }
  · have hψ := (mem_spectralIntegral_domain G hf).1 ψ.2
    rw [spectralIntegral_apply_eq G hf]
    exact norm_sq_limitVector G hf hψ
  · have hψ := (mem_spectralIntegral_domain G hf).1 ψ.2
    rw [spectralIntegral_apply_eq G hf]
    exact inner_limitVector G hf hψ
  · have hm : Measurable fun x => f x + z * g x := hf.add (hg.const_mul z)
    have hψf := (mem_spectralIntegral_domain G hf).1 h₁
    have hψg := (mem_spectralIntegral_domain G hg).1 h₂
    have hd := mem_functionalDomain_add hf hg z hψf hψg
    refine ⟨(mem_spectralIntegral_domain G hm).2 hd, ?_⟩
    rw [spectralIntegral_apply_eq G hm, spectralIntegral_apply_eq G hf,
      spectralIntegral_apply_eq G hg]
    exact limitVector_add G hf hg z hψf hψg
  · have hm : Measurable fun x => f x * g x := hf.mul hg
    have hmb : IsBoundedComplexFn fun x => f x * g x := by
      obtain ⟨C, hC⟩ := hfb
      obtain ⟨D, hD⟩ := hgb
      exact ⟨C * D, fun x => by
        rw [norm_mul]
        exact mul_le_mul (hC x) (hD x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))⟩
    refine ContinuousLinearMap.ext fun ψ => ?_
    change E.boundedCalculus f (E.boundedCalculus g ψ) = _
    rw [boundedIntegralOp_apply_eq G hf hfb, boundedIntegralOp_apply_eq G hg hgb,
      boundedIntegralOp_apply_eq G hm hmb]
    exact (limitVector_comp G hf hg hgb (mem_functionalDomain_of_isBounded E hfb ψ)).2.1
  · have hm : Measurable fun x => conj (f x) := Complex.continuous_conj.measurable.comp hf
    have hbc : IsBoundedComplexFn fun x => conj (f x) := by
      obtain ⟨C, hC⟩ := hb
      exact ⟨C, fun x => by simpa using hC x⟩
    refine ContinuousLinearMap.ext fun ψ => ext_inner_left ℂ fun φ => ?_
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      boundedIntegralOp_apply_eq G hf hb, boundedIntegralOp_apply_eq G hm hbc]
    exact inner_limitVector_conj G hf hb φ ψ
  · rw [boundedIntegralOp_apply_eq G hg hgb,
      diagonalMeasure_limitVector G hg (mem_functionalDomain_of_isBounded E hgb ψ),
      withDensity_apply _ A.2]
  · have hψ' := (mem_spectralIntegral_domain G hf).1 hψ
    have hm : Measurable fun x => f x * g x := hf.mul hg
    obtain ⟨h₁, h₂, h₃⟩ := limitVector_comp G hf hg hgb hψ'
    have hχ : E.boundedCalculus g ψ ∈ (E.functionalCalculus f).domain := by
      rw [boundedIntegralOp_apply_eq G hg hgb]
      exact (mem_spectralIntegral_domain G hf).2 (limitVector_mem_functionalDomain G hf hg hgb hψ')
    refine ⟨hχ, (mem_spectralIntegral_domain G hm).2 h₁, ?_, ?_⟩
    · rw [spectralIntegral_apply_eq G hf, spectralIntegral_apply_eq G hm]
      simp only [boundedIntegralOp_apply_eq G hg hgb]
      exact h₂
    · rw [spectralIntegral_apply_eq G hm, boundedIntegralOp_apply_eq G hg hgb,
        spectralIntegral_apply_eq G hf]
      exact h₃
  · constructor
    · rintro ⟨h₁, h₂⟩
      exact eq_spectralIntegral_of_diagonal G hf B h₁ h₂
    · rintro rfl
      refine ⟨(spectralIntegral_spec G hf).1, fun ψ => ?_⟩
      rw [spectralIntegral_apply_eq G hf]
      exact inner_limitVector G hf ((mem_spectralIntegral_domain G hf).1 ψ.2)
  · constructor
    · intro h
      refine ContinuousLinearMap.ext fun ψ => ext_inner_left ℂ fun φ => ?_
      rw [h, inner_boundedIntegralOp G hf hb]
    · rintro rfl φ ψ
      exact inner_boundedIntegralOp G hf hb φ ψ
end YangMills.Construction.SpectralTheory.IntegralLawsProof
