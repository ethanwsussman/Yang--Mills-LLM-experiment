import YangMills.Construction.EuclideanSpectral.FunctionalCalculusTransport
import YangMills.Construction.SpectralTheory.IntegralConstruction
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate
noncomputable section
namespace YangMills.Construction.SpectralTheory.IntegralConstructionArgument
open YangMills.Construction.SpectralTheory YangMills.Construction.SpectralTheory.ProjectionMeasure
variable {n : ℕ} [NeZero n] {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
  [CompleteSpace ℋ]
theorem inner_apply_eq_polarization (T : ℋ →L[ℂ] ℋ) (φ ψ : ℋ) :
    ⟪φ, T ψ⟫_ℂ = (1 / 4 : ℂ) * ∑ r ∈ Finset.range 4,
      Complex.I ^ r * ⟪ψ + Complex.I ^ r • φ, T (ψ + Complex.I ^ r • φ)⟫_ℂ := by
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := Complex.I_pow_three
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, hI2, hI3, map_add,
    map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    map_neg, Complex.conj_I, map_one, zero_add]
  linear_combination ((⟪φ, T ψ⟫_ℂ - ⟪ψ, T φ⟫_ℂ) / 2) * Complex.I_sq
theorem ext_of_inner_self_apply {S T : ℋ →L[ℂ] ℋ} (h : ∀ ψ, ⟪ψ, S ψ⟫_ℂ = ⟪ψ, T ψ⟫_ℂ) : S = T := by apply _root_.YangMills.Construction.EuclideanSpectral.FunctionalCalculus.ext_inner_self <;> assumption
theorem diagonalMeasure_eq_ofReal (E : ProjectionMeasure n ℋ) (ψ : ℋ) {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) : E.spectralValueMeasure ψ A = ENNReal.ofReal (‖E ⟨A, hA⟩ ψ‖ ^ 2) :=
  E.spectralValueMeasure_apply ψ ⟨A, hA⟩
instance diagonalMeasure_isFiniteMeasure (E : ProjectionMeasure n ℋ) (ψ : ℋ) :
    IsFiniteMeasure (E.spectralValueMeasure ψ) := by
  refine ⟨?_⟩
  rw [diagonalMeasure_eq_ofReal E ψ MeasurableSet.univ]
  exact ENNReal.ofReal_lt_top
theorem inner_apply_self_eq_measureReal (E : ProjectionMeasure n ℋ) (ψ : ℋ) (A : BorelSets n) :
    ⟪ψ, E A ψ⟫_ℂ = (((E.spectralValueMeasure ψ).real A.1 : ℝ) : ℂ) :=
  E.spectralValue_eq_spectralValueMeasure ψ A
theorem offDiagonal_eq_polarization (E : ProjectionMeasure n ℋ) (φ ψ : ℋ) (A : BorelSets n) :
    E.spectralPairing φ ψ A =
      (1 / 4 : ℂ) * ∑ r ∈ Finset.range 4, Complex.I ^ r * E.spectralValue (ψ + Complex.I ^ r • φ) A :=
  inner_apply_eq_polarization (E A) φ ψ
theorem offDiagonal_eq_linear_combination (E : ProjectionMeasure n ℋ) (φ ψ : ℋ) :
    ∃ (μ : Fin 4 → Measure (Fin n → ℝ)) (c : Fin 4 → ℂ), (∀ r, IsFiniteMeasure (μ r)) ∧
      ∀ A : BorelSets n, E.spectralPairing φ ψ A = ∑ r, c r * (((μ r A.1).toReal : ℝ) : ℂ) := by
  refine ⟨fun r => E.spectralValueMeasure (ψ + Complex.I ^ (r : ℕ) • φ),
    fun r => (1 / 4 : ℂ) * Complex.I ^ (r : ℕ), fun r => inferInstance, fun A => ?_⟩
  rw [offDiagonal_eq_polarization, Finset.mul_sum, Finset.sum_range]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [E.spectralValue_eq_spectralValueMeasure, mul_assoc]
theorem diagonalMeasure_add_le (E : ProjectionMeasure n ℋ) (ψ φ : ℋ) :
    E.spectralValueMeasure (ψ + φ) ≤
      (2 : ℝ≥0∞) • E.spectralValueMeasure ψ + (2 : ℝ≥0∞) • E.spectralValueMeasure φ := by
  refine Measure.le_iff.2 fun A hA => ?_
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [diagonalMeasure_eq_ofReal E _ hA, diagonalMeasure_eq_ofReal E _ hA,
    diagonalMeasure_eq_ofReal E _ hA]
  have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [htwo, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [map_add]
  have htri := norm_add_le (E ⟨A, hA⟩ ψ) (E ⟨A, hA⟩ φ)
  have hnn := norm_nonneg (E ⟨A, hA⟩ ψ + E ⟨A, hA⟩ φ)
  nlinarith [sq_nonneg (‖E ⟨A, hA⟩ ψ‖ - ‖E ⟨A, hA⟩ φ‖), norm_nonneg (E ⟨A, hA⟩ ψ),
    norm_nonneg (E ⟨A, hA⟩ φ)]
theorem diagonalMeasure_smul (E : ProjectionMeasure n ℋ) (z : ℂ) (ψ : ℋ) :
    E.spectralValueMeasure (z • ψ) = (‖z‖ₑ ^ 2) • E.spectralValueMeasure ψ := by
  refine Measure.ext fun A hA => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [diagonalMeasure_eq_ofReal E _ hA, diagonalMeasure_eq_ofReal E _ hA, map_smul, norm_smul,
    mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg z), ofReal_norm]
section Simple
variable {h h' : (Fin n → ℝ) → ℂ}
omit [NeZero n] in
def asSimpleFunc (hh : IsSimpleBorel h) : SimpleFunc (Fin n → ℝ) ℂ :=
  ⟨h, fun z => hh.1 (measurableSet_singleton z), hh.2⟩
omit [NeZero n] in
theorem integrable_of_isSimpleBorel (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ]
    (hh : IsSimpleBorel h) : Integrable h μ :=
  (asSimpleFunc hh).integrable_of_isFiniteMeasure
theorem inner_simpleIntegral_self (E : ProjectionMeasure n ℋ) (hh : IsSimpleBorel h) (ψ : ℋ) :
    ⟪ψ, simpleIntegral E h hh ψ⟫_ℂ = ∫ x, h x ∂(E.spectralValueMeasure ψ) := by
  have h1 : ∫ x, h x ∂(E.spectralValueMeasure ψ) =
      ∑ z ∈ hh.2.toFinset, (E.spectralValueMeasure ψ).real (h ⁻¹' {z}) • z := by
    have h2 := SimpleFunc.integral_eq_sum (asSimpleFunc hh)
      (integrable_of_isSimpleBorel (E.spectralValueMeasure ψ) hh)
    have h3 : (asSimpleFunc hh).range = hh.2.toFinset := by
      ext z
      simp [asSimpleFunc, SimpleFunc.mem_range]
    rw [h3] at h2
    exact h2
  rw [h1, simpleIntegral, ContinuousLinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, inner_apply_self_eq_measureReal,
    Complex.real_smul, mul_comm]
theorem simpleIntegral_eq_sum (E : ProjectionMeasure n ℋ) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (B : ι → BorelSets n) (hh : IsSimpleBorel h)
    (hs : ∀ x, h x = ∑ i ∈ s, c i * (B i).1.indicator (fun _ => (1 : ℂ)) x) :
    simpleIntegral E h hh = ∑ i ∈ s, c i • E (B i) := by
  refine ext_of_inner_self_apply fun ψ => ?_
  rw [inner_simpleIntegral_self, ContinuousLinearMap.sum_apply, inner_sum]
  simp only [hs]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_indicator_const _ (B i).2, ContinuousLinearMap.smul_apply,
      inner_smul_right, inner_apply_self_eq_measureReal]
    simp
  · intro i _
    exact ((integrable_const (1 : ℂ)).indicator (B i).2).const_mul _
omit [NeZero n] in
theorem eq_sum_fibre_indicator (hh : IsSimpleBorel h) (x : Fin n → ℝ) :
    h x = ∑ z ∈ hh.2.toFinset, z * (h ⁻¹' {z}).indicator (fun _ => (1 : ℂ)) x := by
  rw [Finset.sum_eq_single (h x)]
  · simp
  · intro z _ hz
    simp [Ne.symm hz]
  · intro hx
    exact absurd (hh.2.mem_toFinset.2 ⟨x, rfl⟩) hx
theorem simpleIntegral_add_const_mul (E : ProjectionMeasure n ℋ) (hh : IsSimpleBorel h)
    (hh' : IsSimpleBorel h') (z : ℂ) : simpleIntegral E _ (hh.add_const_mul hh' z) =
      simpleIntegral E h hh + z • simpleIntegral E h' hh' := by
  refine ext_of_inner_self_apply fun ψ => ?_
  rw [inner_simpleIntegral_self, ContinuousLinearMap.add_apply, inner_add_right,
    ContinuousLinearMap.smul_apply, inner_smul_right, inner_simpleIntegral_self,
    inner_simpleIntegral_self,
    integral_add (integrable_of_isSimpleBorel _ hh)
      ((integrable_of_isSimpleBorel _ hh').const_mul z),
    integral_const_mul]
theorem simpleIntegral_mul (E : ProjectionMeasure n ℋ) (hh : IsSimpleBorel h)
    (hh' : IsSimpleBorel h') :
    simpleIntegral E _ (hh.mul hh') = simpleIntegral E h hh * simpleIntegral E h' hh' := by
  rw [simpleIntegral_eq_sum E (hh.2.toFinset ×ˢ hh'.2.toFinset) (fun p => p.1 * p.2)
    (fun p => ⟨h ⁻¹' {p.1} ∩ h' ⁻¹' {p.2}, (hh.1 (measurableSet_singleton _)).inter
      (hh'.1 (measurableSet_singleton _))⟩) (hh.mul hh')]
  · rw [Finset.sum_product]
    conv_rhs => rw [simpleIntegral, simpleIntegral, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [E.map_inter ⟨h ⁻¹' {z}, hh.1 (measurableSet_singleton _)⟩
      ⟨h' ⁻¹' {w}, hh'.1 (measurableSet_singleton _)⟩, smul_mul_smul_comm]
  · intro x
    rw [Finset.sum_product]
    conv_lhs => rw [eq_sum_fibre_indicator hh x, eq_sum_fibre_indicator hh' x, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h1 : h x = z <;> by_cases h2 : h' x = w <;> simp [indicator, h1, h2]
theorem simpleIntegral_conj (E : ProjectionMeasure n ℋ) (hh : IsSimpleBorel h) :
    simpleIntegral E _ hh.conjugate = star (simpleIntegral E h hh) := by
  refine ext_of_inner_self_apply fun ψ => ?_
  rw [inner_simpleIntegral_self, integral_conj, ← inner_simpleIntegral_self E hh,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_conj_symm]
theorem simpleIntegral_indicator (E : ProjectionMeasure n ℋ) (A : BorelSets n) :
    simpleIntegral E _ (IsSimpleBorel.indicator_one A) = E A := by
  refine ext_of_inner_self_apply fun ψ => ?_
  rw [inner_simpleIntegral_self, integral_indicator_const _ A.2, inner_apply_self_eq_measureReal]
  simp
theorem inner_simpleIntegral_eq_pairIntegral (E : ProjectionMeasure n ℋ) (hh : IsSimpleBorel h)
    (φ ψ : ℋ) : ⟪φ, simpleIntegral E h hh ψ⟫_ℂ = E.polarizedIntegral φ ψ h := by
  rw [inner_apply_eq_polarization, polarizedIntegral]
  simp only [inner_simpleIntegral_self]
theorem norm_simpleIntegral_sq (E : ProjectionMeasure n ℋ) (hh : IsSimpleBorel h) (ψ : ℋ) :
    ‖simpleIntegral E h hh ψ‖ ^ 2 = ∫ x, ‖h x‖ ^ 2 ∂(E.spectralValueMeasure ψ) := by
  have h1 : ⟪simpleIntegral E h hh ψ, simpleIntegral E h hh ψ⟫_ℂ =
      ⟪ψ, simpleIntegral E _ (hh.conjugate.mul hh) ψ⟫_ℂ := by
    rw [simpleIntegral_mul E hh.conjugate hh, simpleIntegral_conj E hh,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  rw [inner_simpleIntegral_self] at h1
  have h2 : ∀ x, conj (h x) * h x = ((‖h x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [h2] at h1
  rw [integral_complex_ofReal] at h1
  have h3 := congrArg RCLike.re h1
  rw [inner_self_eq_norm_sq] at h3
  simpa using h3
end Simple
section Functions
variable {f : (Fin n → ℝ) → ℂ}
theorem ofReal_norm_sq_eq_enorm_sq {V : Type*} [SeminormedAddCommGroup V] (v : V) :
    ENNReal.ofReal (‖v‖ ^ 2) = ‖v‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg v), ofReal_norm]
omit [NeZero n] in
theorem integrable_norm_sq_of_isSimpleBorel (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ]
    {g : (Fin n → ℝ) → ℂ} (hg : IsSimpleBorel g) : Integrable (fun x => ‖g x‖ ^ 2) μ :=
  by
  have h := ((asSimpleFunc hg).map fun z => ‖z‖ ^ 2).integrable_of_isFiniteMeasure (μ := μ)
  rw [SimpleFunc.coe_map] at h
  exact h
omit [NeZero n] in
theorem lintegral_enorm_sq_eq_eLpNorm_sq (μ : Measure (Fin n → ℝ)) (g : (Fin n → ℝ) → ℂ) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = eLpNorm g 2 μ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := g) (p := 2) (by norm_num)
  simp only [NNReal.coe_ofNat, ENNReal.rpow_ofNat, ENNReal.coe_ofNat] at h
  exact h.symm
omit [NeZero n] in
theorem exists_isSimpleBorel_tendsto (μ : Measure (Fin n → ℝ)) (hf : Measurable f)
    (hμ : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ < ∞) :
    ∃ h : ℕ → (Fin n → ℝ) → ℂ, (∀ r, IsSimpleBorel (h r)) ∧
      Tendsto (fun r => ∫⁻ x, ‖h r x - f x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hi : eLpNorm (fun x => f x - 0) 2 μ < ∞ := by
    simp only [sub_zero]
    rw [lintegral_enorm_sq_eq_eLpNorm_sq] at hμ
    by_contra hc
    rw [not_lt_top_iff.1 hc] at hμ
    simp at hμ
  have ht := SimpleFunc.tendsto_approxOn_Lp_eLpNorm hf (s := univ) (y₀ := 0) (mem_univ 0)
    (p := 2) (by norm_num) (μ := μ) (Eventually.of_forall fun x => by simp) hi
  refine ⟨fun r => SimpleFunc.approxOn f hf univ 0 (mem_univ 0) r,
    fun r => ⟨SimpleFunc.measurable _, SimpleFunc.finite_range _⟩, ?_⟩
  have h2 := ENNReal.Tendsto.pow (n := 2) ht
  rw [zero_pow two_ne_zero] at h2
  exact h2.congr fun r => (lintegral_enorm_sq_eq_eLpNorm_sq μ _).symm
theorem ofReal_norm_simpleIntegral_sub_sq (E : ProjectionMeasure n ℋ) {g g' : (Fin n → ℝ) → ℂ}
    (hg : IsSimpleBorel g) (hg' : IsSimpleBorel g') (ψ : ℋ) :
    ENNReal.ofReal (‖simpleIntegral E g hg ψ - simpleIntegral E g' hg' ψ‖ ^ 2) =
      ∫⁻ x, ‖g x - g' x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) := by
  have h1 := norm_simpleIntegral_sq E (hg.add_const_mul hg' (-1)) ψ
  rw [simpleIntegral_add_const_mul E hg hg' (-1)] at h1
  have h2 : (simpleIntegral E g hg + (-1 : ℂ) • simpleIntegral E g' hg') ψ =
      simpleIntegral E g hg ψ - simpleIntegral E g' hg' ψ := by
    simp [sub_eq_add_neg]
  rw [h2] at h1
  rw [h1, ofReal_integral_eq_lintegral_ofReal
    (integrable_norm_sq_of_isSimpleBorel _ (hg.add_const_mul hg' (-1)))
    (Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [ofReal_norm_sq_eq_enorm_sq, neg_one_mul, ← sub_eq_add_neg]
omit [NeZero n] in
theorem enorm_sub_sq_le_two_mul (a b c : ℂ) :
    ‖a - b‖ₑ ^ 2 ≤ 2 * ‖a - c‖ₑ ^ 2 + 2 * ‖b - c‖ₑ ^ 2 := by
  rw [← ofReal_norm_sq_eq_enorm_sq, ← ofReal_norm_sq_eq_enorm_sq, ← ofReal_norm_sq_eq_enorm_sq]
  have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [htwo, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h : ‖a - b‖ ≤ ‖a - c‖ + ‖b - c‖ := norm_sub_le_norm_sub_add_norm_sub a c b |>.trans_eq (by
    rw [norm_sub_rev c b])
  have h0 := norm_nonneg (a - b)
  nlinarith [sq_nonneg (‖a - c‖ - ‖b - c‖), norm_nonneg (a - c), norm_nonneg (b - c)]
theorem ofReal_norm_simpleIntegral_sub_sq_le (E : ProjectionMeasure n ℋ)
    {g g' : (Fin n → ℝ) → ℂ} (hf : Measurable f) (hg : IsSimpleBorel g)
    (hg' : IsSimpleBorel g') (ψ : ℋ) :
    ENNReal.ofReal (‖simpleIntegral E g hg ψ - simpleIntegral E g' hg' ψ‖ ^ 2) ≤
      2 * ∫⁻ x, ‖g x - f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) +
        2 * ∫⁻ x, ‖g' x - f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) := by
  have m : ∀ {k : (Fin n → ℝ) → ℂ}, IsSimpleBorel k →
      Measurable fun x => ‖k x - f x‖ₑ ^ 2 := fun hk => (hk.1.sub hf).enorm.pow_const 2
  rw [ofReal_norm_simpleIntegral_sub_sq, ← lintegral_const_mul _ (m hg),
    ← lintegral_const_mul _ (m hg'), ← lintegral_add_left ((m hg).const_mul _)]
  exact lintegral_mono fun x => enorm_sub_sq_le_two_mul _ _ _
theorem norm_lt_of_ofReal_norm_sq_lt {w : ℋ} {ε : ℝ} (hε : 0 < ε)
    (h : ENNReal.ofReal (‖w‖ ^ 2) < ENNReal.ofReal (ε ^ 2)) : ‖w‖ < ε :=
  lt_of_pow_lt_pow_left₀ 2 hε.le ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 h)
theorem tendsto_zero_of_ofReal_norm_sq_le {w : ℕ → ℋ} {c : ℕ → ℝ≥0∞}
    (hc : Tendsto c atTop (𝓝 0))
    (hw : ∀ r, ENNReal.ofReal (‖w r‖ ^ 2) ≤ c r) : Tendsto w atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have hpos : 0 < ENNReal.ofReal (ε ^ 2) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hc).2 _ hpos)
  refine ⟨N, fun r hr => ?_⟩
  rw [dist_zero_right]
  exact norm_lt_of_ofReal_norm_sq_lt hε ((hw r).trans_lt (hN r hr))
theorem cauchySeq_simpleIntegral_apply (E : ProjectionMeasure n ℋ) (hf : Measurable f) (ψ : ℋ)
    {h : ℕ → (Fin n → ℝ) → ℂ} (hh : ∀ r, IsSimpleBorel (h r))
    (ht : Tendsto (fun r => ∫⁻ x, ‖h r x - f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ)) atTop (𝓝 0)) :
    CauchySeq fun r => simpleIntegral E (h r) (hh r) ψ := by
  refine Metric.cauchySeq_iff.2 fun ε hε => ?_
  have h2 : Tendsto (fun r => 2 * ∫⁻ x, ‖h r x - f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ)) atTop
      (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := 2) ht (Or.inr (by simp))
  have hpos : 0 < ENNReal.ofReal (ε ^ 2 / 2) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 h2).2 _ hpos)
  refine ⟨N, fun r hr s hs => ?_⟩
  rw [dist_eq_norm]
  refine norm_lt_of_ofReal_norm_sq_lt hε
    ((ofReal_norm_simpleIntegral_sub_sq_le E hf (hh r) (hh s) ψ).trans_lt ?_)
  have h3 := ENNReal.add_lt_add (hN r hr) (hN s hs)
  rwa [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves] at h3
theorem exists_isLimitVector (E : ProjectionMeasure n ℋ) (hf : Measurable f) {ψ : ℋ}
    (hψ : ψ ∈ functionalDomain E f) : ∃ χ, E.IsApproximantLimit f ψ χ := by
  obtain ⟨h, hh, ht⟩ := exists_isSimpleBorel_tendsto (E.spectralValueMeasure ψ) hf hψ
  obtain ⟨χ, hχ⟩ := cauchySeq_tendsto_of_complete (cauchySeq_simpleIntegral_apply E hf ψ hh ht)
  refine ⟨χ, fun h' hh' ht' => ?_⟩
  have hc : Tendsto (fun r => 2 * ∫⁻ x, ‖h' r x - f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) +
      2 * ∫⁻ x, ‖h r x - f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ)) atTop (𝓝 0) := by
    simpa using (ENNReal.Tendsto.const_mul (a := 2) ht' (Or.inr (by simp))).add
      (ENNReal.Tendsto.const_mul (a := 2) ht (Or.inr (by simp)))
  have hd := tendsto_zero_of_ofReal_norm_sq_le hc
    fun r => ofReal_norm_simpleIntegral_sub_sq_le E hf (hh' r) (hh r) ψ
  simpa using hd.add hχ
theorem isLimitVector_unique (E : ProjectionMeasure n ℋ) (hf : Measurable f) {ψ χ χ' : ℋ}
    (hψ : ψ ∈ functionalDomain E f) (h₁ : E.IsApproximantLimit f ψ χ)
    (h₂ : E.IsApproximantLimit f ψ χ') : χ = χ' := by
  obtain ⟨h, hh, ht⟩ := exists_isSimpleBorel_tendsto (E.spectralValueMeasure ψ) hf hψ
  exact tendsto_nhds_unique (h₁ h hh ht) (h₂ h hh ht)
theorem isLimitVector_limitVector (E : ProjectionMeasure n ℋ) (hf : Measurable f) {ψ : ℋ}
    (hψ : ψ ∈ functionalDomain E f) : E.IsApproximantLimit f ψ (E.approximantLimit f ψ) :=
  Classical.epsilon_spec (exists_isLimitVector E hf hψ)
theorem lintegral_diagonalMeasure_add_smul_le (E : ProjectionMeasure n ℋ)
    (g : (Fin n → ℝ) → ℝ≥0∞) (ψ φ : ℋ) (z : ℂ) :
    ∫⁻ x, g x ∂(E.spectralValueMeasure (ψ + z • φ)) ≤
      2 * ∫⁻ x, g x ∂(E.spectralValueMeasure ψ) +
        2 * (‖z‖ₑ ^ 2 * ∫⁻ x, g x ∂(E.spectralValueMeasure φ)) := by
  refine (lintegral_mono' (diagonalMeasure_add_le E ψ (z • φ)) le_rfl).trans_eq ?_
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, diagonalMeasure_smul,
    lintegral_smul_measure]
  simp only [smul_eq_mul]
theorem diagonalMeasure_zero (E : ProjectionMeasure n ℋ) :
    E.spectralValueMeasure (0 : ℋ) = 0 := by
  simpa using diagonalMeasure_smul E 0 (0 : ℋ)
def functionalDomainSubmodule (E : ProjectionMeasure n ℋ) (f : (Fin n → ℝ) → ℂ) :
    Submodule ℂ ℋ where
  carrier := functionalDomain E f
  add_mem' {ψ φ} hψ hφ := by
    have h := lintegral_diagonalMeasure_add_smul_le E (fun x => ‖f x‖ₑ ^ 2) ψ φ 1
    rw [one_smul] at h
    refine h.trans_lt ?_
    have hψ' : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) < ∞ := hψ
    have hφ' : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(E.spectralValueMeasure φ) < ∞ := hφ
    simp only [enorm_one, one_pow, one_mul]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hψ',
      ENNReal.mul_lt_top (by simp) hφ'⟩
  zero_mem' := by
    change ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(E.spectralValueMeasure (0 : ℋ)) < ∞
    simp [diagonalMeasure_zero]
  smul_mem' z ψ hψ := by
    change ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(E.spectralValueMeasure (z • ψ)) < ∞
    have hψ' : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) < ∞ := hψ
    rw [diagonalMeasure_smul, lintegral_smul_measure, smul_eq_mul]
    exact ENNReal.mul_lt_top (by simp) hψ'
theorem limitVector_add_smul (E : ProjectionMeasure n ℋ) (hf : Measurable f) {ψ φ : ℋ}
    (hψ : ψ ∈ functionalDomain E f) (hφ : φ ∈ functionalDomain E f) (z : ℂ) :
    E.approximantLimit f (ψ + z • φ) =
      E.approximantLimit f ψ + z • E.approximantLimit f φ := by
  have hψφ : ψ + z • φ ∈ functionalDomain E f :=
    (functionalDomainSubmodule E f).add_mem hψ ((functionalDomainSubmodule E f).smul_mem z hφ)
  have hψ' : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) < ∞ := hψ
  have hφ' : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(E.spectralValueMeasure φ) < ∞ := hφ
  obtain ⟨h, hh, ht⟩ :=
    exists_isSimpleBorel_tendsto (E.spectralValueMeasure ψ + E.spectralValueMeasure φ) hf
      (by rw [lintegral_add_measure]; exact ENNReal.add_lt_top.2 ⟨hψ', hφ'⟩)
  simp only [lintegral_add_measure] at ht
  have t₁ : Tendsto (fun r => ∫⁻ x, ‖h r x - f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ)) atTop
      (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
      fun _ => le_self_add
  have t₂ : Tendsto (fun r => ∫⁻ x, ‖h r x - f x‖ₑ ^ 2 ∂(E.spectralValueMeasure φ)) atTop
      (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
      fun _ => le_add_self
  have t₃ : Tendsto (fun r => ∫⁻ x, ‖h r x - f x‖ₑ ^ 2 ∂(E.spectralValueMeasure (ψ + z • φ)))
      atTop (𝓝 0) := by
    have hc : Tendsto (fun r => 2 * ∫⁻ x, ‖h r x - f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) +
        2 * (‖z‖ₑ ^ 2 * ∫⁻ x, ‖h r x - f x‖ₑ ^ 2 ∂(E.spectralValueMeasure φ))) atTop (𝓝 0) := by
      simpa using (ENNReal.Tendsto.const_mul (a := 2) t₁ (Or.inr (by simp))).add
        (ENNReal.Tendsto.const_mul (a := 2)
          (ENNReal.Tendsto.const_mul (a := ‖z‖ₑ ^ 2) t₂ (Or.inr (by simp))) (Or.inr (by simp)))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun _ => zero_le)
      fun r => lintegral_diagonalMeasure_add_smul_le E _ ψ φ z
  have a₁ := isLimitVector_limitVector E hf hψ h hh t₁
  have a₂ := isLimitVector_limitVector E hf hφ h hh t₂
  have a₃ := isLimitVector_limitVector E hf hψφ h hh t₃
  refine tendsto_nhds_unique a₃ ((a₁.add (a₂.const_smul z)).congr fun r => ?_)
  rw [map_add, map_smul]
theorem diagonalMeasure_apply_self (E : ProjectionMeasure n ℋ) (B : BorelSets n) (ψ : ℋ) :
    E.spectralValueMeasure (E B ψ) = (E.spectralValueMeasure ψ).restrict B.1 := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.restrict_apply hA, diagonalMeasure_eq_ofReal E _ hA,
    diagonalMeasure_eq_ofReal E _ (hA.inter B.2), E.map_inter ⟨A, hA⟩ B]
  rfl
theorem apply_add_apply_compl (E : ProjectionMeasure n ℋ) (B : BorelSets n) :
    E B + E ⟨B.1ᶜ, B.2.compl⟩ = 1 := by
  refine ext_of_inner_self_apply fun ψ => ?_
  have h := inner_apply_self_eq_measureReal E ψ ⟨univ, MeasurableSet.univ⟩
  rw [E.map_univ] at h
  rw [ContinuousLinearMap.add_apply, inner_add_right, inner_apply_self_eq_measureReal,
    inner_apply_self_eq_measureReal, h, ← Complex.ofReal_add,
    measureReal_add_measureReal_compl B.2]
theorem dense_functionalDomain (E : ProjectionMeasure n ℋ) (hf : Measurable f) :
    Dense (functionalDomain E f) := by
  intro ψ
  let B : ℕ → BorelSets n := fun r =>
    ⟨{x | ‖f x‖ ≤ r}, measurableSet_le hf.norm measurable_const⟩
  have hmem : ∀ r, E (B r) ψ ∈ functionalDomain E f := fun r => by
    change ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(E.spectralValueMeasure (E (B r) ψ)) < ∞
    rw [diagonalMeasure_apply_self]
    have h1 : ∫⁻ x in (B r).1, ‖f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) ≤
        ∫⁻ _ in (B r).1, ENNReal.ofReal r ^ 2 ∂(E.spectralValueMeasure ψ) := by
      refine setLIntegral_mono' (B r).2 fun x hx => ?_
      rw [← ofReal_norm]
      gcongr
      exact hx
    refine h1.trans_lt ?_
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)
  have hanti : Antitone fun r => (B r).1ᶜ := fun r s hrs => by
    refine compl_subset_compl.2 fun x hx => ?_
    exact le_trans (show ‖f x‖ ≤ r from hx) (by exact_mod_cast hrs)
  have hint : ⋂ r, (B r).1ᶜ = ∅ := by
    refine eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨r, hr⟩ := exists_nat_ge ‖f x‖
    exact mem_iInter.1 hx r hr
  have ht := tendsto_measure_iInter_atTop (μ := E.spectralValueMeasure ψ)
    (fun r => (B r).2.compl.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hint, measure_empty] at ht
  have hd := tendsto_zero_of_ofReal_norm_sq_le (w := fun r => ψ - E (B r) ψ) ht fun r => by
    have h1 : E (B r) ψ + E ⟨(B r).1ᶜ, (B r).2.compl⟩ ψ = ψ :=
      congrArg (fun T : ℋ →L[ℂ] ℋ => T ψ) (apply_add_apply_compl E (B r))
    have h2 : ψ - E (B r) ψ = E ⟨(B r).1ᶜ, (B r).2.compl⟩ ψ := sub_eq_of_eq_add' h1.symm
    rw [h2]
    exact (diagonalMeasure_eq_ofReal E ψ (B r).2.compl).ge
  have hlim : Tendsto (fun r => E (B r) ψ) atTop (𝓝 ψ) := by
    simpa using (tendsto_const_nhds (x := ψ)).sub hd
  exact mem_closure_of_tendsto hlim (Eventually.of_forall hmem)
theorem limitVectorsExist_of_measurable (E : ProjectionMeasure n ℋ) (hf : Measurable f) :
    E.ApproximantLimitsExist f where
  isSubspace := ⟨functionalDomainSubmodule E f, rfl⟩
  dense := dense_functionalDomain E hf
  exists_simple ψ hψ := exists_isSimpleBorel_tendsto (E.spectralValueMeasure ψ) hf hψ
  existsUnique_limit ψ hψ := by
    obtain ⟨χ, hχ⟩ := exists_isLimitVector E hf hψ
    exact ⟨χ, hχ, fun χ' hχ' => isLimitVector_unique E hf hψ hχ' hχ⟩
  isApproximantLimit ψ hψ := isLimitVector_limitVector E hf hψ
  isLinear := by
    have hzero : E.approximantLimit f 0 = 0 := by
      have h0 : (0 : ℋ) ∈ functionalDomain E f := (functionalDomainSubmodule E f).zero_mem
      have h := limitVector_add_smul E hf h0 h0 1
      simpa using h
    refine ⟨⟨functionalDomainSubmodule E f,
      { toFun := fun ψ => E.approximantLimit f ψ
        map_add' := fun ψ φ => ?_
        map_smul' := fun z ψ => ?_ }⟩, rfl, fun ψ => rfl⟩
    · have h := limitVector_add_smul E hf ψ.2 φ.2 1
      simpa using h
    · have h := limitVector_add_smul E hf (functionalDomainSubmodule E f).zero_mem ψ.2 z
      simpa [hzero] using h
end Functions
theorem integralConstruction_holds : IntegralConstruction.IntegralConstructionHolds := by
  intro n _ ℋ _ _ _ E
  refine ⟨⟨offDiagonal_eq_polarization E, offDiagonal_eq_linear_combination E,
      diagonalMeasure_add_le E, diagonalMeasure_smul E⟩,
    ⟨fun hh hh' z => simpleIntegral_add_const_mul E hh hh' z,
      fun hh hh' => simpleIntegral_mul E hh hh',
      fun hh => simpleIntegral_conj E hh, simpleIntegral_indicator E,
      fun hh φ ψ => inner_simpleIntegral_eq_pairIntegral E hh φ ψ,
      fun hh ψ => norm_simpleIntegral_sq E hh ψ⟩,
    fun f hf => limitVectorsExist_of_measurable E hf⟩
end YangMills.Construction.SpectralTheory.IntegralConstructionArgument
