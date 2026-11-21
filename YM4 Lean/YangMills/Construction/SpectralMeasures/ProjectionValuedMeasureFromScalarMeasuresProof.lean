import YangMills.Construction.EuclideanBorel.PVMFromScalarMeasures
import YangMills.Construction.HilbertSpaces.BoundedFunctionalsBoundedFormsAdjointsAndOrthogonalVectors
import YangMills.Construction.SpectralMeasures.BoundedBorelCalculusProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanBorel.PVMConstruction
variable {m : ℕ}
theorem integrable_of_isBoundedMeasurableFn (μ : Measure (Space m)) [IsFiniteMeasure μ]
    {f : Space m → ℂ} (hf : IsBoundedMeasurableFn f) : Integrable f μ := by apply _root_.YangMills.Construction.EuclideanBorel.MeasureUniqueness.integrable_of_isBoundedMeasurableFn <;> assumption
theorem isBoundedMeasurableFn_mul {f g : Space m → ℂ} (hf : IsBoundedMeasurableFn f)
    (hg : IsBoundedMeasurableFn g) : IsBoundedMeasurableFn (f * g) := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, D, hD⟩ := hg
  refine ⟨hfm.mul hgm, C * D, fun y => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hC y) (hD y) (norm_nonneg _) ((norm_nonneg _).trans (hC y))
theorem isBoundedMeasurableFn_indicator {f : Space m → ℂ} (hf : IsBoundedMeasurableFn f)
    (Δ : BorelSubset m) : IsBoundedMeasurableFn (Δ.1.indicator f) := by
  obtain ⟨hmeas, C, hC⟩ := hf
  refine ⟨hmeas.indicator Δ.2, C, fun y => ?_⟩
  by_cases hy : y ∈ Δ.1
  · rw [Set.indicator_of_mem hy]
    exact hC y
  · rw [Set.indicator_of_notMem hy, norm_zero]
    exact (norm_nonneg _).trans (hC y)
theorem isBoundedMeasurableFn_one : IsBoundedMeasurableFn (1 : Space m → ℂ) :=
  ⟨measurable_const, 1, fun y => by simp⟩
theorem combination_integral_congr {p q : MeasureCombination m}
    (h : p.toSetFunction = q.toSetFunction) {f : Space m → ℂ} (hf : IsBoundedMeasurableFn f) :
    p.integral f = q.integral f := by apply _root_.YangMills.Construction.EuclideanBorel.BoundedCalculusProof.combination_integral_unique <;> assumption
theorem complexIntegral_toSetFunction (p : MeasureCombination m) {f : Space m → ℂ}
    (hf : IsBoundedMeasurableFn f) : complexIntegral p.toSetFunction f = p.integral f := by
  have h : IsFiniteCombinationMeasure p.toSetFunction := ⟨p, rfl⟩
  rw [complexIntegral, dif_pos h]
  exact combination_integral_congr (Classical.choose_spec h) hf
theorem toSetFunction_eq_integral_indicator (p : MeasureCombination m) (Δ : BorelSubset m) :
    p.toSetFunction Δ = p.integral (Δ.1.indicator 1) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : ∫ y, Δ.1.indicator (1 : Space m → ℂ) y ∂(p.component j) =
      (((p.component j).real Δ.1 : ℝ) : ℂ) := by
    have h1 : Δ.1.indicator (1 : Space m → ℂ) = Δ.1.indicator fun _ => (1 : ℂ) := rfl
    rw [h1, integral_indicator_const _ Δ.2, Complex.real_smul, mul_one]
  rw [h]
theorem complexIntegral_indicator_one {ν : BorelSubset m → ℂ} (hν : IsFiniteCombinationMeasure ν)
    (Δ : BorelSubset m) : complexIntegral ν (Δ.1.indicator 1) = ν Δ := by
  obtain ⟨p, rfl⟩ := hν
  rw [complexIntegral_toSetFunction p
      (isBoundedMeasurableFn_indicator isBoundedMeasurableFn_one Δ),
    toSetFunction_eq_integral_indicator]
def combinationOfFamily {ι : Type} [Fintype ι] [Nonempty ι] (c : ι → ℂ) (μs : ι → Measure (Space m))
    (hμs : ∀ i, IsFiniteMeasure (μs i)) : MeasureCombination m where
  numTerms := Fintype.card ι
  one_le_numTerms := Fintype.card_pos
  coeff := c ∘ (Fintype.equivFin ι).symm
  component := μs ∘ (Fintype.equivFin ι).symm
  isFinite := fun _ => hμs _
theorem combinationOfFamily_integral {ι : Type} [Fintype ι] [Nonempty ι] (c : ι → ℂ)
    (μs : ι → Measure (Space m)) (hμs : ∀ i, IsFiniteMeasure (μs i)) (f : Space m → ℂ) :
    (combinationOfFamily c μs hμs).integral f = ∑ i, c i * ∫ y, f y ∂(μs i) :=
  (Fintype.equivFin ι).symm.sum_comp fun i => c i * ∫ y, f y ∂(μs i)
theorem combinationOfFamily_toSetFunction {ι : Type} [Fintype ι] [Nonempty ι] (c : ι → ℂ)
    (μs : ι → Measure (Space m)) (hμs : ∀ i, IsFiniteMeasure (μs i)) (Δ : BorelSubset m) :
    (combinationOfFamily c μs hμs).toSetFunction Δ = ∑ i, c i * (((μs i).real Δ.1 : ℝ) : ℂ) :=
  (Fintype.equivFin ι).symm.sum_comp fun i => c i * (((μs i).real Δ.1 : ℝ) : ℂ)
def pairCombination (a b : ℂ) (p q : MeasureCombination m) : MeasureCombination m :=
  have : Nonempty (Fin p.numTerms ⊕ Fin q.numTerms) := ⟨Sum.inl ⟨0, p.one_le_numTerms⟩⟩
  combinationOfFamily (ι := Fin p.numTerms ⊕ Fin q.numTerms)
    (Sum.elim (fun j => a * p.coeff j) fun j => b * q.coeff j)
    (Sum.elim p.component q.component)
    (fun i => by
      rcases i with j | j
      · exact p.isFinite j
      · exact q.isFinite j)
theorem isFiniteCombinationMeasure_linear {ν₁ ν₂ : BorelSubset m → ℂ}
    (h₁ : IsFiniteCombinationMeasure ν₁) (h₂ : IsFiniteCombinationMeasure ν₂) (a b : ℂ) :
    IsFiniteCombinationMeasure (fun Δ => a * ν₁ Δ + b * ν₂ Δ) ∧
      ∀ f : Space m → ℂ, IsBoundedMeasurableFn f →
        complexIntegral (fun Δ => a * ν₁ Δ + b * ν₂ Δ) f =
          a * complexIntegral ν₁ f + b * complexIntegral ν₂ f := by
  obtain ⟨p, rfl⟩ := h₁
  obtain ⟨q, rfl⟩ := h₂
  have : Nonempty (Fin p.numTerms ⊕ Fin q.numTerms) := ⟨Sum.inl ⟨0, p.one_le_numTerms⟩⟩
  have hfun : (pairCombination a b p q).toSetFunction =
      fun Δ => a * p.toSetFunction Δ + b * q.toSetFunction Δ := by
    funext Δ
    rw [pairCombination, combinationOfFamily_toSetFunction, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, MeasureCombination.toSetFunction, Finset.mul_sum,
      mul_assoc]
  refine ⟨⟨_, hfun⟩, fun f hf => ?_⟩
  rw [← hfun, complexIntegral_toSetFunction _ hf, complexIntegral_toSetFunction _ hf,
    complexIntegral_toSetFunction _ hf, pairCombination, combinationOfFamily_integral,
    Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, MeasureCombination.integral, Finset.mul_sum, mul_assoc]
def singleCombination (μ : Measure (Space m)) (h : IsFiniteMeasure μ) : MeasureCombination m where
  numTerms := 1
  one_le_numTerms := le_rfl
  coeff := fun _ => 1
  component := fun _ => μ
  isFinite := fun _ => h
theorem singleCombination_toSetFunction (μ : Measure (Space m)) (h : IsFiniteMeasure μ) :
    (singleCombination μ h).toSetFunction = fun Δ => ((μ.real Δ.1 : ℝ) : ℂ) := by
  funext Δ
  show ∑ _j : Fin 1, (1 : ℂ) * ((μ.real Δ.1 : ℝ) : ℂ) = _
  simp
theorem singleCombination_integral (μ : Measure (Space m)) (h : IsFiniteMeasure μ)
    (f : Space m → ℂ) : (singleCombination μ h).integral f = ∫ y, f y ∂μ := by
  show ∑ _j : Fin 1, (1 : ℂ) * ∫ y, f y ∂μ = _
  simp
theorem isFiniteCombinationMeasure_of_finite (μ : Measure (Space m)) (h : IsFiniteMeasure μ) :
    IsFiniteCombinationMeasure (fun Δ => ((μ.real Δ.1 : ℝ) : ℂ)) ∧
      ∀ f : Space m → ℂ, IsBoundedMeasurableFn f →
        complexIntegral (fun Δ => ((μ.real Δ.1 : ℝ) : ℂ)) f = ∫ y, f y ∂μ := by
  refine ⟨⟨singleCombination μ h, singleCombination_toSetFunction μ h⟩, fun f hf => ?_⟩
  rw [← singleCombination_toSetFunction μ h, complexIntegral_toSetFunction _ hf,
    singleCombination_integral]
def signPart (g : Space m → ℂ) : Fin 4 → Space m → ℝ≥0 :=
  ![fun y => Real.toNNReal (g y).re, fun y => Real.toNNReal (-(g y).re),
    fun y => Real.toNNReal (g y).im, fun y => Real.toNNReal (-(g y).im)]
def signPhase : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]
theorem sum_signPhase_mul_signPart (g : Space m → ℂ) (y : Space m) :
    ∑ k, signPhase k * ((signPart g k y : ℝ) : ℂ) = g y := by
  have hre : ((Real.toNNReal (g y).re : ℝ) - (Real.toNNReal (-(g y).re) : ℝ)) = (g y).re := by
    rw [Real.coe_toNNReal', Real.coe_toNNReal']
    exact max_zero_sub_max_neg_zero_eq_self _
  have him : ((Real.toNNReal (g y).im : ℝ) - (Real.toNNReal (-(g y).im) : ℝ)) = (g y).im := by
    rw [Real.coe_toNNReal', Real.coe_toNNReal']
    exact max_zero_sub_max_neg_zero_eq_self _
  rw [Fin.sum_univ_four]
  apply Complex.ext
  · simpa [signPart, signPhase, sub_eq_add_neg] using hre
  · simpa [signPart, signPhase, sub_eq_add_neg] using him
theorem measurable_signPart {g : Space m → ℂ} (hg : Measurable g) (k : Fin 4) :
    Measurable (signPart g k) := by
  have hre : Measurable fun y => (g y).re := Complex.measurable_re.comp hg
  have him : Measurable fun y => (g y).im := Complex.measurable_im.comp hg
  fin_cases k
  · exact measurable_real_toNNReal.comp hre
  · exact measurable_real_toNNReal.comp hre.neg
  · exact measurable_real_toNNReal.comp him
  · exact measurable_real_toNNReal.comp him.neg
theorem signPart_le_norm (g : Space m → ℂ) (k : Fin 4) (y : Space m) :
    (signPart g k y : ℝ) ≤ ‖g y‖ := by
  have h0 : 0 ≤ ‖g y‖ := norm_nonneg _
  have hre : |(g y).re| ≤ ‖g y‖ := Complex.abs_re_le_norm _
  have him : |(g y).im| ≤ ‖g y‖ := Complex.abs_im_le_norm _
  fin_cases k
  · exact (Real.coe_toNNReal' _).le.trans (max_le ((le_abs_self _).trans hre) h0)
  · exact (Real.coe_toNNReal' _).le.trans (max_le ((neg_le_abs _).trans hre) h0)
  · exact (Real.coe_toNNReal' _).le.trans (max_le ((le_abs_self _).trans him) h0)
  · exact (Real.coe_toNNReal' _).le.trans (max_le ((neg_le_abs _).trans him) h0)
theorem isBoundedMeasurableFn_signPart {g : Space m → ℂ} (hg : IsBoundedMeasurableFn g)
    (k : Fin 4) : IsBoundedMeasurableFn fun y => ((signPart g k y : ℝ) : ℂ) := by
  obtain ⟨hmeas, C, hC⟩ := hg
  refine ⟨?_, C, fun y => ?_⟩
  · exact Complex.measurable_ofReal.comp
      (measurable_coe_nnreal_real.comp (measurable_signPart hmeas k))
  · rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    exact (signPart_le_norm g k y).trans (hC y)
theorem isFiniteMeasure_withDensity_signPart (μ : Measure (Space m)) [IsFiniteMeasure μ]
    {g : Space m → ℂ} (hg : IsBoundedMeasurableFn g) (k : Fin 4) :
    IsFiniteMeasure (μ.withDensity fun y => (signPart g k y : ℝ≥0∞)) := by
  obtain ⟨_, C, hC⟩ := hg
  refine isFiniteMeasure_withDensity (ne_of_lt ?_)
  calc ∫⁻ y, (signPart g k y : ℝ≥0∞) ∂μ ≤ ∫⁻ _, (Real.toNNReal C : ℝ≥0∞) ∂μ := by
        refine lintegral_mono fun y => ENNReal.coe_le_coe.2 ?_
        exact NNReal.coe_le_coe.1
          (((signPart_le_norm g k y).trans (hC y)).trans (Real.le_coe_toNNReal C))
    _ < ∞ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top μ _)
theorem sum_integral_withDensity_signPart (μ : Measure (Space m)) [IsFiniteMeasure μ]
    {g F : Space m → ℂ} (hg : IsBoundedMeasurableFn g) (hF : IsBoundedMeasurableFn F) :
    ∑ k, signPhase k * ∫ y, F y ∂(μ.withDensity fun y => (signPart g k y : ℝ≥0∞)) =
      ∫ y, (F * g) y ∂μ := by
  have h : ∀ k, ∫ y, F y ∂(μ.withDensity fun y => (signPart g k y : ℝ≥0∞)) =
      ∫ y, (F * fun y => ((signPart g k y : ℝ) : ℂ)) y ∂μ := by
    intro k
    rw [integral_withDensity_eq_integral_smul (measurable_signPart hg.1 k) F]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Pi.mul_apply, NNReal.smul_def, Complex.real_smul]
    ring
  simp only [h]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun k _ =>
    (integrable_of_isBoundedMeasurableFn μ
      (isBoundedMeasurableFn_mul hF (isBoundedMeasurableFn_signPart hg k))).const_mul _]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Pi.mul_apply]
  conv_rhs => rw [← sum_signPhase_mul_signPart g y, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring
def densityCombination (p : MeasureCombination m) {g : Space m → ℂ}
    (hg : IsBoundedMeasurableFn g) : MeasureCombination m :=
  have : Nonempty (Fin p.numTerms) := ⟨⟨0, p.one_le_numTerms⟩⟩
  combinationOfFamily (ι := Fin p.numTerms × Fin 4) (fun i => p.coeff i.1 * signPhase i.2)
    (fun i => (p.component i.1).withDensity fun y => (signPart g i.2 y : ℝ≥0∞))
    (fun i => by
      have := p.isFinite i.1
      exact isFiniteMeasure_withDensity_signPart _ hg i.2)
theorem densityCombination_integral (p : MeasureCombination m) {g F : Space m → ℂ}
    (hg : IsBoundedMeasurableFn g) (hF : IsBoundedMeasurableFn F) :
    (densityCombination p hg).integral F = p.integral (F * g) := by
  have : Nonempty (Fin p.numTerms) := ⟨⟨0, p.one_le_numTerms⟩⟩
  rw [densityCombination, combinationOfFamily_integral, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := p.isFinite j
  rw [← sum_integral_withDensity_signPart (p.component j) hg hF, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring
theorem isFiniteCombinationMeasure_weightedBy {ν : BorelSubset m → ℂ}
    (hν : IsFiniteCombinationMeasure ν) {g : Space m → ℂ} (hg : IsBoundedMeasurableFn g) :
    IsFiniteCombinationMeasure (weightedBy g ν) := by
  obtain ⟨p, rfl⟩ := hν
  refine ⟨densityCombination p hg, ?_⟩
  funext Δ
  rw [toSetFunction_eq_integral_indicator,
    densityCombination_integral p hg
      (isBoundedMeasurableFn_indicator isBoundedMeasurableFn_one Δ),
    weightedBy, complexIntegral_toSetFunction p (isBoundedMeasurableFn_indicator hg Δ)]
  congr 1
  funext y
  by_cases hy : y ∈ Δ.1 <;> simp [hy]
section Diagonal
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {X : BorelSubset m} {M : Set (Space m → ℂ)} {ϱ : M → H →L[ℂ] H} {W : H → Measure (Space m)}
structure DiagonalData (X : BorelSubset m) (M : Set (Space m → ℂ)) (ϱ : M → H →L[ℂ] H)
    (W : H → Measure (Space m)) : Prop where
  isBounded : ∀ u ∈ M, IsBoundedMeasurableFn u
  starClosed : IsStarClosedFamilyOn X M
  separates : SeparatesSupportedMeasures X M
  starHom : IsStarHomOnFamily X M ϱ
  isFinite : ∀ ψ, IsFiniteMeasure (W ψ)
  supported : ∀ ψ, IsSupportedOn (fun Δ => (((W ψ).real Δ.1 : ℝ) : ℂ)) X
  inner_eq_integral : ∀ (ψ : H) (u : M), ⟪ψ, ϱ u ψ⟫_ℂ = ∫ y, u.1 y ∂(W ψ)
theorem eq_of_complexIntegral_eq (hb : ∀ u ∈ M, IsBoundedMeasurableFn u)
    (hd : SeparatesSupportedMeasures X M) {ν₁ ν₂ : BorelSubset m → ℂ}
    (h₁ : IsFiniteCombinationMeasure ν₁) (h₂ : IsFiniteCombinationMeasure ν₂)
    (c₁ : IsSupportedOn ν₁ X) (c₂ : IsSupportedOn ν₂ X)
    (h : ∀ u ∈ M, complexIntegral ν₁ u = complexIntegral ν₂ u) : ν₁ = ν₂ := by
  have hl := isFiniteCombinationMeasure_linear h₁ h₂ 1 (-1)
  have hv := hd _ hl.1 (fun Δ hΔ => by simp [c₁ Δ hΔ, c₂ Δ hΔ]) (fun u hu => by
    rw [hl.2 u (hb u hu), h u hu]
    ring)
  funext Δ
  have := hv Δ
  simp only at this
  linear_combination this
def unitRoot : Fin 4 → ℂ := ![1, Complex.I, -1, -Complex.I]
theorem inner_polarization_sum (A : H →L[ℂ] H) (φ ψ : H) :
    ∑ k, (1 / 4 * conj (unitRoot k)) * ⟪φ + unitRoot k • ψ, A (φ + unitRoot k • ψ)⟫_ℂ =
      ⟪φ, A ψ⟫_ℂ := by
  have r0 : unitRoot 0 = 1 := rfl
  have r1 : unitRoot 1 = Complex.I := rfl
  have r2 : unitRoot 2 = -1 := rfl
  have r3 : unitRoot 3 = -Complex.I := rfl
  simp only [Fin.sum_univ_four, r0, r1, r2, r3, map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, map_one, map_neg, Complex.conj_I, neg_neg]
  linear_combination ((⟪ψ, A φ⟫_ℂ - ⟪φ, A ψ⟫_ℂ) / 2) * Complex.I_mul_I
theorem norm_unitRoot (k : Fin 4) : ‖unitRoot k‖ = 1 := by apply _root_.YangMills.Construction.EuclideanBorel.BoundedCalculusProof.norm_quarterTurn <;> assumption
def polarCombination (S : DiagonalData X M ϱ W) (φ ψ : H) : MeasureCombination m where
  numTerms := 4
  one_le_numTerms := by norm_num
  coeff := fun k => 1 / 4 * conj (unitRoot k)
  component := fun k => W (φ + unitRoot k • ψ)
  isFinite := fun _ => S.isFinite _
def polarMeasure (S : DiagonalData X M ϱ W) (φ ψ : H) : BorelSubset m → ℂ :=
  (polarCombination S φ ψ).toSetFunction
theorem polarMeasure_apply (S : DiagonalData X M ϱ W) (φ ψ : H) (Δ : BorelSubset m) :
    polarMeasure S φ ψ Δ =
      ∑ k : Fin 4, (1 / 4 * conj (unitRoot k)) * (((W (φ + unitRoot k • ψ)).real Δ.1 : ℝ) : ℂ) :=
  rfl
theorem isFiniteCombinationMeasure_polarMeasure (S : DiagonalData X M ϱ W) (φ ψ : H) :
    IsFiniteCombinationMeasure (polarMeasure S φ ψ) :=
  ⟨_, rfl⟩
theorem complexIntegral_polarMeasure (S : DiagonalData X M ϱ W) (φ ψ : H) (u : M) :
    complexIntegral (polarMeasure S φ ψ) u.1 = ⟪φ, ϱ u ψ⟫_ℂ := by
  rw [polarMeasure, complexIntegral_toSetFunction _ (S.isBounded u.1 u.2),
    ← inner_polarization_sum (ϱ u) φ ψ]
  show ∑ k : Fin 4, (1 / 4 * conj (unitRoot k)) * ∫ y, u.1 y ∂(W (φ + unitRoot k • ψ)) = _
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [S.inner_eq_integral]
theorem isSupportedOn_polarMeasure (S : DiagonalData X M ϱ W) (φ ψ : H) :
    IsSupportedOn (polarMeasure S φ ψ) X := by
  intro Δ hΔ
  rw [polarMeasure_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have h0 : (((W (φ + unitRoot k • ψ)).real Δ.1 : ℝ) : ℂ) = 0 := S.supported _ Δ hΔ
  rw [h0, mul_zero]
def diagValues (W : H → Measure (Space m)) (ψ : H) : BorelSubset m → ℂ :=
  fun Δ => (((W ψ).real Δ.1 : ℝ) : ℂ)
theorem isFiniteCombinationMeasure_diagValues (S : DiagonalData X M ϱ W) (ψ : H) :
    IsFiniteCombinationMeasure (diagValues W ψ) :=
  (isFiniteCombinationMeasure_of_finite (W ψ) (S.isFinite ψ)).1
theorem complexIntegral_diagValues (S : DiagonalData X M ϱ W) (ψ : H) (u : M) :
    complexIntegral (diagValues W ψ) u.1 = ⟪ψ, ϱ u ψ⟫_ℂ := by
  rw [S.inner_eq_integral]
  exact (isFiniteCombinationMeasure_of_finite (W ψ) (S.isFinite ψ)).2 _ (S.isBounded _ u.2)
theorem polarMeasure_self (S : DiagonalData X M ϱ W) (ψ : H) :
    polarMeasure S ψ ψ = diagValues W ψ :=
  eq_of_complexIntegral_eq S.isBounded S.separates (isFiniteCombinationMeasure_polarMeasure S ψ ψ)
    (isFiniteCombinationMeasure_diagValues S ψ) (isSupportedOn_polarMeasure S ψ ψ)
    (S.supported ψ) fun u hu =>
      (complexIntegral_polarMeasure S ψ ψ ⟨u, hu⟩).trans
        (complexIntegral_diagValues S ψ ⟨u, hu⟩).symm
theorem diagValues_smul (S : DiagonalData X M ϱ W) {α : ℂ} (hα : ‖α‖ = 1) (ψ : H) :
    diagValues W (α • ψ) = diagValues W ψ :=
  eq_of_complexIntegral_eq S.isBounded S.separates (isFiniteCombinationMeasure_diagValues S _)
    (isFiniteCombinationMeasure_diagValues S ψ) (S.supported _) (S.supported ψ) fun u hu => by
      refine (complexIntegral_diagValues S _ ⟨u, hu⟩).trans
        (Eq.trans ?_ (complexIntegral_diagValues S ψ ⟨u, hu⟩).symm)
      rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', hα]
      simp
theorem measureReal_add_smul_swap (S : DiagonalData X M ϱ W) {α : ℂ} (hα : ‖α‖ = 1) (φ ψ : H)
    (Δ : BorelSubset m) : (W (ψ + α • φ)).real Δ.1 = (W (φ + conj α • ψ)).real Δ.1 := by
  have hv : ψ + α • φ = α • (φ + conj α • ψ) := by
    rw [smul_add, smul_smul, Complex.mul_conj', hα]
    simp [add_comm]
  have h := congrFun (diagValues_smul S hα (φ + conj α • ψ)) Δ
  rw [hv]
  exact Complex.ofReal_injective h
theorem polarMeasure_expand (S : DiagonalData X M ϱ W) (φ ψ : H) (Δ : BorelSubset m) :
    polarMeasure S φ ψ Δ = 1 / 4 * ((((W (φ + unitRoot 0 • ψ)).real Δ.1 : ℝ) : ℂ)
      - Complex.I * (((W (φ + unitRoot 1 • ψ)).real Δ.1 : ℝ) : ℂ)
      - (((W (φ + unitRoot 2 • ψ)).real Δ.1 : ℝ) : ℂ)
      + Complex.I * (((W (φ + unitRoot 3 • ψ)).real Δ.1 : ℝ) : ℂ)) := by
  have c0 : conj (unitRoot 0) = 1 := by simp [unitRoot]
  have c1 : conj (unitRoot 1) = -Complex.I := by simp [unitRoot]
  have c2 : conj (unitRoot 2) = -1 := by simp [unitRoot]
  have c3 : conj (unitRoot 3) = Complex.I := by simp [unitRoot]
  rw [polarMeasure_apply, Fin.sum_univ_four, c0, c1, c2, c3]
  ring
theorem conj_polarMeasure (S : DiagonalData X M ϱ W) (φ ψ : H) (Δ : BorelSubset m) :
    conj (polarMeasure S φ ψ Δ) = polarMeasure S ψ φ Δ := by
  have c0 : conj (unitRoot 0) = unitRoot 0 := by simp [unitRoot]
  have c1 : conj (unitRoot 1) = unitRoot 3 := by simp [unitRoot]
  have c2 : conj (unitRoot 2) = unitRoot 2 := by simp [unitRoot]
  have c3 : conj (unitRoot 3) = unitRoot 1 := by simp [unitRoot]
  have e0 := measureReal_add_smul_swap S (norm_unitRoot 0) φ ψ Δ
  have e1 := measureReal_add_smul_swap S (norm_unitRoot 1) φ ψ Δ
  have e2 := measureReal_add_smul_swap S (norm_unitRoot 2) φ ψ Δ
  have e3 := measureReal_add_smul_swap S (norm_unitRoot 3) φ ψ Δ
  rw [c0] at e0
  rw [c1] at e1
  rw [c2] at e2
  rw [c3] at e3
  have h4 : conj (1 / 4 : ℂ) = 1 / 4 := by
    rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.conj_ofReal _
  rw [polarMeasure_expand, polarMeasure_expand S ψ φ, e0, e1, e2, e3]
  simp only [map_mul, map_add, map_sub, Complex.conj_ofReal, Complex.conj_I, h4]
  ring
theorem polarMeasure_linear_right (S : DiagonalData X M ϱ W) (a b : ℂ) (φ ψ ψ' : H) :
    polarMeasure S φ (a • ψ + b • ψ') =
      fun Δ => a * polarMeasure S φ ψ Δ + b * polarMeasure S φ ψ' Δ := by
  have hl := isFiniteCombinationMeasure_linear (isFiniteCombinationMeasure_polarMeasure S φ ψ)
    (isFiniteCombinationMeasure_polarMeasure S φ ψ') a b
  refine eq_of_complexIntegral_eq S.isBounded S.separates
    (isFiniteCombinationMeasure_polarMeasure S _ _) hl.1 (isSupportedOn_polarMeasure S _ _)
    (fun Δ hΔ => ?_) (fun u hu => ?_)
  · simp [isSupportedOn_polarMeasure S φ ψ Δ hΔ, isSupportedOn_polarMeasure S φ ψ' Δ hΔ]
  · rw [hl.2 u (S.isBounded u hu)]
    refine (complexIntegral_polarMeasure S φ _ ⟨u, hu⟩).trans ?_
    rw [show complexIntegral (polarMeasure S φ ψ) u = _ from
        complexIntegral_polarMeasure S φ ψ ⟨u, hu⟩,
      show complexIntegral (polarMeasure S φ ψ') u = _ from
        complexIntegral_polarMeasure S φ ψ' ⟨u, hu⟩,
      map_add, map_smul, map_smul, inner_add_right, inner_smul_right, inner_smul_right]
theorem polarMeasure_linear_left (S : DiagonalData X M ϱ W) (a b : ℂ) (φ φ' ψ : H)
    (Δ : BorelSubset m) :
    polarMeasure S (a • φ + b • φ') ψ Δ =
      conj a * polarMeasure S φ ψ Δ + conj b * polarMeasure S φ' ψ Δ := by
  rw [← conj_polarMeasure S ψ, polarMeasure_linear_right S a b ψ φ φ']
  simp only [map_add, map_mul, conj_polarMeasure]
theorem isSesquilinear_polarMeasure (S : DiagonalData X M ϱ W) (Δ : BorelSubset m) :
    FormsOperators.IsSesquilinear (fun φ ψ : H => polarMeasure S φ ψ Δ) where
  add_left F₁ F₂ F' := by simpa using polarMeasure_linear_left S 1 1 F₁ F₂ F' Δ
  smul_left c F F' := by simpa using polarMeasure_linear_left S c 0 F F F' Δ
  add_right F F₁ F₂ := by simpa using congrFun (polarMeasure_linear_right S 1 1 F F₁ F₂) Δ
  smul_right c F F' := by simpa using congrFun (polarMeasure_linear_right S c 0 F F' F') Δ
theorem measureReal_univ_eq_norm_sq (S : DiagonalData X M ϱ W) (ψ : H) :
    (W ψ).real Set.univ = ‖ψ‖ ^ 2 := by
  have := S.isFinite ψ
  let w : M := ⟨X.1.indicator fun _ => (1 : ℂ), S.starClosed.indicator_one_mem⟩
  have hw : ϱ w = 1 := S.starHom.map_indicator_one w rfl
  have h := S.inner_eq_integral ψ w
  have h2 : ∫ y, w.1 y ∂(W ψ) = (((W ψ).real X.1 : ℝ) : ℂ) := by
    show ∫ y, X.1.indicator (fun _ => (1 : ℂ)) y ∂(W ψ) = _
    rw [integral_indicator_const _ X.2, Complex.real_smul, mul_one]
  rw [h2, hw, one_apply_eq_self, inner_self_eq_norm_sq_to_K] at h
  have h3 : (W ψ).real X.1ᶜ = 0 := by
    have h0 : (((W ψ).real X.1ᶜ : ℝ) : ℂ) = 0 := S.supported ψ ⟨X.1ᶜ, X.2.compl⟩ subset_rfl
    exact_mod_cast h0
  have h4 : (W ψ).real X.1 = ‖ψ‖ ^ 2 := by
    have h5 : (((W ψ).real X.1 : ℝ) : ℂ) = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
      rw [← h]
      simp
    exact_mod_cast h5
  rw [measureReal_compl X.2] at h3
  linarith
theorem measureReal_le_norm_sq (S : DiagonalData X M ϱ W) (ψ : H) (s : Set (Space m)) :
    (W ψ).real s ≤ ‖ψ‖ ^ 2 := by
  have := S.isFinite ψ
  rw [← measureReal_univ_eq_norm_sq S ψ]
  exact measureReal_mono (Set.subset_univ _)
theorem norm_polarMeasure_le (S : DiagonalData X M ϱ W) (φ ψ : H) (Δ : BorelSubset m) :
    ‖polarMeasure S φ ψ Δ‖ ≤ (‖φ‖ + ‖ψ‖) ^ 2 := by
  have hterm : ∀ k : Fin 4,
      ‖(1 / 4 * conj (unitRoot k)) * (((W (φ + unitRoot k • ψ)).real Δ.1 : ℝ) : ℂ)‖ ≤
        1 / 4 * (‖φ‖ + ‖ψ‖) ^ 2 := by
    intro k
    rw [norm_mul, norm_mul, RCLike.norm_conj, norm_unitRoot, Complex.norm_real,
      Real.norm_of_nonneg measureReal_nonneg]
    have h1 : ‖φ + unitRoot k • ψ‖ ≤ ‖φ‖ + ‖ψ‖ :=
      (norm_add_le _ _).trans (by rw [norm_smul, norm_unitRoot, one_mul])
    have h2 := measureReal_le_norm_sq S (φ + unitRoot k • ψ) Δ.1
    have h3 : ‖φ + unitRoot k • ψ‖ ^ 2 ≤ (‖φ‖ + ‖ψ‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    norm_num
    linarith
  rw [polarMeasure_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => hterm k).trans (le_of_eq ?_))
  simp
theorem exists_norm_one_smul {x : H} (hx : x ≠ 0) :
    ∃ x' : H, ‖x'‖ = 1 ∧ x = ((‖x‖ : ℝ) : ℂ) • x' := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  refine ⟨((‖x‖⁻¹ : ℝ) : ℂ) • x, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn, Complex.ofReal_one, one_smul]
theorem norm_polarMeasure_le_mul (S : DiagonalData X M ϱ W) (Δ : BorelSubset m) (φ ψ : H) :
    ‖polarMeasure S φ ψ Δ‖ ≤ 4 * ‖φ‖ * ‖ψ‖ := by
  have hf := isSesquilinear_polarMeasure (H := H) S Δ
  by_cases hφ : φ = 0
  · have h := hf.smul_left 0 0 ψ
    simp only [zero_smul, map_zero, zero_mul] at h
    simp [hφ, h]
  by_cases hψ : ψ = 0
  · have h := hf.smul_right 0 φ 0
    simp only [zero_smul, zero_mul] at h
    simp [hψ, h]
  obtain ⟨φ', hφ', e1⟩ := exists_norm_one_smul hφ
  obtain ⟨ψ', hψ', e2⟩ := exists_norm_one_smul hψ
  have key : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      ‖polarMeasure S ((s : ℂ) • φ') ((t : ℂ) • ψ') Δ‖ ≤ 4 * s * t := by
    intro s t hs ht
    have h1 := hf.smul_left (s : ℂ) φ' ((t : ℂ) • ψ')
    have h2 := hf.smul_right (t : ℂ) φ' ψ'
    rw [h1, h2, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
    have h3 := norm_polarMeasure_le S φ' ψ' Δ
    rw [hφ', hψ'] at h3
    have h4 : ‖polarMeasure S φ' ψ' Δ‖ ≤ 4 := by linarith
    calc s * (t * ‖polarMeasure S φ' ψ' Δ‖) ≤ s * (t * 4) := by gcongr
      _ = 4 * s * t := by ring
  have h := key ‖φ‖ ‖ψ‖ (norm_nonneg _) (norm_nonneg _)
  rwa [← e1, ← e2] at h
theorem exists_operator_family (S : DiagonalData X M ϱ W) (hr : BoundedRepresentation.Claim) :
    ∃ E : BorelSubset m → H →L[ℂ] H, ∀ Δ φ ψ, ⟪φ, E Δ ψ⟫_ℂ = polarMeasure S φ ψ Δ := by
  have hform := (hr H 4 (by norm_num)).2.1
  have h : ∀ Δ : BorelSubset m, ∃ B : H →L[ℂ] H, ∀ φ ψ, ⟪φ, B ψ⟫_ℂ = polarMeasure S φ ψ Δ :=
    fun Δ => by
      obtain ⟨B, hB, -, -⟩ := hform (fun φ ψ => polarMeasure S φ ψ Δ)
        (isSesquilinear_polarMeasure S Δ) (norm_polarMeasure_le_mul S Δ)
      exact ⟨B, fun φ ψ => (hB φ ψ).symm⟩
  choose E hE using h
  exact ⟨E, hE⟩
theorem inner_operator_symm (S : DiagonalData X M ϱ W) {E : BorelSubset m → H →L[ℂ] H}
    (hE : ∀ Δ φ ψ, ⟪φ, E Δ ψ⟫_ℂ = polarMeasure S φ ψ Δ) (Δ : BorelSubset m) (φ ψ : H) :
    ⟪φ, E Δ ψ⟫_ℂ = ⟪E Δ φ, ψ⟫_ℂ := by
  rw [← inner_conj_symm (E Δ φ) ψ, hE, hE, conj_polarMeasure]
theorem polarMeasure_rep (S : DiagonalData X M ϱ W) (hc : WeightedMeasureTheorem)
    (hn : 1 ≤ m) (φ ψ : H) (u : M) :
    polarMeasure S φ (ϱ u ψ) = weightedBy u.1 (polarMeasure S φ ψ) := by
  have hu := S.isBounded u.1 u.2
  refine eq_of_complexIntegral_eq S.isBounded S.separates
    (isFiniteCombinationMeasure_polarMeasure S _ _)
    (isFiniteCombinationMeasure_weightedBy (isFiniteCombinationMeasure_polarMeasure S φ ψ) hu)
    (isSupportedOn_polarMeasure S _ _) ?_ fun u' hu' => ?_
  · exact (hc m hn _ (isFiniteCombinationMeasure_polarMeasure S φ ψ) X _ _ hu hu).2.2
      (isSupportedOn_polarMeasure S φ ψ)
  · have hb := S.isBounded u' hu'
    let w : M := ⟨fun y => u' y * u.1 y, S.starClosed.mul_mem u' hu' u.1 u.2⟩
    have hw : ϱ w = ϱ ⟨u', hu'⟩ * ϱ u := S.starHom.map_mul ⟨u', hu'⟩ u w rfl
    have h1 : complexIntegral (polarMeasure S φ ψ) (u' * u.1) = ⟪φ, ϱ w ψ⟫_ℂ :=
      complexIntegral_polarMeasure S φ ψ w
    rw [(hc m hn _ (isFiniteCombinationMeasure_polarMeasure S φ ψ) X u' u.1 hb hu).1, h1, hw]
    exact complexIntegral_polarMeasure S φ (ϱ u ψ) ⟨u', hu'⟩
theorem polarMeasure_operator_left (S : DiagonalData X M ϱ W) (hc : WeightedMeasureTheorem)
    (hn : 1 ≤ m) {E : BorelSubset m → H →L[ℂ] H}
    (hE : ∀ Δ φ ψ, ⟪φ, E Δ ψ⟫_ℂ = polarMeasure S φ ψ Δ) (Δ : BorelSubset m) (φ ψ : H) :
    polarMeasure S (E Δ φ) ψ = weightedBy (Δ.1.indicator 1) (polarMeasure S φ ψ) := by
  have h1 := isBoundedMeasurableFn_indicator (isBoundedMeasurableFn_one (m := m)) Δ
  refine eq_of_complexIntegral_eq S.isBounded S.separates
    (isFiniteCombinationMeasure_polarMeasure S _ _)
    (isFiniteCombinationMeasure_weightedBy (isFiniteCombinationMeasure_polarMeasure S φ ψ) h1)
    (isSupportedOn_polarMeasure S _ _) ?_ fun u hu => ?_
  · exact (hc m hn _ (isFiniteCombinationMeasure_polarMeasure S φ ψ) X _ _ h1 h1).2.2
      (isSupportedOn_polarMeasure S φ ψ)
  · have hb := S.isBounded u hu
    rw [(hc m hn _ (isFiniteCombinationMeasure_polarMeasure S φ ψ) X u _ hb h1).1]
    have h2 : complexIntegral (polarMeasure S (E Δ φ) ψ) u = ⟪E Δ φ, ϱ ⟨u, hu⟩ ψ⟫_ℂ :=
      complexIntegral_polarMeasure S _ ψ ⟨u, hu⟩
    have h3 : u * Δ.1.indicator 1 = Δ.1.indicator u := by
      funext y
      by_cases hy : y ∈ Δ.1 <;> simp [hy]
    rw [h2, ← inner_operator_symm S hE, hE, polarMeasure_rep S hc hn φ ψ ⟨u, hu⟩, h3]
    rfl
theorem operator_inter (S : DiagonalData X M ϱ W) (hc : WeightedMeasureTheorem) (hn : 1 ≤ m)
    {E : BorelSubset m → H →L[ℂ] H} (hE : ∀ Δ φ ψ, ⟪φ, E Δ ψ⟫_ℂ = polarMeasure S φ ψ Δ)
    (Δ Δ' : BorelSubset m) : E (Δ ∩ Δ') = E Δ * E Δ' := by
  ext ψ
  refine ext_inner_left ℂ fun φ => ?_
  have hset : (Δ ∩ Δ').1 = Δ.1 ∩ Δ'.1 := rfl
  have h1 : Δ'.1.indicator (Δ.1.indicator (1 : Space m → ℂ)) = (Δ ∩ Δ').1.indicator 1 := by
    funext y
    rw [hset]
    by_cases hy : y ∈ Δ.1 <;> by_cases hy' : y ∈ Δ'.1 <;> simp [hy, hy']
  rw [hE, mul_apply_eq_comp, inner_operator_symm S hE, hE (Δ') (E Δ φ) ψ,
    polarMeasure_operator_left S hc hn hE, weightedBy, h1,
    complexIntegral_indicator_one (isFiniteCombinationMeasure_polarMeasure S φ ψ)]
theorem isPVMRepresenting_of_polar (S : DiagonalData X M ϱ W) (hc : WeightedMeasureTheorem)
    (hi : BoundedBorelCalculusTheorem) (hr : BoundedRepresentation.Claim) (hn : 1 ≤ m)
    {E : BorelSubset m → H →L[ℂ] H} (hE : ∀ Δ φ ψ, ⟪φ, E Δ ψ⟫_ℂ = polarMeasure S φ ψ Δ) :
    IsPVMRepresenting X M ϱ E := by
  have hdiag := (hr H 0 le_rfl).2.2.1
  have hsc : ∀ (Δ : BorelSubset m) (ψ : H), ⟪ψ, E Δ ψ⟫_ℂ = (((W ψ).real Δ.1 : ℝ) : ℂ) := by
    intro Δ ψ
    rw [hE, polarMeasure_self]
    rfl
  have hP : IsPVM E :=
    { isOrthoProjection := fun Δ => by
        refine ⟨?_, inner_operator_symm S hE Δ⟩
        have hΔ : Δ ∩ Δ = Δ := Subtype.ext (Set.inter_self _)
        rw [← operator_inter S hc hn hE, hΔ]
      map_top := hdiag _ _ fun ψ => by
        rw [hsc]
        have h := measureReal_univ_eq_norm_sq S ψ
        have h1 : (⊤ : BorelSubset m).1 = Set.univ := rfl
        rw [h1, h, one_apply_eq_self, inner_self_eq_norm_sq_to_K]
        simp
      map_inter := operator_inter S hc hn hE
      isPositiveMeasure := fun ψ => ⟨W ψ, fun Δ => by
        have := S.isFinite ψ
        exact ⟨measure_ne_top _ _, hsc Δ ψ⟩⟩ }
  refine ⟨hP, ?_, fun u => ?_⟩
  · refine hdiag _ _ fun ψ => ?_
    have h0 : (((W ψ).real (Xᶜ : BorelSubset m).1 : ℝ) : ℂ) = 0 := S.supported ψ _ subset_rfl
    rw [hsc, h0]
    simp
  · obtain ⟨-, -, -, hU, -, hT⟩ := hi m hn H E hP
    have hb := S.isBounded u.1 u.2
    have hmix : IsCrossIntegralOperator E u.1 (ϱ u) := fun φ ψ => by
      have h : crossForm E φ ψ = polarMeasure S φ ψ := funext fun Δ => hE Δ φ ψ
      rw [h, complexIntegral_polarMeasure]
    have hop := (hU u.1 hb).2.1 _ hmix
    exact ⟨(hT.2 u.1 hb).1, fun ψ => by
      rw [spectralIntegral_eq_boundedCalculus hT hb ψ, hop]⟩
theorem boundedCalculus_eq_rep (S : DiagonalData X M ϱ W) (hi : BoundedBorelCalculusTheorem)
    (hn : 1 ≤ m) {E : BorelSubset m → H →L[ℂ] H} (hF : IsPVMRepresenting X M ϱ E) (u : M) :
    boundedCalculus E u.1 = ϱ u := by
  obtain ⟨-, -, -, -, -, hT⟩ := hi m hn H E hF.1
  have hb := S.isBounded u.1 u.2
  obtain ⟨hdom, hval⟩ := hF.2.2 u
  ext ψ
  have hψ : ψ ∈ sqIntegrableDomain E u.1 := by
    rw [hdom]
    trivial
  rw [← hval ⟨ψ, hψ⟩, spectralIntegral_eq_boundedCalculus hT hb ⟨ψ, hψ⟩]
theorem eq_zero_of_subset_compl {E : BorelSubset m → H →L[ℂ] H}
    (hF : IsPVMRepresenting X M ϱ E) {Δ : BorelSubset m} (h : Δ.1 ⊆ X.1ᶜ) : E Δ = 0 := by
  have hΔ : Δ = Δ ∩ Xᶜ := Subtype.ext (Set.inter_eq_left.2 h).symm
  have h0 : E Xᶜ = 0 := hF.2.1
  rw [hΔ, hF.1.map_inter, h0, mul_zero]
theorem diagonalForm_eq_diagValues (S : DiagonalData X M ϱ W) (hi : BoundedBorelCalculusTheorem)
    (hn : 1 ≤ m) {E : BorelSubset m → H →L[ℂ] H} (hF : IsPVMRepresenting X M ϱ E) (ψ : H) :
    diagonalForm E ψ = diagValues W ψ := by
  obtain ⟨-, -, -, hU, -, -⟩ := hi m hn H E hF.1
  have hspec := fun Δ => toMeasure_spec (hF.1.isPositiveMeasure ψ) Δ
  have hfin : IsFiniteMeasure (diagonalMeasure E ψ) := ⟨lt_top_iff_ne_top.2 (hspec ⊤).1⟩
  have hfun : diagonalForm E ψ = fun Δ => (((diagonalMeasure E ψ).real Δ.1 : ℝ) : ℂ) :=
    funext fun Δ => (hspec Δ).2
  have hcm := isFiniteCombinationMeasure_of_finite (diagonalMeasure E ψ) hfin
  refine eq_of_complexIntegral_eq S.isBounded S.separates (hfun ▸ hcm.1)
    (isFiniteCombinationMeasure_diagValues S ψ) ?_ (S.supported ψ) fun u hu => ?_
  · intro Δ hΔ
    show ⟪ψ, E Δ ψ⟫_ℂ = 0
    rw [eq_zero_of_subset_compl hF hΔ]
    simp
  · have hb := S.isBounded u hu
    refine Eq.trans ?_ (complexIntegral_diagValues S ψ ⟨u, hu⟩).symm
    rw [hfun, hcm.2 u hb, ← (hU u hb).2.2.1 ψ, boundedCalculus_eq_rep S hi hn hF ⟨u, hu⟩]
theorem eq_of_isPVMRepresenting (S : DiagonalData X M ϱ W) (hi : BoundedBorelCalculusTheorem)
    (hr : BoundedRepresentation.Claim) (hn : 1 ≤ m)
    {E E' : BorelSubset m → H →L[ℂ] H} (hF : IsPVMRepresenting X M ϱ E)
    (hF' : IsPVMRepresenting X M ϱ E') : E = E' := by
  funext Δ
  refine (hr H 0 le_rfl).2.2.1 _ _ fun ψ => ?_
  have h := congrFun ((diagonalForm_eq_diagValues S hi hn hF ψ).trans
    (diagonalForm_eq_diagValues S hi hn hF' ψ).symm) Δ
  exact h
theorem commute_of_commute_rep (S : DiagonalData X M ϱ W) (hi : BoundedBorelCalculusTheorem)
    (hn : 1 ≤ m) {E : BorelSubset m → H →L[ℂ] H} (hF : IsPVMRepresenting X M ϱ E)
    (B : H →L[ℂ] H) (hB : ∀ u : M, B * ϱ u = ϱ u * B) (Δ : BorelSubset m) :
    B * E Δ = E Δ * B := by
  obtain ⟨-, -, hM, hU, -, -⟩ := hi m hn H E hF.1
  have hint : ∀ (φ ψ : H) (u : M), complexIntegral (crossForm E φ ψ) u.1 = ⟪φ, ϱ u ψ⟫_ℂ := by
    intro φ ψ u
    rw [← (hU u.1 (S.isBounded u.1 u.2)).1 φ ψ, boundedCalculus_eq_rep S hi hn hF u]
  have hcar : ∀ φ ψ : H, IsSupportedOn (crossForm E φ ψ) X := by
    intro φ ψ Δ hΔ
    show ⟪φ, E Δ ψ⟫_ℂ = 0
    rw [eq_zero_of_subset_compl hF hΔ]
    simp
  ext ψ
  refine ext_inner_left ℂ fun φ => ?_
  have h : crossForm E φ (B ψ) = crossForm E (ContinuousLinearMap.adjoint B φ) ψ :=
    eq_of_complexIntegral_eq S.isBounded S.separates (hM.1 _ _) (hM.1 _ _) (hcar _ _) (hcar _ _)
      fun u hu => by
        refine (hint φ (B ψ) ⟨u, hu⟩).trans (Eq.trans ?_ (hint _ ψ ⟨u, hu⟩).symm)
        have h1 := congrArg (fun A : H →L[ℂ] H => A ψ) (hB ⟨u, hu⟩)
        simp only [mul_apply_eq_comp] at h1
        rw [← h1, ContinuousLinearMap.adjoint_inner_left]
  have h2 := congrFun h Δ
  show ⟪φ, B (E Δ ψ)⟫_ℂ = ⟪φ, E Δ (B ψ)⟫_ℂ
  have h3 : ⟪φ, E Δ (B ψ)⟫_ℂ = ⟪ContinuousLinearMap.adjoint B φ, E Δ ψ⟫_ℂ := h2
  rw [h3, ContinuousLinearMap.adjoint_inner_left]
end Diagonal
theorem pvmOfDiagonalMeasures (hc : WeightedMeasureTheorem) (hi : BoundedBorelCalculusTheorem)
    (hr : BoundedRepresentation.Claim) : PVMOfDiagonalMeasuresTheorem := by
  intro m hn H _ _ _ X M ϱ hb hstable hdet hstar hscalar
  choose W hfin hcar hdiag using hscalar
  have S : DiagonalData X M ϱ W := ⟨hb, hstable, hdet, hstar, hfin, hcar, hdiag⟩
  obtain ⟨E, hE⟩ := exists_operator_family S hr
  have hF := isPVMRepresenting_of_polar S hc hi hr hn hE
  exact ⟨⟨E, hF, fun E' hF' => eq_of_isPVMRepresenting S hi hr hn hF' hF⟩,
    fun E' hF' B hB Δ => commute_of_commute_rep S hi hn hF' B hB Δ⟩
end YangMills.Construction.EuclideanBorel.PVMConstruction
