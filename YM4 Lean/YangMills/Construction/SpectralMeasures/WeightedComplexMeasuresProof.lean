import YangMills.Construction.SpectralMeasures.ProjectionValuedMeasureFromScalarMeasuresProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section
namespace YangMills.Construction.EuclideanBorel
namespace WeightedMeasure
variable {n : ℕ}
theorem integrable_of_isBoundedMeasurableFn (μ : Measure (Space n)) [IsFiniteMeasure μ]
    {f : Space n → ℂ} (hf : IsBoundedMeasurableFn f) : Integrable f μ := by apply _root_.YangMills.Construction.EuclideanBorel.MeasureUniqueness.integrable_of_isBoundedMeasurableFn <;> assumption
theorem isBoundedMeasurableFn_mul {f g : Space n → ℂ} (hf : IsBoundedMeasurableFn f)
    (hg : IsBoundedMeasurableFn g) : IsBoundedMeasurableFn (f * g) := by apply _root_.YangMills.Construction.EuclideanBorel.PVMConstruction.isBoundedMeasurableFn_mul <;> assumption
theorem isBoundedMeasurableFn_indicator {f : Space n → ℂ} (hf : IsBoundedMeasurableFn f)
    (S : BorelSubset n) : IsBoundedMeasurableFn (S.1.indicator f) := by apply _root_.YangMills.Construction.EuclideanBorel.PVMConstruction.isBoundedMeasurableFn_indicator <;> assumption
theorem isBoundedMeasurableFn_one : IsBoundedMeasurableFn (1 : Space n → ℂ) :=
  ⟨measurable_const, 1, fun y => by simp⟩
theorem integral_eq_of_toSetFunction_eq {p q : MeasureCombination n}
    (h : p.toSetFunction = q.toSetFunction) {f : Space n → ℂ} (hf : IsBoundedMeasurableFn f) :
    p.integral f = q.integral f := by apply _root_.YangMills.Construction.EuclideanBorel.BoundedCalculusProof.combination_integral_unique <;> assumption
theorem complexIntegral_toSetFunction (p : MeasureCombination n) {f : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) : complexIntegral p.toSetFunction f = p.integral f := by apply _root_.YangMills.Construction.EuclideanBorel.PVMConstruction.complexIntegral_toSetFunction <;> assumption
theorem toSetFunction_eq_integral_indicator (p : MeasureCombination n) (S : BorelSubset n) :
    p.toSetFunction S = p.integral (S.1.indicator 1) := by apply _root_.YangMills.Construction.EuclideanBorel.PVMConstruction.toSetFunction_eq_integral_indicator <;> assumption
def ofFintype {ι : Type} [Fintype ι] [Nonempty ι] (c : ι → ℂ) (m : ι → Measure (Space n))
    (hm : ∀ i, IsFiniteMeasure (m i)) : MeasureCombination n where
  numTerms := Fintype.card ι
  one_le_numTerms := Fintype.card_pos
  coeff := c ∘ (Fintype.equivFin ι).symm
  component := m ∘ (Fintype.equivFin ι).symm
  isFinite := fun _ => hm _
theorem integral_ofFintype {ι : Type} [Fintype ι] [Nonempty ι] (c : ι → ℂ)
    (m : ι → Measure (Space n)) (hm : ∀ i, IsFiniteMeasure (m i)) (f : Space n → ℂ) :
    (ofFintype c m hm).integral f = ∑ i, c i * ∫ y, f y ∂(m i) :=
  (Fintype.equivFin ι).symm.sum_comp fun i => c i * ∫ y, f y ∂(m i)
def nonnegPart (g : Space n → ℂ) : Fin 4 → Space n → ℝ≥0 :=
  ![fun y => Real.toNNReal (g y).re, fun y => Real.toNNReal (-(g y).re),
    fun y => Real.toNNReal (g y).im, fun y => Real.toNNReal (-(g y).im)]
def partCoeff : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]
theorem isFiniteMeasure_withDensity_nonnegPart (μ : Measure (Space n)) [IsFiniteMeasure μ]
    {g : Space n → ℂ} (hg : IsBoundedMeasurableFn g) (k : Fin 4) :
    IsFiniteMeasure (μ.withDensity fun y => (nonnegPart g k y : ℝ≥0∞)) := by apply _root_.YangMills.Construction.EuclideanBorel.PVMConstruction.isFiniteMeasure_withDensity_signPart <;> assumption
theorem sum_integral_withDensity_nonnegPart (μ : Measure (Space n)) [IsFiniteMeasure μ]
    {g F : Space n → ℂ} (hg : IsBoundedMeasurableFn g) (hF : IsBoundedMeasurableFn F) :
    ∑ k, partCoeff k * ∫ y, F y ∂(μ.withDensity fun y => (nonnegPart g k y : ℝ≥0∞)) =
      ∫ y, (F * g) y ∂μ := by apply _root_.YangMills.Construction.EuclideanBorel.PVMConstruction.sum_integral_withDensity_signPart <;> assumption
def weightedComb (p : MeasureCombination n) {g : Space n → ℂ}
    (hg : IsBoundedMeasurableFn g) : MeasureCombination n :=
  have : Nonempty (Fin p.numTerms) := ⟨⟨0, p.one_le_numTerms⟩⟩
  ofFintype (ι := Fin p.numTerms × Fin 4) (fun i => p.coeff i.1 * partCoeff i.2)
    (fun i => (p.component i.1).withDensity fun y => (nonnegPart g i.2 y : ℝ≥0∞))
    (fun i => by
      have := p.isFinite i.1
      exact isFiniteMeasure_withDensity_nonnegPart _ hg i.2)
theorem integral_weightedComb (p : MeasureCombination n) {g F : Space n → ℂ}
    (hg : IsBoundedMeasurableFn g) (hF : IsBoundedMeasurableFn F) :
    (weightedComb p hg).integral F = p.integral (F * g) := by
  have : Nonempty (Fin p.numTerms) := ⟨⟨0, p.one_le_numTerms⟩⟩
  rw [weightedComb, integral_ofFintype, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := p.isFinite j
  rw [← sum_integral_withDensity_nonnegPart (p.component j) hg hF, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring
theorem toSetFunction_weightedComb (p : MeasureCombination n) {g : Space n → ℂ}
    (hg : IsBoundedMeasurableFn g) :
    (weightedComb p hg).toSetFunction = weightedBy g p.toSetFunction := by
  funext S
  rw [toSetFunction_eq_integral_indicator,
    integral_weightedComb p hg (isBoundedMeasurableFn_indicator isBoundedMeasurableFn_one S),
    weightedBy, complexIntegral_toSetFunction p (isBoundedMeasurableFn_indicator hg S)]
  congr 1
  funext y
  by_cases hy : y ∈ S.1 <;> simp [hy]
def restrictTo (p : MeasureCombination n) (Y : BorelSubset n) : MeasureCombination n where
  numTerms := p.numTerms
  one_le_numTerms := p.one_le_numTerms
  coeff := p.coeff
  component := fun j => (p.component j).restrict Y.1
  isFinite := fun j => by
    have := p.isFinite j
    infer_instance
def zeroComb : MeasureCombination n where
  numTerms := 1
  one_le_numTerms := le_rfl
  coeff := fun _ => 0
  component := fun _ => 0
  isFinite := fun _ => inferInstance
theorem complexIntegral_eq_mul_indicator_of_supported (p : MeasureCombination n)
    (X : BorelSubset n) {f : Space n → ℂ} (hf : IsBoundedMeasurableFn f)
    (hX : IsSupportedOn p.toSetFunction X) :
    complexIntegral p.toSetFunction f = complexIntegral p.toSetFunction (f * X.1.indicator 1) := by
  let Y : BorelSubset n := ⟨X.1ᶜ, X.2.compl⟩
  have hzero : (restrictTo p Y).toSetFunction = (zeroComb : MeasureCombination n).toSetFunction := by
    funext S
    have h1 : (restrictTo p Y).toSetFunction S = p.toSetFunction ⟨S.1 ∩ Y.1, S.2.inter Y.2⟩ := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [restrictTo, measureReal_restrict_apply S.2]
    rw [h1, hX _ Set.inter_subset_right]
    simp [zeroComb, MeasureCombination.toSetFunction]
  have hint : (restrictTo p Y).integral f = 0 := by
    rw [integral_eq_of_toSetFunction_eq hzero hf]
    simp [zeroComb, MeasureCombination.integral]
  have hg : IsBoundedMeasurableFn (f * X.1.indicator 1) :=
    isBoundedMeasurableFn_mul hf (isBoundedMeasurableFn_indicator isBoundedMeasurableFn_one X)
  rw [complexIntegral_toSetFunction p hf, complexIntegral_toSetFunction p hg]
  have hsplit : p.integral f = p.integral (f * X.1.indicator 1) + (restrictTo p Y).integral f := by
    show ∑ j, p.coeff j * ∫ y, f y ∂(p.component j) =
      ∑ j, p.coeff j * ∫ y, (f * X.1.indicator 1 : Space n → ℂ) y ∂(p.component j) +
        ∑ j, p.coeff j * ∫ y, f y ∂((p.component j).restrict Y.1)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := p.isFinite j
    rw [← mul_add]
    congr 1
    have hind : (f * X.1.indicator 1) = X.1.indicator f := by
      funext y
      by_cases hy : y ∈ X.1 <;> simp [hy]
    rw [hind, integral_indicator X.2]
    exact (integral_add_compl X.2 (integrable_of_isBoundedMeasurableFn _ hf)).symm
  rw [hsplit, hint, add_zero]
end WeightedMeasure
open WeightedMeasure in
theorem weightedMeasureTheorem_proof : WeightedMeasureTheorem := by
  intro n _ ν hν X f g hf hg
  obtain ⟨p, rfl⟩ := hν
  have hfg : IsBoundedMeasurableFn (f * g) := isBoundedMeasurableFn_mul hf hg
  refine ⟨?_, fun hX => complexIntegral_eq_mul_indicator_of_supported p X hf hX,
    fun hX S hS => ?_⟩
  · rw [← toSetFunction_weightedComb p hg, complexIntegral_toSetFunction _ hf,
      integral_weightedComb p hg hf, complexIntegral_toSetFunction p hfg]
  · have hb := isBoundedMeasurableFn_indicator hg S
    have h0 : S.1.indicator g * X.1.indicator 1 = 0 := by
      funext y
      by_cases hy : y ∈ X.1
      · have hn : y ∉ S.1 := fun h => hS h hy
        simp [hn]
      · simp [hy]
    rw [weightedBy, complexIntegral_eq_mul_indicator_of_supported p X hb hX, h0,
      complexIntegral_toSetFunction p (f := 0) ⟨measurable_const, 0, by simp⟩]
    simp [MeasureCombination.integral]
end YangMills.Construction.EuclideanBorel
