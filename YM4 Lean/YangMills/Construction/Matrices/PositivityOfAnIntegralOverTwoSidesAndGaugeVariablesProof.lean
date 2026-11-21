import YangMills.Construction.Matrices.FiniteProductOfSpecialUnitary
import YangMills.Construction.Matrices.FunctionsAndOperatorsOfSeveralVariablesOnG
import YangMills.Construction.Matrices.PositivityOfAnIntegralOverTwoSidesAndGaugeVariables
import YangMills.Construction.ReflectionPositivity.ExponentialKernelPositivity
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.Matrices
open ComplexMatrix2
namespace TwoSidedGaugePositivity
theorem measurePreserving_pairToQuotient {P T : Type} [MeasurableSpace P] [MeasurableSpace T]
    [Group T] [MeasurableMul₂ T] [MeasurableInv T] (μ : Measure P) (ρ : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] [ρ.IsMulLeftInvariant] :
    MeasurePreserving (fun p : (P × T) × (P × T) => (p.1.1, p.2.1, p.2.2⁻¹ * p.1.2))
      ((μ.prod ρ).prod (μ.prod ρ)) (μ.prod (μ.prod ρ)) := by
  have hquot : MeasurePreserving (fun z : T × T => z.1⁻¹ * z.2) (ρ.prod ρ) ρ :=
    (measurePreserving_snd (μ := ρ) (ν := ρ)).comp (measurePreserving_prod_inv_mul ρ ρ)
  have hsecond : MeasurePreserving (fun q : T × (P × T) => (q.2.1, q.2.2⁻¹ * q.1))
      (ρ.prod (μ.prod ρ)) (μ.prod ρ) :=
    (((MeasurePreserving.id μ).prod hquot).comp (measurePreserving_prodAssoc μ ρ ρ)).comp
      (Measure.measurePreserving_swap (μ := ρ) (ν := μ.prod ρ))
  exact ((MeasurePreserving.id μ).prod hsecond).comp
    (measurePreserving_prodAssoc μ ρ (μ.prod ρ))
def bondConjugate {B S : Type} (c : B) (s s' : S) (x : (B → specialUnitary) × (S → specialUnitary)) :
    specialUnitary :=
  x.2 s * x.1 c * (x.2 s')⁻¹
theorem continuous_bondConjugate {B S : Type} (c : B) (s s' : S) :
    Continuous (bondConjugate c s s') := by
  unfold bondConjugate
  exact (((continuous_apply s).comp continuous_snd).mul
    ((continuous_apply c).comp continuous_fst)).mul
    ((continuous_apply s').comp continuous_snd).inv
theorem re_fullTrace_mul_inv (M M' : specialUnitary) :
    (fullTrace ((M * M'⁻¹ : specialUnitary) : ComplexMatrix2)).re =
      ∑ i, ∑ j, (((M : ComplexMatrix2) i j).re * ((M' : ComplexMatrix2) i j).re +
        ((M : ComplexMatrix2) i j).im * ((M' : ComplexMatrix2) i j).im) := by
  have hinv : ((M'⁻¹ : specialUnitary) : ComplexMatrix2) = star (M' : ComplexMatrix2) := rfl
  rw [Submonoid.coe_mul, hinv]
  simp only [fullTrace, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.add_re, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring
theorem fullTrace_gauge_eq (W W' a a' c c' : specialUnitary) :
    fullTrace ((W * (c'⁻¹ * a')⁻¹ * W'⁻¹ * (c⁻¹ * a) : specialUnitary) : ComplexMatrix2) =
      fullTrace (((a * W * a'⁻¹) * (c * W' * c'⁻¹)⁻¹ : specialUnitary) : ComplexMatrix2) := by
  have hleft : W * (c'⁻¹ * a')⁻¹ * W'⁻¹ * (c⁻¹ * a) = (W * a'⁻¹ * c' * W'⁻¹ * c⁻¹) * a := by
    group
  have hright : (a * W * a'⁻¹) * (c * W' * c'⁻¹)⁻¹ = a * (W * a'⁻¹ * c' * W'⁻¹ * c⁻¹) := by
    group
  rw [hleft, hright, Submonoid.coe_mul, Submonoid.coe_mul]
  exact Matrix.trace_mul_comm _ _
def scaledEntry {B S E : Type} (β : ℝ) (b : E → B) (y y' : E → S)
    (γ : E × Fin 2 × Fin 2 × Bool) (x : (B → specialUnitary) × (S → specialUnitary)) : ℝ :=
  Real.sqrt (β / 2) *
    (if γ.2.2.2 then
      ((bondConjugate (b γ.1) (y γ.1) (y' γ.1) x : specialUnitary) : ComplexMatrix2) γ.2.1 γ.2.2.1 |>.re
    else
      ((bondConjugate (b γ.1) (y γ.1) (y' γ.1) x : specialUnitary) : ComplexMatrix2) γ.2.1 γ.2.2.1 |>.im)
theorem measurable_scaledEntry {B S E : Type} [Finite B] [Finite S] (β : ℝ) (b : E → B)
    (y y' : E → S) (γ : E × Fin 2 × Fin 2 × Bool) : Measurable (scaledEntry β b y y' γ) := by
  have hentry : Continuous fun x : (B → specialUnitary) × (S → specialUnitary) =>
      ((bondConjugate (b γ.1) (y γ.1) (y' γ.1) x : specialUnitary) : ComplexMatrix2) γ.2.1 γ.2.2.1 :=
    Continuous.matrix_elem
      (continuous_subtype_val.comp (continuous_bondConjugate _ _ _)) _ _
  unfold scaledEntry
  by_cases h : γ.2.2.2 = true
  · simp only [h, if_true]
    exact ((Complex.continuous_re.comp hentry).measurable).const_mul _
  · simp only [h, if_false, Bool.false_eq_true]
    exact ((Complex.continuous_im.comp hentry).measurable).const_mul _
theorem abs_scaledEntry_le {B S E : Type} (β : ℝ) (b : E → B) (y y' : E → S)
    (γ : E × Fin 2 × Fin 2 × Bool) (x : (B → specialUnitary) × (S → specialUnitary)) :
    |scaledEntry β b y y' γ x| ≤ Real.sqrt (β / 2) := by
  have hentry : ‖((bondConjugate (b γ.1) (y γ.1) (y' γ.1) x : specialUnitary) : ComplexMatrix2)
      γ.2.1 γ.2.2.1‖ ≤ 1 :=
    entry_norm_bound_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup
      (bondConjugate (b γ.1) (y γ.1) (y' γ.1) x).2) _ _
  unfold scaledEntry
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_of_le_one_right (Real.sqrt_nonneg _) ?_
  by_cases h : γ.2.2.2 = true
  · simp only [h, if_true]
    exact (Complex.abs_re_le_norm _).trans hentry
  · simp only [h, if_false, Bool.false_eq_true]
    exact (Complex.abs_im_le_norm _).trans hentry
theorem sum_scaledEntry_mul {B S E : Type} [Fintype E] (β : ℝ) (hβ : 0 < β) (b : E → B)
    (y y' : E → S) (x x' : (B → specialUnitary) × (S → specialUnitary)) :
    ∑ γ, scaledEntry β b y y' γ x * scaledEntry β b y y' γ x' =
      (β / 2) * ∑ e, (fullTrace ((x.1 (b e) * ((x'.2⁻¹ * x.2) (y' e))⁻¹ * (x'.1 (b e))⁻¹ *
        (x'.2⁻¹ * x.2) (y e) : specialUnitary) : ComplexMatrix2)).re := by
  have hsq : Real.sqrt (β / 2) * Real.sqrt (β / 2) = β / 2 :=
    Real.mul_self_sqrt (by positivity)
  rw [Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Pi.mul_apply, Pi.inv_apply]
  rw [fullTrace_gauge_eq, re_fullTrace_mul_inv, Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [scaledEntry, bondConjugate, if_true, if_false, Bool.false_eq_true]
  generalize Real.sqrt (β / 2) = r at hsq ⊢
  rw [← hsq]
  ring
def boltzmannWeighted {B S : Type} (A : (B → specialUnitary) → ℝ) (β : ℝ)
    (F : (B → specialUnitary) → ℂ) (x : (B → specialUnitary) × (S → specialUnitary)) : ℂ :=
  F x.1 * (Real.exp (-β * A x.1) : ℂ)
theorem measurable_boltzmannWeighted {B S : Type} {A : (B → specialUnitary) → ℝ} (β : ℝ)
    {F : (B → specialUnitary) → ℂ} (hA : Measurable A) (hF : Measurable F) :
    Measurable (boltzmannWeighted (S := S) A β F) := by
  unfold boltzmannWeighted
  exact (hF.comp measurable_fst).mul (Complex.measurable_ofReal.comp
    (Real.measurable_exp.comp ((hA.comp measurable_fst).const_mul _)))
theorem norm_boltzmannWeighted_le {B S : Type} {A : (B → specialUnitary) → ℝ} {β : ℝ} (hβ : 0 < β)
    (hA : ∀ W, 0 ≤ A W) (F : (B → specialUnitary) → ℂ)
    (x : (B → specialUnitary) × (S → specialUnitary)) :
    ‖boltzmannWeighted A β F x‖ ≤ ‖F x.1‖ := by
  unfold boltzmannWeighted
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  rw [Real.exp_le_one_iff]
  nlinarith [hA x.1]
theorem measurable_gaugeExponent {B S E : Type} [Fintype B] [Fintype S] [Fintype E] (b : E → B)
    (y y' : E → S) {A : (B → specialUnitary) → ℝ} (hA : Measurable A) :
    Measurable (gaugeExponent b y y' A) := by
  unfold gaugeExponent
  refine ((hA.comp measurable_fst).add (hA.comp (measurable_fst.comp measurable_snd))).add ?_
  refine Finset.measurable_sum _ fun e _ => ?_
  have hcont : Continuous fun x : (B → specialUnitary) × (B → specialUnitary) × (S → specialUnitary) =>
      (x.1 (b e) * (x.2.2 (y' e))⁻¹ * (x.2.1 (b e))⁻¹ * x.2.2 (y e) : specialUnitary) :=
    ((((continuous_apply (b e)).comp continuous_fst).mul
      ((continuous_apply (y' e)).comp (continuous_snd.comp continuous_snd)).inv).mul
      ((continuous_apply (b e)).comp (continuous_fst.comp continuous_snd)).inv).mul
      ((continuous_apply (y e)).comp (continuous_snd.comp continuous_snd))
  have htr : Continuous fun x : (B → specialUnitary) × (B → specialUnitary) × (S → specialUnitary) =>
      (fullTrace ((x.1 (b e) * (x.2.2 (y' e))⁻¹ * (x.2.1 (b e))⁻¹ * x.2.2 (y e) : specialUnitary) :
        ComplexMatrix2)).re :=
    Complex.continuous_re.comp (Continuous.matrix_trace (continuous_subtype_val.comp hcont))
  exact (htr.measurable.const_mul _).const_sub _
theorem gaugeForm_eq_kernelForm {B S E : Type} [Fintype B] [Fintype S] [Fintype E] (b : E → B)
    (y y' : E → S) {A : (B → specialUnitary) → ℝ} {β : ℝ} (hβ : 0 < β) (hA : Measurable A)
    (hS : (haarPi S).IsMulLeftInvariant) {F' F : (B → specialUnitary) → ℂ}
    (hF' : Measurable F') (hF : Measurable F) :
    gaugeForm b y y' A β F' F = (Real.exp (-β * (Fintype.card E : ℝ)) : ℂ) *
      ReflectionPositivity.ExpSumProductKernel.kernelForm
        ((haarPi B).prod (haarPi S)) (scaledEntry β b y y')
        (boltzmannWeighted A β F') (boltzmannWeighted A β F) := by
  have hmp := measurePreserving_pairToQuotient (haarPi B) (haarPi S)
  have hint : Measurable fun x : (B → specialUnitary) × (B → specialUnitary) × (S → specialUnitary) =>
      starRingEnd ℂ (F' x.2.1) * F x.1 * (Real.exp (-β * gaugeExponent b y y' A x) : ℂ) :=
    ((Complex.continuous_conj.measurable.comp
      (hF'.comp (measurable_fst.comp measurable_snd))).mul (hF.comp measurable_fst)).mul
      (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
        ((measurable_gaugeExponent b y y' hA).const_mul _)))
  unfold gaugeForm ReflectionPositivity.ExpSumProductKernel.kernelForm
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    hint.aestronglyMeasurable, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  have hreal : Real.exp (-β * gaugeExponent b y y' A (p.1.1, p.2.1, p.2.2⁻¹ * p.1.2)) =
      Real.exp (-β * (Fintype.card E : ℝ)) * Real.exp (-β * A p.2.1) * Real.exp (-β * A p.1.1) *
        Real.exp (∑ γ, scaledEntry β b y y' γ p.1 * scaledEntry β b y y' γ p.2) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, sum_scaledEntry_mul β hβ]
    congr 1
    simp only [gaugeExponent, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, ← Finset.mul_sum]
    ring
  simp only [hreal, boltzmannWeighted, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  ring
theorem positivityStatement_holds
    (hkernel : ReflectionPositivity.ExpSumProductKernel.PositivityStatement)
    (hgroup : FiniteProductGroupStatement) :
    PositivityStatement := by
  intro B S E _ _ _ b y y' A β hβ hA hA₀ F F' hF hFb hF' hF'b
  have hS : (haarPi S).IsMulLeftInvariant := (hgroup.2.1 S).2.2.2.1
  obtain ⟨C, hC⟩ := hFb
  obtain ⟨C', hC'⟩ := hF'b
  have hres := hkernel ((B → specialUnitary) × (S → specialUnitary)) (E × Fin 2 × Fin 2 × Bool)
    ((haarPi B).prod (haarPi S)) (scaledEntry β b y y')
    (measurable_scaledEntry β b y y')
    (fun γ => ⟨_, abs_scaledEntry_le β b y y' γ⟩)
    (boltzmannWeighted A β F) (boltzmannWeighted A β F')
    (measurable_boltzmannWeighted β hA hF)
    ⟨C, fun x => (norm_boltzmannWeighted_le hβ hA₀ F x).trans (hC _)⟩
    (measurable_boltzmannWeighted β hA hF')
    ⟨C', fun x => (norm_boltzmannWeighted_le hβ hA₀ F' x).trans (hC' _)⟩
  set c : ℝ := Real.exp (-β * (Fintype.card E : ℝ)) with hc
  have c_pos : 0 < c := Real.exp_pos _
  have hsame := gaugeForm_eq_kernelForm b y y' hβ hA hS hF hF
  have hmixed := gaugeForm_eq_kernelForm b y y' hβ hA hS hF' hF
  have hother := gaugeForm_eq_kernelForm b y y' hβ hA hS hF' hF'
  rw [← hc] at hsame hmixed hother
  obtain ⟨hnonneg, hcauchy⟩ := hres
  refine ⟨?_, ?_⟩
  · rw [hsame]
    exact mul_nonneg (by exact_mod_cast c_pos.le) hnonneg
  · rw [hsame, hmixed, hother, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos c_pos,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, mul_pow]
    calc c ^ 2 * _ ≤ c ^ 2 * _ := mul_le_mul_of_nonneg_left hcauchy (by positivity)
      _ = _ := by ring
end TwoSidedGaugePositivity
end YangMills.Construction.Matrices
end
