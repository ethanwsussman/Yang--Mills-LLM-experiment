import YangMills.Construction.ReflectionPositivity.FromFivePointInequalitiesAtSmallTimesToTheCone
import YangMills.Construction.SpectralTheory.SpectralIntegralLaws
import YangMills.Construction.SpectralTheory.SpectralMeasureConcentratedOnSupport
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace ENNReal ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.SmallTimeCone
open YangMills.Construction.ReflectionPositivity.TupleForm YangMills.Construction.SpectralTheory YangMills.Construction.ReflectionPositivity.ContractionFunctionals YangMills.Construction.ReflectionPositivity.PairMeasureOperators YangMills.Construction.ReflectionPositivity.ShiftSpectralMeasure
open YangMills.Construction.SeparatedTuples (TupleFunctional)
open YangMills.Construction.ReflectionPositivity.Reconstruction (PhysicalSpace fivePointCombination
  timeShift spaceShift spatialBasisVec embedSpatial timeBasisVec posClass SemigroupProperties
  SpatialProperties MatrixElementFormula)
open YangMills.Construction.HilbertSpaceBasics (IsPosSemidef ofBounded)
def fivePointSymbol (t : ℝ) (y : Fin 2 → ℝ) : ℝ :=
  if 0 ≤ y 0 then
    (1 - Real.exp (-t * y 0)) ^ 2 - 2 * Real.exp (-t * y 0) * (1 - Real.cos (t * y 1))
  else 0
theorem abs_le_of_fivePointSymbol_nonneg (E q : ℝ) (hE : 0 ≤ E) (t : ℕ → ℝ) (ht : ∀ k, 0 < t k)
    (hlim : Tendsto t atTop (𝓝 0))
    (hg : ∀ k, 0 ≤ (1 - Real.exp (-t k * E)) ^ 2 -
      2 * Real.exp (-t k * E) * (1 - Real.cos (t k * q))) : |q| ≤ E := by
  have hne : Tendsto t atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun k => (ht k).ne'⟩
  have ha : HasDerivAt (fun s : ℝ => 1 - Real.exp (-s * E)) E 0 := by
    have h1 : HasDerivAt (fun s : ℝ => -s * E) (-E) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).neg.mul_const E
    simpa using h1.exp.const_sub 1
  have hb : HasDerivAt (fun s : ℝ => Real.sin (s * (q / 2))) (q / 2) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s * (q / 2)) (q / 2) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (q / 2)
    simpa using h1.sin
  have hA : Tendsto (fun k => (t k)⁻¹ * (1 - Real.exp (-t k * E))) atTop (𝓝 E) := by
    refine (ha.tendsto_slope_zero.comp hne).congr fun k => ?_
    simp
  have hB : Tendsto (fun k => (t k)⁻¹ * Real.sin (t k * (q / 2))) atTop (𝓝 (q / 2)) := by
    refine (hb.tendsto_slope_zero.comp hne).congr fun k => ?_
    simp
  have he : Tendsto (fun k => Real.exp (-t k * E)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun k => -t k * E) atTop (𝓝 0) := by
      simpa using (hlim.neg).mul_const E
    have h2 := (Real.continuous_exp.tendsto 0).comp h1
    rw [Real.exp_zero] at h2
    exact h2
  have hle : ∀ k, 4 * Real.exp (-t k * E) * ((t k)⁻¹ * Real.sin (t k * (q / 2))) ^ 2 ≤
      ((t k)⁻¹ * (1 - Real.exp (-t k * E))) ^ 2 := by
    intro k
    have hc : Real.cos (t k * q) = 1 - 2 * Real.sin (t k * (q / 2)) ^ 2 := by
      rw [show t k * q = 2 * (t k * (q / 2)) by ring, Real.cos_two_mul, Real.cos_sq']
      ring
    have h := hg k
    rw [hc] at h
    have hi : 0 ≤ ((t k)⁻¹) ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_left (sub_nonneg.mp h) hi
    nlinarith [this]
  have hlimle : 4 * 1 * (q / 2) ^ 2 ≤ E ^ 2 :=
    le_of_tendsto_of_tendsto' ((he.const_mul 4).mul (hB.pow 2)) (hA.pow 2) hle
  have hsq : q ^ 2 ≤ E ^ 2 := by nlinarith [hlimle]
  exact abs_le_of_sq_le_sq hsq hE
theorem measurable_fivePointSymbol (t : ℝ) : Measurable (fivePointSymbol t) := by
  refine Measurable.ite (measurableSet_le measurable_const (measurable_pi_apply 0)) ?_
    measurable_const
  fun_prop
section Spectral
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
theorem apply_eq_of_eq_ofBounded {S : UnboundedOperator ℋ} {B : ℋ →L[ℂ] ℋ} (h : S = ofBounded B)
    (ψ : S.domain) : S ψ = B ψ := by
  subst h
  rfl
def heatCharacter (t u : ℝ) : (Fin 2 → ℝ) → ℂ :=
  extendByZero energyMomentumRegion fun y =>
    Complex.exp (((-t * y.1 0 : ℝ) : ℂ) + Complex.I * ((u * y.1 1 : ℝ) : ℂ))
theorem heatCharacter_of_nonneg (t u : ℝ) {y : Fin 2 → ℝ} (hy : 0 ≤ y 0) :
    heatCharacter t u y = Complex.exp (((-t * y 0 : ℝ) : ℂ) + Complex.I * ((u * y 1 : ℝ) : ℂ)) :=
  extendByZero_apply_of_mem energyMomentumRegion _ ⟨y, hy⟩
theorem heatCharacter_of_neg (t u : ℝ) {y : Fin 2 → ℝ} (hy : y 0 < 0) : heatCharacter t u y = 0 :=
  extendByZero_apply_of_not_mem energyMomentumRegion _ (not_le.mpr hy)
theorem measurable_heatCharacter (t u : ℝ) : Measurable (heatCharacter t u) := by
  have h0 : Continuous fun y : energyMomentumRegion.1 => y.1 0 :=
    (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous fun y : energyMomentumRegion.1 => y.1 1 :=
    (continuous_apply 1).comp continuous_subtype_val
  exact measurable_extendByZero energyMomentumRegion (Continuous.measurable
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_const.mul h0)).add
      (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul h1))))))
theorem norm_heatCharacter_le {t : ℝ} (ht : 0 ≤ t) (u : ℝ) (y : Fin 2 → ℝ) :
    ‖heatCharacter t u y‖ ≤ 1 := by
  rcases le_or_gt 0 (y 0) with hy | hy
  · rw [heatCharacter_of_nonneg t u hy, Complex.norm_exp]
    have hre : (((-t * y 0 : ℝ) : ℂ) + Complex.I * ((u * y 1 : ℝ) : ℂ)).re = -t * y 0 := by
      simp
    rw [hre, Real.exp_le_one_iff]
    nlinarith [mul_nonneg ht hy]
  · rw [heatCharacter_of_neg t u hy]
    simp
theorem fivePointSymbol_eq_heatCharacter (t : ℝ) (y : Fin 2 → ℝ) :
    ((fivePointSymbol t y : ℝ) : ℂ) = heatCharacter 0 0 y - 4 * heatCharacter t 0 y +
      heatCharacter (2 * t) 0 y + heatCharacter t t y + heatCharacter t (-t) y := by
  rcases le_or_gt 0 (y 0) with hy | hy
  · simp only [heatCharacter_of_nonneg _ _ hy, fivePointSymbol, if_pos hy]
    have e0 : Complex.exp (((-(0 : ℝ) * y 0 : ℝ) : ℂ) + Complex.I * (((0 : ℝ) * y 1 : ℝ) : ℂ)) = 1 := by
      simp
    have e1 : Complex.exp (((-t * y 0 : ℝ) : ℂ) + Complex.I * (((0 : ℝ) * y 1 : ℝ) : ℂ)) =
        ((Real.exp (-t * y 0) : ℝ) : ℂ) := by
      simp [Complex.ofReal_exp]
    have e2 : Complex.exp (((-(2 * t) * y 0 : ℝ) : ℂ) + Complex.I * (((0 : ℝ) * y 1 : ℝ) : ℂ)) =
        ((Real.exp (-t * y 0) : ℝ) : ℂ) ^ 2 := by
      rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have e3 : Complex.exp (((-t * y 0 : ℝ) : ℂ) + Complex.I * ((t * y 1 : ℝ) : ℂ)) +
        Complex.exp (((-t * y 0 : ℝ) : ℂ) + Complex.I * ((-t * y 1 : ℝ) : ℂ)) =
        ((Real.exp (-t * y 0) : ℝ) : ℂ) * (2 * ((Real.cos (t * y 1) : ℝ) : ℂ)) := by
      have hm : ((-t * y 1 : ℝ) : ℂ) = -((t * y 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hm, Complex.exp_add, Complex.exp_add, Complex.ofReal_exp, mul_comm Complex.I,
        mul_comm Complex.I (-_), Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg,
        Complex.sin_neg, Complex.ofReal_cos]
      push_cast
      ring
    rw [e0, e1, e2, add_assoc, e3]
    push_cast
    ring
  · simp [heatCharacter_of_neg _ _ hy, fivePointSymbol, not_le.mpr hy]
variable (E : ProjectionMeasure 2 ℋ)
theorem isBoundedComplexFn_fivePointSymbol {t : ℝ} (ht : 0 ≤ t) :
    IsBoundedComplexFn fun y => ((fivePointSymbol t y : ℝ) : ℂ) := by
  refine ⟨8, fun y => ?_⟩
  change ‖((fivePointSymbol t y : ℝ) : ℂ)‖ ≤ 8
  rw [fivePointSymbol_eq_heatCharacter]
  have h0 := norm_heatCharacter_le le_rfl 0 y
  have h1 := norm_heatCharacter_le ht 0 y
  have h2 := norm_heatCharacter_le (mul_nonneg zero_le_two ht) 0 y
  have h3 := norm_heatCharacter_le ht t y
  have h4 := norm_heatCharacter_le ht (-t) y
  have a1 := norm_add_le (heatCharacter 0 0 y - 4 * heatCharacter t 0 y +
    heatCharacter (2 * t) 0 y + heatCharacter t t y) (heatCharacter t (-t) y)
  have a2 := norm_add_le (heatCharacter 0 0 y - 4 * heatCharacter t 0 y +
    heatCharacter (2 * t) 0 y) (heatCharacter t t y)
  have a3 := norm_add_le (heatCharacter 0 0 y - 4 * heatCharacter t 0 y) (heatCharacter (2 * t) 0 y)
  have a4 := norm_sub_le (heatCharacter 0 0 y) (4 * heatCharacter t 0 y)
  have a5 : ‖(4 : ℂ) * heatCharacter t 0 y‖ = 4 * ‖heatCharacter t 0 y‖ := by simp
  linarith
theorem inner_apply_eq_integral (R : E.CalculusLaws) {f : (Fin 2 → ℝ) → ℂ} (hf : Measurable f)
    {T : ℋ →L[ℂ] ℋ} (hT : ofBounded T = E.functionalCalculus f) (ψ : ℋ) :
    ⟪ψ, T ψ⟫_ℂ = ∫ y, f y ∂(E.spectralValueMeasure ψ) := by
  have hm : ψ ∈ (E.functionalCalculus f).domain := by
    rw [← hT]
    exact Submodule.mem_top
  have h1 := R.inner_self f hf ⟨ψ, hm⟩
  rw [apply_eq_of_eq_ofBounded hT.symm ⟨ψ, hm⟩] at h1
  exact h1
theorem isNullOn_fivePointSymbol_neg (R : E.CalculusLaws)
    (hfin : ∀ ψ, IsFiniteMeasure (E.spectralValueMeasure ψ)) {t : ℝ} (ht : 0 ≤ t)
    (hpos : ∀ ψ, 0 ≤ ∫ y, heatCharacter 0 0 y ∂(E.spectralValueMeasure ψ) -
      4 * ∫ y, heatCharacter t 0 y ∂(E.spectralValueMeasure ψ) +
      ∫ y, heatCharacter (2 * t) 0 y ∂(E.spectralValueMeasure ψ) +
      ∫ y, heatCharacter t t y ∂(E.spectralValueMeasure ψ) +
      ∫ y, heatCharacter t (-t) y ∂(E.spectralValueMeasure ψ)) :
    E.VanishesOn ⟨{y | fivePointSymbol t y < 0},
      measurableSet_lt (measurable_fivePointSymbol t) measurable_const⟩ := by
  have hf : Measurable fun y => ((fivePointSymbol t y : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_fivePointSymbol t)
  have hb := isBoundedComplexFn_fivePointSymbol ht
  have hint : ∀ (ψ : ℋ) (s u : ℝ), 0 ≤ s →
      Integrable (heatCharacter s u) (E.spectralValueMeasure ψ) := fun ψ s u hs => by
    have := hfin ψ
    exact Integrable.of_bound (measurable_heatCharacter s u).aestronglyMeasurable 1
      (ae_of_all _ (norm_heatCharacter_le hs u))
  have hge : LoewnerGe (E.boundedCalculus fun y => ((fivePointSymbol t y : ℝ) : ℂ)) 0 := by
    intro ψ
    have hd := inner_apply_eq_integral E R hf
      (T := E.boundedCalculus fun y => ((fivePointSymbol t y : ℝ) : ℂ))
      (R.isBoundedCalculusOf _ hf hb).symm ψ
    have hsum : ∫ y, ((fivePointSymbol t y : ℝ) : ℂ) ∂(E.spectralValueMeasure ψ) =
        ∫ y, heatCharacter 0 0 y ∂(E.spectralValueMeasure ψ) -
        4 * ∫ y, heatCharacter t 0 y ∂(E.spectralValueMeasure ψ) +
        ∫ y, heatCharacter (2 * t) 0 y ∂(E.spectralValueMeasure ψ) +
        ∫ y, heatCharacter t t y ∂(E.spectralValueMeasure ψ) +
        ∫ y, heatCharacter t (-t) y ∂(E.spectralValueMeasure ψ) := by
      have i0 := hint ψ 0 0 le_rfl
      have i1 := hint ψ t 0 ht
      have i2 := hint ψ (2 * t) 0 (mul_nonneg zero_le_two ht)
      have i3 := hint ψ t t ht
      have i4 := hint ψ t (-t) ht
      simp only [fivePointSymbol_eq_heatCharacter]
      rw [integral_add, integral_add, integral_add, integral_sub, integral_const_mul]
      · exact i0
      · exact i1.const_mul 4
      · exact i0.sub (i1.const_mul 4)
      · exact i2
      · exact (i0.sub (i1.const_mul 4)).add i2
      · exact i3
      · exact ((i0.sub (i1.const_mul 4)).add i2).add i3
      · exact i4
    simp only [sub_zero]
    rw [hd, hsum]
    exact hpos ψ
  have hz := (R.loewnerGe_zero_iff _ hf (fun y => Complex.ofReal_im _) hb).mp hge
  have hset : (⟨{y | fivePointSymbol t y < 0},
      measurableSet_lt (measurable_fivePointSymbol t) measurable_const⟩ : BorelSets 2) =
      ⟨{y | (((fivePointSymbol t y : ℝ) : ℂ)).re < 0},
        measurableSet_lt (Complex.measurable_re.comp hf) measurable_const⟩ :=
    Subtype.ext (by ext y; simp)
  rw [ProjectionMeasure.VanishesOn, hset]
  exact hz
theorem isClosed_forwardCone : IsClosed QuantumSystem.forwardCone :=
  isClosed_le (by fun_prop) (by fun_prop)
theorem compl_forwardCone_eq_zero (Sp : E.SupportLaws) (hY : E.IsConcentratedOn energyMomentumRegion)
    (t : ℕ → ℝ) (ht : ∀ k, 0 < t k) (hlim : Tendsto t atTop (𝓝 0))
    (hv : ∀ k, E.VanishesOn ⟨{y | fivePointSymbol (t k) y < 0},
      measurableSet_lt (measurable_fivePointSymbol (t k)) measurable_const⟩) :
    E ⟨QuantumSystem.forwardConeᶜ, isClosed_forwardCone.isOpen_compl.measurableSet⟩ = 0 := by
  let A : Option ℕ → BorelSets 2 := fun o => o.elim
    ⟨energyMomentumRegion.1ᶜ, energyMomentumRegion.2.compl⟩
    fun k => ⟨{y | fivePointSymbol (t k) y < 0},
      measurableSet_lt (measurable_fivePointSymbol (t k)) measurable_const⟩
  have hU := Sp.vanishesOn_iUnion (Option ℕ) A (by
    rintro (_ | k)
    · exact hY
    · exact hv k)
  refine Sp.vanishesOn_of_subset _ _ (fun y hy => ?_) hU
  by_contra hn
  have hn' : ∀ o, y ∉ (A o).1 := fun o ho => hn (mem_iUnion.mpr ⟨o, ho⟩)
  have h0 : 0 ≤ y 0 := by
    by_contra h
    exact hn' none h
  refine hy (abs_le_of_fivePointSymbol_nonneg (y 0) (y 1) h0 t ht hlim fun k => ?_)
  have h1 := hn' (some k)
  have h2 : ¬ fivePointSymbol (t k) y < 0 := h1
  simpa [fivePointSymbol, h0] using h2
variable {E}
theorem ae_mem_forwardCone
    (hC : E ⟨QuantumSystem.forwardConeᶜ, isClosed_forwardCone.isOpen_compl.measurableSet⟩ = 0)
    (ψ : ℋ) : ∀ᵐ y ∂(E.spectralValueMeasure ψ), y ∈ QuantumSystem.forwardCone := by
  have h := E.spectralValueMeasure_apply ψ
    ⟨QuantumSystem.forwardConeᶜ, isClosed_forwardCone.isOpen_compl.measurableSet⟩
  rw [hC] at h
  rw [ae_iff]
  change E.spectralValueMeasure ψ QuantumSystem.forwardConeᶜ = 0
  simpa using h
theorem integrable_of_mem_functionalDomain (hfin : ∀ ψ, IsFiniteMeasure (E.spectralValueMeasure ψ))
    {f : (Fin 2 → ℝ) → ℂ} (hf : Measurable f) {ψ : ℋ} (hψ : ψ ∈ functionalDomain E f) :
    Integrable f (E.spectralValueMeasure ψ) := by
  have := hfin ψ
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have hle : ∀ x : ℝ≥0∞, x ≤ 1 + x ^ 2 := fun x => by
    rcases le_total x 1 with h | h
    · exact h.trans le_self_add
    · calc x = x * 1 := (mul_one x).symm
        _ ≤ x * x := mul_le_mul_right h x
        _ = x ^ 2 := (sq x).symm
        _ ≤ 1 + x ^ 2 := le_add_self
  calc ∫⁻ y, ‖f y‖ₑ ∂(E.spectralValueMeasure ψ)
        ≤ ∫⁻ y, (1 + ‖f y‖ₑ ^ 2) ∂(E.spectralValueMeasure ψ) :=
        lintegral_mono fun y => hle _
    _ = ∫⁻ _, 1 ∂(E.spectralValueMeasure ψ) + ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) :=
        lintegral_add_left measurable_const _
    _ < ∞ := by
        refine ENNReal.add_lt_top.mpr ⟨?_, hψ⟩
        simp
theorem integrable_sq_of_mem_functionalDomain {f : (Fin 2 → ℝ) → ℂ} (hf : Measurable f) {ψ : ℋ}
    (hψ : ψ ∈ functionalDomain E f) :
    Integrable (fun y => ‖f y‖ ^ 2) (E.spectralValueMeasure ψ) := by
  refine ⟨(hf.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  have heq : ∀ y, ‖‖f y‖ ^ 2‖ₑ = ‖f y‖ₑ ^ 2 := fun y => by
    rw [enorm_pow, enorm_norm]
  simp only [HasFiniteIntegral, heq]
  exact hψ
theorem domain_energy_le_domain_momentum (R : E.CalculusLaws)
    (hC : E ⟨QuantumSystem.forwardConeᶜ, isClosed_forwardCone.isOpen_compl.measurableSet⟩ = 0) :
    (E.functionalCalculus (coordFun 0)).domain ≤ (E.functionalCalculus (coordFun 1)).domain := by
  intro ψ hψ
  have h0 : ψ ∈ functionalDomain E (coordFun 0) := by
    rw [← (R.isOperator _ (measurable_coordFun 0)).1]
    exact hψ
  have h1 : ψ ∈ functionalDomain E (coordFun 1) := by
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) h0
    filter_upwards [ae_mem_forwardCone hC ψ] with y hy
    have hy' : |y 1| ≤ y 0 := hy
    have hn : ‖coordFun 1 y‖ₑ ≤ ‖coordFun 0 y‖ₑ := by
      refine enorm_le_iff_norm_le.mpr ?_
      simp only [coordFun, Complex.norm_real, Real.norm_eq_abs]
      exact hy'.trans (le_abs_self _)
    gcongr
  have := (R.isOperator _ (measurable_coordFun 1)).1
  change ψ ∈ ((E.functionalCalculus (coordFun 1)).domain : Set ℋ)
  rw [this]
  exact h1
theorem inner_abs_momentum_le_inner_energy (R : E.CalculusLaws)
    (hfin : ∀ ψ, IsFiniteMeasure (E.spectralValueMeasure ψ))
    (hC : E ⟨QuantumSystem.forwardConeᶜ, isClosed_forwardCone.isOpen_compl.measurableSet⟩ = 0)
    (ψ : (E.functionalCalculus (coordFun 0)).domain) :
    ∃ hψ : (ψ : ℋ) ∈ (E.functionalCalculus fun y => ((|y 1| : ℝ) : ℂ)).domain,
      ⟪(ψ : ℋ), E.functionalCalculus (fun y => ((|y 1| : ℝ) : ℂ)) ⟨ψ, hψ⟩⟫_ℂ ≤
        ⟪(ψ : ℋ), E.functionalCalculus (coordFun 0) ψ⟫_ℂ := by
  have hg : Measurable fun y : Fin 2 → ℝ => ((|y 1| : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (by fun_prop)
  have h1 : (ψ : ℋ) ∈ functionalDomain E (coordFun 1) := by
    rw [← (R.isOperator _ (measurable_coordFun 1)).1]
    exact domain_energy_le_domain_momentum R hC ψ.2
  have h0 : (ψ : ℋ) ∈ functionalDomain E (coordFun 0) := by
    rw [← (R.isOperator _ (measurable_coordFun 0)).1]
    exact ψ.2
  have hgd : (ψ : ℋ) ∈ functionalDomain E fun y => ((|y 1| : ℝ) : ℂ) := by
    have he : ∀ y : Fin 2 → ℝ, ‖((|y 1| : ℝ) : ℂ)‖ₑ = ‖coordFun 1 y‖ₑ := fun y => by
      refine le_antisymm (enorm_le_iff_norm_le.mpr ?_) (enorm_le_iff_norm_le.mpr ?_) <;>
        simp [coordFun]
    change ∫⁻ y, ‖((|y 1| : ℝ) : ℂ)‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) < ∞
    simp only [he]
    exact h1
  have hψ : (ψ : ℋ) ∈ (E.functionalCalculus fun y => ((|y 1| : ℝ) : ℂ)).domain := by
    change (ψ : ℋ) ∈ ((E.functionalCalculus fun y => ((|y 1| : ℝ) : ℂ)).domain : Set ℋ)
    rw [(R.isOperator _ hg).1]
    exact hgd
  refine ⟨hψ, ?_⟩
  rw [R.inner_self _ hg ⟨ψ, hψ⟩, R.inner_self _ (measurable_coordFun 0) ψ]
  have hi0 : Integrable (fun y : Fin 2 → ℝ => y 0) (E.spectralValueMeasure ψ) :=
    (integrable_of_mem_functionalDomain hfin (measurable_coordFun 0) h0).re
  have hi1 : Integrable (fun y : Fin 2 → ℝ => |y 1|) (E.spectralValueMeasure ψ) :=
    (integrable_of_mem_functionalDomain hfin hg hgd).re
  have hr : ∫ y, |y 1| ∂(E.spectralValueMeasure ψ) ≤ ∫ y, y 0 ∂(E.spectralValueMeasure ψ) :=
    integral_mono_ae hi1 hi0 (ae_mem_forwardCone hC _)
  have e1 : ∫ y, ((|y 1| : ℝ) : ℂ) ∂(E.spectralValueMeasure ψ) =
      ((∫ y, |y 1| ∂(E.spectralValueMeasure ψ) : ℝ) : ℂ) := integral_ofReal
  have e0 : ∫ y, coordFun 0 y ∂(E.spectralValueMeasure ψ) =
      ((∫ y, y 0 ∂(E.spectralValueMeasure ψ) : ℝ) : ℂ) := integral_ofReal
  rw [e1, e0]
  exact Complex.real_le_real.mpr hr
theorem integral_heatCharacter_of_energy_eq_zero (R : E.CalculusLaws) (Sp : E.SupportLaws)
    (hC : E ⟨QuantumSystem.forwardConeᶜ, isClosed_forwardCone.isOpen_compl.measurableSet⟩ = 0)
    (ψ : (E.functionalCalculus (coordFun 0)).domain)
    (hk : E.functionalCalculus (coordFun 0) ψ = 0) (u : ℝ) :
    ∫ y, heatCharacter 0 u y ∂(E.spectralValueMeasure ψ) = ((‖(ψ : ℋ)‖ ^ 2 : ℝ) : ℂ) := by
  have := Sp.isFiniteMeasure (ψ : ℋ)
  have h0 : (ψ : ℋ) ∈ functionalDomain E (coordFun 0) := by
    rw [← (R.isOperator _ (measurable_coordFun 0)).1]
    exact ψ.2
  have hn := R.norm_sq _ (measurable_coordFun 0) ψ
  rw [hk, norm_zero] at hn
  have hz : ∀ᵐ y ∂(E.spectralValueMeasure ψ), ‖coordFun 0 y‖ ^ 2 = 0 := by
    have h1 := (integral_eq_zero_iff_of_nonneg (fun y => by positivity)
      (integrable_sq_of_mem_functionalDomain (measurable_coordFun 0) h0)).mp
        (by simpa using hn.symm)
    exact h1
  have hone : ∀ᵐ y ∂(E.spectralValueMeasure ψ), heatCharacter 0 u y = 1 := by
    filter_upwards [hz, ae_mem_forwardCone hC ψ] with y hy hc
    have hy0 : y 0 = 0 := by simpa [coordFun] using hy
    have hc' : |y 1| ≤ y 0 := hc
    have hy1 : y 1 = 0 := by
      rw [hy0] at hc'
      exact abs_nonpos_iff.mp hc'
    rw [heatCharacter_of_nonneg 0 u hy0.ge]
    simp [hy0, hy1]
  rw [integral_congr_ae hone, integral_const]
  have hu := Sp.spectralValueMeasure_univ (ψ : ℋ)
  simp [Measure.real, hu]
omit [CompleteSpace ℋ] in
theorem inner_fivePoint_operator (S U V : ℋ →L[ℂ] ℋ) (ψ : ℋ) :
    ⟪ψ, ((1 - S) ^ 2 - S * ((2 : ℂ) • 1 - U - V) : ℋ →L[ℂ] ℋ) ψ⟫_ℂ =
      ⟪ψ, ψ⟫_ℂ - 4 * ⟪ψ, S ψ⟫_ℂ + ⟪ψ, S (S ψ)⟫_ℂ + ⟪ψ, S (U ψ)⟫_ℂ + ⟪ψ, S (V ψ)⟫_ℂ := by
  have hb : (1 - S) ^ 2 - S * ((2 : ℂ) • 1 - U - V) =
      1 - S - S - S - S + S * S + S * U + S * V := by
    rw [two_smul]
    noncomm_ring
  rw [hb]
  change ⟪ψ, ψ - S ψ - S ψ - S ψ - S ψ + S (S ψ) + S (U ψ) + S (V ψ)⟫_ℂ = _
  simp only [inner_add_right, inner_sub_right]
  ring
theorem apply_eq_self_of_inner_eq (U : ℋ →L[ℂ] ℋ) (hU : HilbertSpaceBasics.IsUnitaryOp U) (ψ : ℋ)
    (h : ⟪ψ, U ψ⟫_ℂ = ((‖ψ‖ ^ 2 : ℝ) : ℂ)) : U ψ = ψ := by
  have hn : ‖U ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    have h1 : star U (U ψ) = ψ := by
      have := congrArg (fun T : ℋ →L[ℂ] ℋ => T ψ) hU.1
      simpa using this
    have h2 : ⟪U ψ, U ψ⟫_ℂ = ⟪ψ, ψ⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, h1]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
    exact_mod_cast h2
  have hs := norm_sub_sq (𝕜 := ℂ) ψ (U ψ)
  rw [h, hn] at hs
  have hre : RCLike.re ((‖ψ‖ ^ 2 : ℝ) : ℂ) = ‖ψ‖ ^ 2 := Complex.ofReal_re _
  rw [hre] at hs
  have h0 : ‖ψ - U ψ‖ ^ 2 = 0 := by rw [hs]; ring
  have h1 : ψ - U ψ = 0 := by simpa using h0
  exact (sub_eq_zero.mp h1).symm
end Spectral
section Diagonal
variable (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ))
theorem embedSpatial_zero : embedSpatial 0 = 0 := by
  ext r
  fin_cases r <;> simp [embedSpatial]
theorem embedSpatial_smul (c : ℝ) (a : Fin 3 → ℝ) :
    embedSpatial (c • a) = c • embedSpatial a := by
  ext r
  fin_cases r <;> simp [embedSpatial]
theorem fivePoint_diagonal_nonneg (hS : SemigroupProperties σ h) (hP : SpatialProperties σ h)
    (hM : MatrixElementFormula σ h)
    (i : Fin 3) (t : ℝ≥0) (hf : FivePointNonnegAt σ i t) (ψ : PhysicalSpace σ h) :
    0 ≤ ⟪ψ, ψ⟫_ℂ - 4 * ⟪ψ, timeShift σ h t ψ⟫_ℂ +
      ⟪ψ, timeShift σ h t (timeShift σ h t ψ)⟫_ℂ +
      ⟪ψ, timeShift σ h t (spaceShift σ h ((t : ℝ) • spatialBasisVec i) ψ)⟫_ℂ +
      ⟪ψ, timeShift σ h t (spaceShift σ h ((-(t : ℝ)) • spatialBasisVec i) ψ)⟫_ℂ := by
  obtain ⟨-, -, -, ⟨hT0, hTm⟩, -⟩ := hS
  obtain ⟨-, -, -, ⟨-, hU0, -⟩, -⟩ := hP
  have hd : DenseRange (posClass σ h) :=
    UniformSpace.Completion.denseRange_coe (α := HilbertSpaceBasics.FormSpace (reflectionForm σ) h)
  refine hd.induction_on (p := fun ψ => 0 ≤ ⟪ψ, ψ⟫_ℂ - 4 * ⟪ψ, timeShift σ h t ψ⟫_ℂ +
      ⟪ψ, timeShift σ h t (timeShift σ h t ψ)⟫_ℂ +
      ⟪ψ, timeShift σ h t (spaceShift σ h ((t : ℝ) • spatialBasisVec i) ψ)⟫_ℂ +
      ⟪ψ, timeShift σ h t (spaceShift σ h ((-(t : ℝ)) • spatialBasisVec i) ψ)⟫_ℂ)
    ψ (isClosed_le continuous_const (by fun_prop)) fun Z => ?_
  have m : ∀ (s : ℝ≥0) (a : Fin 3 → ℝ),
      ⟪posClass σ h Z, timeShift σ h s (spaceShift σ h a (posClass σ h Z))⟫_ℂ =
        reflectedCorrelation σ Z ((s : ℝ) • timeBasisVec + embedSpatial a) := hM Z Z
  have c0 : ⟪posClass σ h Z, posClass σ h Z⟫_ℂ = reflectedCorrelation σ Z 0 := by
    have := m 0 0
    simpa [hT0, hU0, embedSpatial_zero] using this
  have c1 : ⟪posClass σ h Z, timeShift σ h t (posClass σ h Z)⟫_ℂ =
      reflectedCorrelation σ Z ((t : ℝ) • timeBasisVec) := by
    have := m t 0
    simpa [hU0, embedSpatial_zero] using this
  have c2 : ⟪posClass σ h Z,
      timeShift σ h t (timeShift σ h t (posClass σ h Z))⟫_ℂ =
      reflectedCorrelation σ Z ((2 * (t : ℝ)) • timeBasisVec) := by
    have h1 := m (t + t) 0
    rw [hU0, embedSpatial_zero, ← hTm, add_zero] at h1
    have h2 : ((t + t : ℝ≥0) : ℝ) = 2 * (t : ℝ) := by push_cast; ring
    rw [h2] at h1
    exact h1
  have c3 : ⟪posClass σ h Z,
      timeShift σ h t (spaceShift σ h ((t : ℝ) • spatialBasisVec i) (posClass σ h Z))⟫_ℂ =
      reflectedCorrelation σ Z ((t : ℝ) • timeBasisVec + (t : ℝ) • embedSpatial (spatialBasisVec i)) := by
    rw [m, embedSpatial_smul]
  have c4 : ⟪posClass σ h Z,
      timeShift σ h t
        (spaceShift σ h ((-(t : ℝ)) • spatialBasisVec i) (posClass σ h Z))⟫_ℂ =
      reflectedCorrelation σ Z ((t : ℝ) • timeBasisVec - (t : ℝ) • embedSpatial (spatialBasisVec i)) := by
    rw [m, embedSpatial_smul, neg_smul, sub_eq_add_neg]
  rw [c0, c1, c2, c3, c4]
  exact hf Z
end Diagonal
theorem smallTimeConeTheorem_holds (hRec : Reconstruction.ReconstructionTheorem)
    (hPair : ShiftSpectralMeasure.ShiftSpectralMeasureTheorem)
    (hR : SpectralTheory.SpectralIntegralLawsHold)
    (hSp : YangMills.Construction.SpectralSupport.ConcentratedOnSupportTheorem) :
    SmallTimeConeTheorem := by
  intro σ hσ
  obtain ⟨h, hc, hE⟩ := hPair σ hσ
  obtain ⟨D₀, hD⟩ := hσ.contraction
  obtain ⟨h', -, hS', hP', hM', -, -⟩ := hRec σ D₀ hD
  have hS : SemigroupProperties σ h := hS'
  have hP : SpatialProperties σ h := hP'
  have hM : MatrixElementFormula σ h := hM'
  refine ⟨h, fun i => ?_⟩
  obtain ⟨hMeas, -, hMom, -, -⟩ := hc i
  obtain ⟨-, ⟨⟨F, -, hF, hFc, hexpT⟩, -⟩, -⟩ := hc 0
  obtain ⟨⟨G, hGv, hG, hexpU⟩, -⟩ := hMom
  have hPM := hMeas.2
  obtain ⟨E, hEdef⟩ : ∃ E, E = (shiftSpectralMeasure σ h i).extend := ⟨_, rfl⟩
  have R := hR 2 _ E
  have Sp := hSp 2 _ E
  have hw : ∀ (s : ℝ≥0) (u : ℝ),
      ofBounded (timeShift σ h s * spaceShift σ h (u • spatialBasisVec i)) =
        E.functionalCalculus (heatCharacter s u) := fun s u => by
    rw [hEdef]
    exact hPM s u
  have hip : ∀ (s : ℝ≥0) (u : ℝ) (ψ : PhysicalSpace σ h),
      ⟪ψ, timeShift σ h s (spaceShift σ h (u • spatialBasisVec i) ψ)⟫_ℂ =
        ∫ y, heatCharacter s u y ∂(E.spectralValueMeasure ψ) := fun s u ψ =>
    inner_apply_eq_integral E R (measurable_heatCharacter s u) (hw s u) ψ
  obtain ⟨-, -, -, ⟨hT0, hTm⟩, -⟩ := id hS
  obtain ⟨-, -, -, ⟨hUni, hU0, -⟩, -⟩ := id hP
  have hOp : ∀ t : ℝ≥0, FivePointNonnegAt σ i t → HeatMomentumInequalityAt σ h i t := by
    intro t ht
    refine ⟨F, G, timeShift σ h t, spaceShift σ h ((t : ℝ) • spatialBasisVec i),
      spaceShift σ h ((-(t : ℝ)) • spatialBasisVec i), hF, hFc, hG, (hexpT t).symm,
      (hexpU _).symm, (hexpU _).symm, fun ψ => ?_⟩
    have hd := fivePoint_diagonal_nonneg σ h hS hP hM i t ht ψ
    rw [← inner_fivePoint_operator (timeShift σ h t)
      (spaceShift σ h ((t : ℝ) • spatialBasisVec i))
      (spaceShift σ h ((-(t : ℝ)) • spatialBasisVec i)) ψ] at hd
    exact hd
  refine ⟨fun t ht0 _ ht hfive => ?_, fun t _ hfive => hOp t hfive⟩
  have hfin := Sp.isFiniteMeasure
  have hv : ∀ k, E.VanishesOn ⟨{y | fivePointSymbol (t k : ℝ) y < 0},
      measurableSet_lt (measurable_fivePointSymbol (t k : ℝ)) measurable_const⟩ := by
    intro k
    refine isNullOn_fivePointSymbol_neg E R hfin (t k).2 fun ψ => ?_
    have hd := fivePoint_diagonal_nonneg σ h hS hP hM i (t k) (hfive k) ψ
    have e0 := hip 0 0 ψ
    have e1 := hip (t k) 0 ψ
    have e2 := hip (t k + t k) 0 ψ
    have e3 := hip (t k) (t k) ψ
    have e4 := hip (t k) (-(t k : ℝ)) ψ
    simp only [zero_smul, hU0, hT0, NNReal.coe_zero] at e0 e1 e2
    rw [← hTm] at e2
    have h2 : ((t k + t k : ℝ≥0) : ℝ) = 2 * (t k : ℝ) := by push_cast; ring
    rw [h2] at e2
    have e2' : ⟪ψ, timeShift σ h (t k) (timeShift σ h (t k) ψ)⟫_ℂ =
        ∫ y, heatCharacter (2 * (t k : ℝ)) 0 y ∂(E.spectralValueMeasure ψ) := e2
    rw [← e0, ← e1, ← e2', ← e3, ← e4]
    exact hd
  have hC : E ⟨QuantumSystem.forwardConeᶜ, isClosed_forwardCone.isOpen_compl.measurableSet⟩ = 0 := by
    refine compl_forwardCone_eq_zero E Sp ?_ (fun k => (t k : ℝ)) (fun k => ht0 k) ?_ hv
    · rw [hEdef]
      exact SpectralMeasureOn.extend_isConcentratedOn _
    · have hl := (NNReal.continuous_coe.tendsto 0).comp ht
      rw [NNReal.coe_zero] at hl
      exact hl
  have hHam : pairHamiltonian σ h = E.functionalCalculus (coordFun 0) := by
    rw [hEdef]
    exact (hE 0 i)
  have hMo : pairMomentum σ h i = E.functionalCalculus (coordFun 1) := by
    rw [hEdef]
    rfl
  have hGim : G = E.imageMeasure momentumProj measurable_momentumProj := by
    have hfun : G.toFun = (E.imageMeasure momentumProj measurable_momentumProj).toFun := by
      funext B
      rw [hEdef]
      exact hGv B
    cases G
    cases hI : E.imageMeasure momentumProj measurable_momentumProj
    rw [hI] at hfun
    simp only at hfun
    subst hfun
    rfl
  have hAbs : G.absValueOp = E.functionalCalculus fun y => ((|y 1| : ℝ) : ℂ) := by
    rw [hGim]
    exact R.calculus_imageMeasure 1 momentumProj measurable_momentumProj _
      (Complex.measurable_ofReal.comp (by fun_prop))
  refine ⟨fun k => hOp (t k) (hfive k), ?_, ?_, ⟨G, hG, ?_⟩, ⟨G, hG, ?_⟩⟩
  · have hsup := (Sp.support_subset_iff _ isClosed_forwardCone).mpr hC
    change (shiftSpectralMeasure σ h i).extend.support ⊆ QuantumSystem.forwardCone
    rw [← hEdef]
    exact hsup
  · change (pairHamiltonian σ h).domain ≤ (pairMomentum σ h i).domain
    rw [hHam, hMo]
    exact domain_energy_le_domain_momentum R hC
  · rw [hAbs, hHam]
    exact inner_abs_momentum_le_inner_energy R hfin hC
  · rw [hHam]
    intro ψ hk u
    have hm : (ψ : PhysicalSpace σ h) ∈ (G.expIMulOp u).domain := by
      rw [hexpU u]
      exact Submodule.mem_top
    refine ⟨hm, ?_⟩
    rw [apply_eq_of_eq_ofBounded (hexpU u) ⟨ψ, hm⟩]
    refine apply_eq_self_of_inner_eq _ (hUni _) _ ?_
    have e := hip 0 u ψ
    simp only [hT0, NNReal.coe_zero] at e
    have e' : ⟪(ψ : PhysicalSpace σ h), spaceShift σ h (u • spatialBasisVec i) ψ⟫_ℂ =
        ∫ y, heatCharacter 0 u y ∂(E.spectralValueMeasure ψ) := e
    exact e'.trans (integral_heatCharacter_of_energy_eq_zero R Sp hC ψ hk u)
end YangMills.Construction.ReflectionPositivity.SmallTimeCone
