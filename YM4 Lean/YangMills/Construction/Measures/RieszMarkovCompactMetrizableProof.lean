import YangMills.Construction.Measures.RieszMarkovCompactMetrizable
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory
open scoped ComplexOrder CompactlySupported
noncomputable section
namespace YangMills.Construction.Measures.RieszMarkov
variable {X : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X]
def complexifyReal (g : C(X, ℝ)) : C(X, ℂ) :=
  ⟨fun x => (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩
def reMap (f : C(X, ℂ)) : C(X, ℝ) :=
  ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩
def imMap (f : C(X, ℂ)) : C(X, ℝ) :=
  ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩
theorem integrable_of_continuousMap {E : Type} [NormedAddCommGroup E] (μ : Measure X)
    [IsFiniteMeasure μ] (f : C(X, E)) : Integrable (fun x => f x) μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
theorem measure_eq_of_integral_real_eq (μ ν : Measure X) (hμ : IsFiniteMeasure μ)
    (hν : IsFiniteMeasure ν)
    (h : ∀ f : C(X, ℝ), ∫ x, f x ∂μ = ∫ x, f x ∂ν) : μ = ν := by
  let := TopologicalSpace.metrizableSpaceMetric X
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => h f.toContinuousMap
theorem exists_finiteMeasure_of_positive_real (Λ : C(X, ℝ) →ₗ[ℝ] ℝ)
    (hΛ : ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ Λ f) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ ∀ f : C(X, ℝ), Λ f = ∫ x, f x ∂μ := by
  let Φ₀ : C_c(X, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun g => Λ g.toContinuousMap
      map_add' := fun f g => by
        rw [← map_add]
        rfl
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← map_smul]
        rfl }
  let Φ : C_c(X, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ Φ₀ fun g hg => hΛ _ fun x => hg x
  refine ⟨RealRMK.rieszMeasure Φ, inferInstance, fun f => ?_⟩
  exact (RealRMK.integral_rieszMeasure Φ (CompactlySupportedContinuousMap.continuousMapEquiv f)).symm
theorem real_representation (Λ : C(X, ℝ) →ₗ[ℝ] ℝ)
    (hΛ : ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ Λ f) :
    (∃! μ : Measure X, IsFiniteMeasure μ ∧ ∀ f : C(X, ℝ), Λ f = ∫ x, f x ∂μ) ∧
      (Λ 1 = 1 → ∀ μ : Measure X, IsFiniteMeasure μ →
        (∀ f : C(X, ℝ), Λ f = ∫ x, f x ∂μ) → IsProbabilityMeasure μ) := by
  obtain ⟨μ, hμ, hrep⟩ := exists_finiteMeasure_of_positive_real Λ hΛ
  refine ⟨⟨μ, ⟨hμ, hrep⟩, fun ν hν => ?_⟩, fun hone ν hν hrepν => ?_⟩
  · exact measure_eq_of_integral_real_eq ν μ hν.1 hμ fun f => by rw [← hν.2 f, ← hrep f]
  · have h : ν.real Set.univ = 1 := by
      have := hrepν 1
      simpa [hone] using this.symm
    refine ⟨?_⟩
    rwa [measureReal_def, ENNReal.toReal_eq_one_iff] at h
theorem im_apply_complexifyReal (Λ : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hΛ : ∀ f : C(X, ℂ), (∀ x, 0 ≤ f x) → 0 ≤ Λ f) (g : C(X, ℝ)) :
    (Λ (complexifyReal g)).im = 0 := by
  have pos : ∀ p : C(X, ℝ), (∀ x, 0 ≤ p x) → (Λ (complexifyReal p)).im = 0 := fun p hp =>
    (Complex.nonneg_iff.mp (hΛ _ fun x => Complex.zero_le_real.mpr (hp x))).2.symm
  let p : C(X, ℝ) := ⟨fun x => max (g x) 0, by fun_prop⟩
  let n : C(X, ℝ) := ⟨fun x => max (-(g x)) 0, by fun_prop⟩
  have hg : complexifyReal g = complexifyReal p - complexifyReal n := by
    ext x
    simp [complexifyReal, p, n, ← Complex.ofReal_sub, max_zero_sub_max_neg_zero_eq_self]
  rw [hg, map_sub, Complex.sub_im, pos p fun x => le_max_right _ _,
    pos n fun x => le_max_right _ _, sub_zero]
theorem eq_complexifyReal_re_add_I_smul (f : C(X, ℂ)) :
    f = complexifyReal (reMap f) + Complex.I • complexifyReal (imMap f) := by
  ext x
  simp [complexifyReal, reMap, imMap, mul_comm Complex.I]
def realRestriction (Λ : C(X, ℂ) →ₗ[ℂ] ℂ) : C(X, ℝ) →ₗ[ℝ] ℝ where
  toFun g := (Λ (complexifyReal g)).re
  map_add' f g := by
    have : complexifyReal (f + g) = complexifyReal f + complexifyReal g := by
      ext x
      simp [complexifyReal]
    rw [this, map_add, Complex.add_re]
  map_smul' c f := by
    have : complexifyReal (c • f) = (c : ℂ) • complexifyReal f := by
      ext x
      simp [complexifyReal]
    rw [this, map_smul, smul_eq_mul, Complex.re_ofReal_mul, RingHom.id_apply, smul_eq_mul]
theorem apply_complexifyReal (Λ : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hΛ : ∀ f : C(X, ℂ), (∀ x, 0 ≤ f x) → 0 ≤ Λ f) (g : C(X, ℝ)) :
    Λ (complexifyReal g) = (realRestriction Λ g : ℂ) :=
  Complex.ext (by simp [realRestriction]) (by simp [im_apply_complexifyReal Λ hΛ g])
theorem integral_complexifyReal (μ : Measure X) (g : C(X, ℝ)) :
    ∫ x, complexifyReal g x ∂μ = ((∫ x, g x ∂μ : ℝ) : ℂ) :=
  integral_complex_ofReal
theorem complex_representation (Λ : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hΛ : ∀ f : C(X, ℂ), (∀ x, 0 ≤ f x) → 0 ≤ Λ f) :
    (∃! μ : Measure X, IsFiniteMeasure μ ∧ ∀ f : C(X, ℂ), Λ f = ∫ x, f x ∂μ) ∧
      (Λ 1 = 1 → ∀ μ : Measure X, IsFiniteMeasure μ →
        (∀ f : C(X, ℂ), Λ f = ∫ x, f x ∂μ) → IsProbabilityMeasure μ) := by
  have hre : ∀ g : C(X, ℝ), (∀ x, 0 ≤ g x) → 0 ≤ realRestriction Λ g := fun g hg =>
    (Complex.nonneg_iff.mp (hΛ _ fun x => Complex.zero_le_real.mpr (hg x))).1
  obtain ⟨μ, hμ, hrep⟩ := exists_finiteMeasure_of_positive_real (realRestriction Λ) hre
  have hrepC : ∀ f : C(X, ℂ), Λ f = ∫ x, f x ∂μ := fun f => by
    have hi := integral_re_add_im (integrable_of_continuousMap μ f)
    rw [← hi]
    conv_lhs => rw [eq_complexifyReal_re_add_I_smul f]
    rw [map_add, map_smul, apply_complexifyReal Λ hΛ, apply_complexifyReal Λ hΛ, hrep, hrep]
    simp [reMap, imMap, mul_comm Complex.I]
  refine ⟨⟨μ, ⟨hμ, hrepC⟩, fun ν hν => ?_⟩, fun hone ν hν hrepν => ?_⟩
  · refine measure_eq_of_integral_real_eq ν μ hν.1 hμ fun g => ?_
    apply Complex.ofReal_injective
    rw [← integral_complexifyReal, ← integral_complexifyReal, ← hν.2, ← hrepC]
  · have h : ν.real Set.univ = 1 := by
      have := hrepν 1
      rw [hone] at this
      have h' : (1 : ℂ) = ((ν.real Set.univ : ℝ) : ℂ) := by simpa using this
      exact_mod_cast h'.symm
    refine ⟨?_⟩
    rwa [measureReal_def, ENNReal.toReal_eq_one_iff] at h
theorem positiveFunctional_representation_holds : positiveFunctional_representation := by
  intro X _ _ _ _ _
  refine ⟨real_representation, complex_representation, measure_eq_of_integral_real_eq, ?_⟩
  intro μ ν hμ hν h
  refine measure_eq_of_integral_real_eq μ ν hμ hν fun g => ?_
  apply Complex.ofReal_injective
  rw [← integral_complexifyReal, ← integral_complexifyReal]
  exact h (complexifyReal g)
end YangMills.Construction.Measures.RieszMarkov
end
