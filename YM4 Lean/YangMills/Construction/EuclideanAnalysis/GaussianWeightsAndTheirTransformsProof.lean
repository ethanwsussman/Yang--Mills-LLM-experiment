import YangMills.Construction.EuclideanAnalysis.GaussianWeightsAndTheirTransforms
import Mathlib
open Filter Topology MeasureTheory
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanAnalysis.GaussianDensity
theorem density_eq_inv_sqrt_mul_exp {σ : ℝ} (hσ : 0 < σ) (m x : ℝ) :
    Strip.gaussianDensity σ m x =
      (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-(x - m) ^ 2 / (2 * σ)) := by
  have hpos : 0 < 2 * Real.pi * σ := by positivity
  unfold Strip.gaussianDensity YangMills.Construction.RealPower.rpowPos
  rw [if_pos hpos, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos, ← Real.exp_neg]
  congr 2
  ring
theorem density_nonneg {σ : ℝ} (hσ : 0 < σ) (m x : ℝ) : 0 ≤ Strip.gaussianDensity σ m x := by
  rw [density_eq_inv_sqrt_mul_exp hσ]
  positivity
theorem continuous_density (σ m : ℝ) : Continuous (Strip.gaussianDensity σ m) := by
  unfold Strip.gaussianDensity
  fun_prop
theorem integral_cexp_mul_cexp_neg_sq {b : ℝ} (hb : 0 < b) (t : ℝ) :
    (∫ x : ℝ, Complex.exp (Complex.I * t * x) * Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2)) =
      (Real.sqrt (Real.pi / b) : ℂ) * Complex.exp (-(t : ℂ) ^ 2 / (4 * b)) := by
  rw [fourierIntegral_gaussian (b := (b : ℂ)) (by simpa using hb) (t : ℂ)]
  congr 1
  have hcast : ((Real.pi : ℂ) / b) = ((Real.pi / b : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
  push_cast
  rfl
theorem characteristic_function {σ : ℝ} (hσ : 0 < σ) (m ξ : ℝ) :
    (∫ x : ℝ, (Strip.gaussianDensity σ m x : ℂ) * Complex.exp (Complex.I * x * ξ)) =
      Complex.exp (Complex.I * m * ξ - σ * (ξ : ℂ) ^ 2 / 2) := by
  have hσC : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hb : 0 < 1 / (2 * σ) := by positivity
  have hroot : 0 < Real.sqrt (2 * Real.pi * σ) := Real.sqrt_pos.2 (by positivity)
  have hrootC : ((Real.sqrt (2 * Real.pi * σ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hroot.ne'
  have hshift : ∀ u : ℝ,
      (Strip.gaussianDensity σ m (u + m) : ℂ) * Complex.exp (Complex.I * ((u + m : ℝ) : ℂ) * ξ) =
        ((Real.sqrt (2 * Real.pi * σ) : ℝ) : ℂ)⁻¹ * (Complex.exp (Complex.I * m * ξ) *
          (Complex.exp (Complex.I * ξ * u) *
            Complex.exp (-((1 / (2 * σ) : ℝ) : ℂ) * (u : ℂ) ^ 2))) := by
    intro u
    have hexp : Complex.exp ((-(u + m - m) ^ 2 / (2 * σ) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((u + m : ℝ) : ℂ) * ξ) =
        Complex.exp (Complex.I * m * ξ) * (Complex.exp (Complex.I * ξ * u) *
          Complex.exp (-((1 / (2 * σ) : ℝ) : ℂ) * (u : ℂ) ^ 2)) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    rw [density_eq_inv_sqrt_mul_exp hσ, Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, hexp,
      Complex.ofReal_inv]
  rw [← integral_add_right_eq_self _ m]
  simp_rw [hshift]
  rw [integral_const_mul, integral_const_mul, integral_cexp_mul_cexp_neg_sq hb]
  have hquot : Real.pi / (1 / (2 * σ)) = 2 * Real.pi * σ := by
    field_simp
  rw [hquot]
  have hsplit : Complex.exp (Complex.I * m * ξ - σ * (ξ : ℂ) ^ 2 / 2) =
      Complex.exp (Complex.I * m * ξ) *
        Complex.exp (-(ξ : ℂ) ^ 2 / (4 * ((1 / (2 * σ) : ℝ) : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [hsplit]
  field_simp
theorem integral_density {σ : ℝ} (hσ : 0 < σ) (m : ℝ) :
    (∫ x : ℝ, Strip.gaussianDensity σ m x) = 1 := by
  have hzero := characteristic_function hσ m 0
  have hcomplex : ((∫ x : ℝ, Strip.gaussianDensity σ m x : ℝ) : ℂ) = 1 := by
    rw [← integral_complex_ofReal]
    simpa using hzero
  exact_mod_cast hcomplex
theorem fourier_inversion {σ : ℝ} (hσ : 0 < σ) (m x : ℝ) :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ ξ : ℝ, Complex.exp (Complex.I * m * ξ - σ * (ξ : ℂ) ^ 2 / 2) *
          Complex.exp (-(Complex.I * x * ξ))) =
      (Strip.gaussianDensity σ m x : ℂ) := by
  have hσC : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hmerge : ∀ ξ : ℝ,
      Complex.exp (Complex.I * m * ξ - σ * (ξ : ℂ) ^ 2 / 2) *
          Complex.exp (-(Complex.I * x * ξ)) =
        Complex.exp (Complex.I * ((m - x : ℝ) : ℂ) * ξ) *
          Complex.exp (-((σ / 2 : ℝ) : ℂ) * (ξ : ℂ) ^ 2) := by
    intro ξ
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hmerge]
  rw [integral_cexp_mul_cexp_neg_sq (half_pos hσ), density_eq_inv_sqrt_mul_exp hσ]
  have hprod : Real.sqrt (Real.pi / (σ / 2)) * Real.sqrt (2 * Real.pi * σ) = 2 * Real.pi := by
    rw [← Real.sqrt_mul (by positivity)]
    have hsq : Real.pi / (σ / 2) * (2 * Real.pi * σ) = (2 * Real.pi) ^ 2 := by
      field_simp
    rw [hsq, Real.sqrt_sq (by positivity)]
  have hconst : 1 / (2 * Real.pi) * Real.sqrt (Real.pi / (σ / 2)) =
      (Real.sqrt (2 * Real.pi * σ))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [mul_assoc, hprod]
    field_simp
  have hconstC : (1 / (2 * Real.pi) : ℂ) * ((Real.sqrt (Real.pi / (σ / 2)) : ℝ) : ℂ) =
      ((Real.sqrt (2 * Real.pi * σ) : ℝ) : ℂ)⁻¹ := by
    exact_mod_cast hconst
  have hexponent : -((m - x : ℝ) : ℂ) ^ 2 / (4 * ((σ / 2 : ℝ) : ℂ)) =
      ((-(x - m) ^ 2 / (2 * σ) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [← mul_assoc, hconstC, hexponent, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_inv]
theorem integral_density_mul_eq_standard {σ : ℝ} (hσ : 0 < σ) (m : ℝ) (f : ℝ → ℂ) :
    (∫ x : ℝ, (Strip.gaussianDensity σ m x : ℂ) * f x) =
      ∫ z : ℝ, (Strip.gaussianDensity 1 0 z : ℂ) * f (m + Real.sqrt σ * z) := by
  have hroot : 0 < Real.sqrt σ := Real.sqrt_pos.2 hσ
  have hroot_sq : Real.sqrt σ * Real.sqrt σ = σ := Real.mul_self_sqrt hσ.le
  have hrootC : ((Real.sqrt σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hroot.ne'
  have hscale : ∀ z : ℝ, Strip.gaussianDensity 1 0 z =
      Real.sqrt σ * Strip.gaussianDensity σ m (Real.sqrt σ * z + m) := by
    intro z
    have hsplit : Real.sqrt (2 * Real.pi * σ) = Real.sqrt (2 * Real.pi) * Real.sqrt σ :=
      Real.sqrt_mul (by positivity) σ
    have hexponent : -(Real.sqrt σ * z + m - m) ^ 2 / (2 * σ) = -(z - 0) ^ 2 / (2 * 1) := by
      have hsq : (Real.sqrt σ * z + m - m) ^ 2 = (Real.sqrt σ * Real.sqrt σ) * z ^ 2 := by
        ring
      rw [hsq, hroot_sq]
      field_simp
      ring
    rw [density_eq_inv_sqrt_mul_exp one_pos, density_eq_inv_sqrt_mul_exp hσ, hsplit, hexponent,
      mul_one]
    field_simp
  have hpoint : ∀ z : ℝ, (Strip.gaussianDensity 1 0 z : ℂ) * f (m + Real.sqrt σ * z) =
      ((Real.sqrt σ : ℝ) : ℂ) * ((Strip.gaussianDensity σ m (Real.sqrt σ * z + m) : ℂ) *
        f (Real.sqrt σ * z + m)) := by
    intro z
    rw [hscale z, add_comm m, Complex.ofReal_mul, mul_assoc]
  have hchange : (∫ z : ℝ, (Strip.gaussianDensity σ m (Real.sqrt σ * z + m) : ℂ) *
        f (Real.sqrt σ * z + m)) =
      |(Real.sqrt σ)⁻¹| • ∫ u : ℝ, (Strip.gaussianDensity σ m (u + m) : ℂ) * f (u + m) :=
    Measure.integral_comp_mul_left
      (fun u : ℝ => (Strip.gaussianDensity σ m (u + m) : ℂ) * f (u + m)) _
  simp_rw [hpoint]
  rw [integral_const_mul, hchange,
    integral_add_right_eq_self (fun x : ℝ => (Strip.gaussianDensity σ m x : ℂ) * f x) m,
    abs_of_pos (inv_pos.2 hroot), Complex.real_smul, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ hrootC, one_mul]
theorem integrable_standard_density : Integrable (Strip.gaussianDensity 1 0) := by
  have hint := (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul
    (Real.sqrt (2 * Real.pi * 1))⁻¹
  refine hint.congr (Eventually.of_forall fun z => ?_)
  simp only []
  rw [density_eq_inv_sqrt_mul_exp one_pos]
  congr 2
  ring
theorem tendsto_integral_density_mul (m : ℝ) (f : ℝ → ℂ) (hf : Continuous f)
    (hbound : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun σ : ℝ => ∫ x : ℝ, (Strip.gaussianDensity σ m x : ℂ) * f x) (𝓝[>] 0)
      (𝓝 (f m)) := by
  obtain ⟨C, hC⟩ := hbound
  have heq : (fun σ : ℝ => ∫ z : ℝ, (Strip.gaussianDensity 1 0 z : ℂ) * f (m + Real.sqrt σ * z))
      =ᶠ[𝓝[>] 0] fun σ : ℝ => ∫ x : ℝ, (Strip.gaussianDensity σ m x : ℂ) * f x := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (integral_density_mul_eq_standard hσ m f).symm
  refine Tendsto.congr' heq ?_
  have hvalue : (∫ z : ℝ, (Strip.gaussianDensity 1 0 z : ℂ) * f m) = f m := by
    rw [integral_mul_const, integral_complex_ofReal, integral_density one_pos]
    simp
  rw [← hvalue]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z => Strip.gaussianDensity 1 0 z * C)
    (Eventually.of_forall fun σ => ?_) (Eventually.of_forall fun σ => ae_of_all _ fun z => ?_)
    (integrable_standard_density.mul_const C) (ae_of_all _ fun z => ?_)
  · have hcont₁ : Continuous fun z : ℝ => (Strip.gaussianDensity 1 0 z : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_density 1 0)
    have hcont₂ : Continuous fun z : ℝ => f (m + Real.sqrt σ * z) :=
      hf.comp (continuous_const.add (continuous_const.mul continuous_id))
    exact (hcont₁.mul hcont₂).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (density_nonneg one_pos 0 z)]
    exact mul_le_mul_of_nonneg_left (hC _) (density_nonneg one_pos 0 z)
  · have harg : Tendsto (fun σ : ℝ => m + Real.sqrt σ * z) (𝓝[>] 0) (𝓝 m) := by
      have hcont : Continuous fun σ : ℝ => m + Real.sqrt σ * z :=
        continuous_const.add (Real.continuous_sqrt.mul continuous_const)
      exact (hcont.tendsto' 0 m (by simp)).mono_left nhdsWithin_le_nhds
    exact ((hf.tendsto m).comp harg).const_mul _
theorem gaussianDensityTransforms_holds : Strip.GaussianDensityTransforms := fun m =>
  ⟨fun _ hσ => ⟨integral_density hσ m, characteristic_function hσ m, fourier_inversion hσ m⟩,
    tendsto_integral_density_mul m⟩
end YangMills.Construction.EuclideanAnalysis.GaussianDensity
