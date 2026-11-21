import YangMills.Construction.Gaussian.PositiveDefiniteMatrixIntegral
import Mathlib
set_option autoImplicit false
open MeasureTheory Matrix
open scoped MatrixOrder
namespace YangMills.Construction.Gaussian.PosDefMatrix
theorem realGaussianIntegral : RealGaussianIntegral := by
  intro n A hA
  obtain ⟨M, hMA⟩ : ∃ M : Matrix (Fin n) (Fin n) ℝ, A = star M * M :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  have hdet : A.det = M.det ^ 2 := by
    rw [hMA, star_eq_conjTranspose, det_mul, conjTranspose_eq_transpose_of_trivial,
      det_transpose, sq]
  have hpos : 0 < A.det := hA.det_pos
  have hM0 : M.det ≠ 0 := by
    intro h
    rw [hdet, h] at hpos
    simp at hpos
  have hquad : ∀ x : Fin n → ℝ, x ⬝ᵥ A *ᵥ x = ∑ i, (M *ᵥ x) i ^ 2 := by
    intro x
    rw [hMA, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, ← mulVec_mulVec,
      dotProduct_mulVec, vecMul_transpose]
    simp [dotProduct, sq]
  let φ : ℝ → ℝ := fun t => Real.exp (-(1 / 2) * t ^ 2)
  let Φ : (Fin n → ℝ) → ℝ := fun y => ∏ i, φ (y i)
  have hΦ : ∀ x : Fin n → ℝ,
      Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x)) = Φ (toLin' M x) := by
    intro x
    simp only [Φ, φ, toLin'_apply, hquad, Finset.mul_sum, Real.exp_sum]
  have hlin : Continuous (toLin' M) := LinearMap.continuous_of_finiteDimensional _
  have hΦcont : Continuous Φ := by
    simp only [Φ, φ]
    fun_prop
  have hsubst : ∫ x : Fin n → ℝ, Φ (toLin' M x) = |M.det|⁻¹ * ∫ y : Fin n → ℝ, Φ y := by
    rw [← integral_map hlin.measurable.aemeasurable hΦcont.aestronglyMeasurable,
      Real.map_matrix_volume_pi_eq_smul_volume_pi hM0, integral_smul_measure,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul]
  have hfactor : ∫ y : Fin n → ℝ, Φ y = Real.sqrt (2 * Real.pi) ^ n := by
    have hpi := integral_fintype_prod_volume_eq_pow (ι := Fin n) φ
    have hone : ∫ t : ℝ, φ t = Real.sqrt (2 * Real.pi) := by
      have := integral_gaussian (1 / 2)
      simp only [φ]
      rw [this]
      congr 1
      ring
    simp only [Φ]
    rw [hpi, hone, Fintype.card_fin]
  have hroot : Real.sqrt A.det = |M.det| := by
    rw [hdet, Real.sqrt_sq_eq_abs]
  have hrpow : Real.sqrt (2 * Real.pi) ^ n = (2 * Real.pi) ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  simp_rw [hΦ]
  rw [hsubst, hfactor, hroot, hrpow]
  exact (div_eq_inv_mul _ _).symm
end YangMills.Construction.Gaussian.PosDefMatrix
