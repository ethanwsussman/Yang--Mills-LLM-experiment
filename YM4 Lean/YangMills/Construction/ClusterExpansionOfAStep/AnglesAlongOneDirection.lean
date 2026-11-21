import YangMills.Construction.ColdStepAtMirrorFrames.BareActionIsCriticalAtAnAbelianFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TorusFields
open BlockAverages (UnitQuaternion expUnit imaginaryQuaternions)
variable {n : ℕ}
theorem expUnit_add_smul (X : imaginaryQuaternions) (a b : ℝ) :
    expUnit ((a + b) • X) = expUnit (a • X) * expUnit (b • X) := by apply _root_.YangMills.SharedProofs.p2328 <;> assumption
theorem expUnit_zero_smul (X : imaginaryQuaternions) : expUnit ((0 : ℝ) • X) = 1 := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.expUnit_zero_smul <;> assumption
theorem expUnit_neg_smul (X : imaginaryQuaternions) (a : ℝ) : expUnit ((-a) • X) = (expUnit (a • X))⁻¹ := by
  have h : expUnit ((-a) • X) * expUnit (a • X) = 1 := by
    rw [← expUnit_add_smul]
    simpa using expUnit_zero_smul X
  exact eq_inv_of_mul_eq_one_left h
theorem expUnit_sub_smul (X : imaginaryQuaternions) (a b : ℝ) :
    expUnit ((a - b) • X) = expUnit (a • X) * (expUnit (b • X))⁻¹ := by
  rw [sub_eq_add_neg, expUnit_add_smul, expUnit_neg_smul]
theorem coe_expUnit_smul (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (t : ℝ) :
    ((expUnit (t • X) : UnitQuaternion) : ℍ[ℝ]) =
      ((Real.cos t : ℝ) : ℍ[ℝ]) + Real.sin t • ((X : imaginaryQuaternions) : ℍ[ℝ]) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.coe_expUnit_smul <;> assumption
theorem expUnit_two_pi_int_smul (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (m : ℤ) :
    expUnit ((2 * Real.pi * m) • X) = 1 := by
  apply Subtype.ext
  rw [coe_expUnit_smul X hX]
  have hc : Real.cos (2 * Real.pi * m) = 1 := by
    have := Real.cos_int_mul_two_pi m
    rwa [mul_comm] at this
  have hs : Real.sin (2 * Real.pi * m) = 0 := by
    have e : 2 * Real.pi * m = ((2 * m : ℤ) : ℝ) * Real.pi := by
      push_cast
      ring
    rw [e]
    exact Real.sin_int_mul_pi _
  simp [hc, hs]
theorem norm_coe_expUnit_smul_sub_one_le (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (t : ℝ) :
    ‖((expUnit (t • X) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ t ^ 2 / 2 + |t| := by
  rw [coe_expUnit_smul X hX]
  have h1 : ((Real.cos t : ℝ) : ℍ[ℝ]) + Real.sin t • ((X : imaginaryQuaternions) : ℍ[ℝ]) - 1 =
      ((Real.cos t - 1 : ℝ) : ℍ[ℝ]) + Real.sin t • ((X : imaginaryQuaternions) : ℍ[ℝ]) := by
    have e : ((Real.cos t - 1 : ℝ) : ℍ[ℝ]) = ((Real.cos t : ℝ) : ℍ[ℝ]) - 1 := by simp
    rw [e]
    abel
  rw [h1]
  refine (norm_add_le _ _).trans ?_
  have h2 : ‖((Real.cos t - 1 : ℝ) : ℍ[ℝ])‖ ≤ t ^ 2 / 2 := by
    rw [Quaternion.norm_coe, Real.norm_eq_abs, abs_le]
    constructor
    · have := Real.one_sub_sq_div_two_le_cos (x := t)
      linarith
    · have := Real.cos_le_one t
      nlinarith [sq_nonneg t]
  have h3 : ‖Real.sin t • ((X : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ |t| := by
    rw [norm_smul]
    have hXq : ‖((X : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by simpa using hX
    rw [hXq, mul_one, Real.norm_eq_abs]
    exact Real.abs_sin_le_abs
  linarith
def angleCurl (θ : TorusSite n → Fin 4 → ℝ) (x : TorusSite n) (i j : Fin 4) : ℝ :=
  θ x i + θ (x + unitStep n i) j - θ (x + unitStep n j) i - θ x j
theorem holonomy_eq_expUnit_angleCurl (X : imaginaryQuaternions) (θ : TorusSite n → Fin 4 → ℝ) (V : TorusField n)
    (hV : ∀ x i, V x i = expUnit (θ x i • X)) (x : TorusSite n) (i j : Fin 4) :
    holonomy V x i j = expUnit (angleCurl θ x i j • X) := by
  simp only [holonomy, angleCurl, hV, sub_eq_add_neg, expUnit_add_smul, expUnit_neg_smul]
end YangMills.Construction.TorusFields
end
