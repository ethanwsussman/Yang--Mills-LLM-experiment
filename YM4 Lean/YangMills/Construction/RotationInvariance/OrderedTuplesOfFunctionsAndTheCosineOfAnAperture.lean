import YangMills.Construction.RotationInvariance.PencilsOfThePlane
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ForwardTube
def rightAngle : rightAngleMultiples := ⟨Real.pi / 2, 1, by simp⟩
theorem rotatedDirection_eq_rotate_unitX (θ : rightAngleMultiples) :
    rotatedDirection θ = RealPlane.rotate θ RealPlane.unitX := by
  ext i
  fin_cases i <;>
    simp [rotatedDirection, rotatedUnitVector_eq_cos_sin, RealPlane.rotate,
      RealPlane.unitX, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
theorem rotatedDirection_rightAngle :
    rotatedDirection rightAngle = RealPlane.unitY := by
  rw [rotatedDirection_eq_rotate_unitX]
  ext i
  fin_cases i <;>
    simp [RealPlane.rotate, RealPlane.unitX,
      RealPlane.unitY, rightAngle]
theorem inner_eq_coord_sum (u y : RealPlane) :
    inner ℝ u y = u 0 * y 0 + u 1 * y 1 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  ring
def FunsDirectionSeparated {E : Type*} [Zero E] (θ : rightAngleMultiples) {n : ℕ}
    (f : Fin n → RealPlane → E) : Prop :=
  (∀ i, HasCompactSupport (f i)) ∧ (∀ i, f i ≠ 0) ∧ IsDirectionSeparated θ fun i => tsupport (f i)
def FunsTimeSeparated {E : Type*} [Zero E] {n : ℕ}
    (f : Fin n → RealPlane → E) : Prop :=
  FunsDirectionSeparated rightAngleZero f
end ForwardTube
namespace RealPlane
def openingAngleCos (a : openingAngles) : ℝ := Real.cos ((a : ℝ) + Real.pi / 4)
end RealPlane
end YangMills.Construction
end
