import YangMills.Construction.ForwardTube.LightConeCoordinates
import YangMills.Construction.PositiveDefinite.HalfPlaneKernelDefs
import Mathlib
set_option autoImplicit false
open Complex
noncomputable section
namespace YangMills.Construction.ForwardTube
def rightAngleMultiples : Set ℝ := {θ | ∃ k : ℤ, θ = k * (Real.pi / 2)}
def rightAngleZero : rightAngleMultiples := ⟨0, 0, by simp⟩
def embedPlane (y : RealPlane) : ℂ × ℂ := ((y 0 : ℂ), (y 1 : ℂ))
def rotatedUnitVector (θ : rightAngleMultiples) : ℂ × ℂ :=
  complexBoost ((θ : ℝ) : ℂ) (embedPlane RealPlane.unitX)
theorem rotatedUnitVector_eq_cos_sin (θ : rightAngleMultiples) :
    rotatedUnitVector θ = ((Real.cos θ : ℂ), (Real.sin θ : ℂ)) := by
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hx : (RealPlane.unitX 0 : ℝ) = 1 := by simp [RealPlane.unitX]
  have hy : (RealPlane.unitX 1 : ℝ) = 0 := by simp [RealPlane.unitX]
  simp only [rotatedUnitVector, complexBoost, ofLightConeCoords, lightConePlus, lightConeMinus,
    embedPlane, hx, hy, Complex.ofReal_cos, Complex.ofReal_sin, Complex.cos, Complex.sin,
    Prod.mk.injEq, Complex.ofReal_one, Complex.ofReal_zero, mul_zero, add_zero, sub_zero, mul_one]
  rw [show ((θ : ℝ) : ℂ) * I = I * ((θ : ℝ) : ℂ) from mul_comm _ _,
    show -((θ : ℝ) : ℂ) * I = -(I * ((θ : ℝ) : ℂ)) by ring]
  generalize exp (I * ((θ : ℝ) : ℂ)) = p
  generalize exp (-(I * ((θ : ℝ) : ℂ))) = q
  constructor
  · ring
  · field_simp
    linear_combination (p - q) * I_sq
def rotatedDirection (θ : rightAngleMultiples) : RealPlane :=
  !₂[(rotatedUnitVector θ).1.re, (rotatedUnitVector θ).2.re]
theorem rotatedDirection_rightAngleZero :
    rotatedDirection rightAngleZero = RealPlane.unitX := by
  ext j
  fin_cases j <;>
    simp [rotatedDirection, rotatedUnitVector_eq_cos_sin, rightAngleZero, RealPlane.unitX]
def rotatedForwardTube (θ : rightAngleMultiples) : Set (ℂ × ℂ) :=
  complexBoost ((θ : ℝ) : ℂ) '' forwardTube
def supInner (v : RealPlane) (S : Set RealPlane) : ℝ :=
  sSup ((fun y => inner ℝ v y) '' S)
def infInner (v : RealPlane) (S : Set RealPlane) : ℝ :=
  sInf ((fun y => inner ℝ v y) '' S)
theorem isGreatest_supInner (v : RealPlane) {S : Set RealPlane} (hS : IsCompact S)
    (hne : S.Nonempty) : IsGreatest ((fun y => inner ℝ v y) '' S) (supInner v S) := by
  have himg : IsCompact ((fun y => inner ℝ v y) '' S) :=
    hS.image (continuous_const.inner continuous_id)
  exact ⟨himg.sSup_mem (hne.image _), himg.isLUB_sSup (hne.image _) |>.1⟩
theorem isLeast_infInner (v : RealPlane) {S : Set RealPlane} (hS : IsCompact S)
    (hne : S.Nonempty) : IsLeast ((fun y => inner ℝ v y) '' S) (infInner v S) := by
  have himg : IsCompact ((fun y => inner ℝ v y) '' S) :=
    hS.image (continuous_const.inner continuous_id)
  exact ⟨himg.sInf_mem (hne.image _), himg.isGLB_sInf (hne.image _) |>.1⟩
def IsDirectionSeparated (θ : rightAngleMultiples) {n : ℕ} (S : Fin n → Set RealPlane) : Prop :=
  (∀ j, IsCompact (S j)) ∧ (∀ j, (S j).Nonempty) ∧
    ∀ (j : ℕ) (hj : j + 1 < n),
      supInner (rotatedDirection θ) (S ⟨j, Nat.lt_of_succ_lt hj⟩) <
        infInner (rotatedDirection θ) (S ⟨j + 1, hj⟩)
end YangMills.Construction.ForwardTube
end
