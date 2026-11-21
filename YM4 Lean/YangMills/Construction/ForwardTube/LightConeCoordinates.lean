import Mathlib
set_option autoImplicit false
open Complex ComplexConjugate
noncomputable section
namespace YangMills.Construction.ForwardTube
def lightConePlus (v : ℂ × ℂ) : ℂ := v.1 + I * v.2
def lightConeMinus (v : ℂ × ℂ) : ℂ := v.1 - I * v.2
def ofLightConeCoords (a b : ℂ) : ℂ × ℂ := (1 / 2 * (a + b), 1 / (2 * I) * (a - b))
theorem ofLightConeCoords_lightConePlus_lightConeMinus (v : ℂ × ℂ) :
    ofLightConeCoords (lightConePlus v) (lightConeMinus v) = v := by
  obtain ⟨x, y⟩ := v
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  simp only [ofLightConeCoords, lightConePlus, lightConeMinus, Prod.mk.injEq]
  constructor <;> field_simp <;> ring
theorem lightConePlus_ofLightConeCoords (a b : ℂ) : lightConePlus (ofLightConeCoords a b) = a := by
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  simp only [ofLightConeCoords, lightConePlus]
  field_simp
  ring
theorem lightConeMinus_ofLightConeCoords (a b : ℂ) : lightConeMinus (ofLightConeCoords a b) = b := by
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  simp only [ofLightConeCoords, lightConeMinus]
  field_simp
  ring
def realVectors : Set (ℂ × ℂ) := {v | v.1.im = 0 ∧ v.2.im = 0}
def forwardTube : Set (ℂ × ℂ) := {v | (lightConePlus v).re > 0 ∧ (lightConeMinus v).re > 0}
def tubeStar (v : ℂ × ℂ) : ℂ × ℂ := (conj v.1, -conj v.2)
def complexBoost (z : ℂ) (v : ℂ × ℂ) : ℂ × ℂ :=
  ofLightConeCoords (exp (I * z) * lightConePlus v) (exp (-(I * z)) * lightConeMinus v)
theorem lightConePlus_complexBoost (z : ℂ) (v : ℂ × ℂ) :
    lightConePlus (complexBoost z v) = exp (I * z) * lightConePlus v :=
  lightConePlus_ofLightConeCoords _ _
theorem lightConeMinus_complexBoost (z : ℂ) (v : ℂ × ℂ) :
    lightConeMinus (complexBoost z v) = exp (-(I * z)) * lightConeMinus v :=
  lightConeMinus_ofLightConeCoords _ _
end YangMills.Construction.ForwardTube
