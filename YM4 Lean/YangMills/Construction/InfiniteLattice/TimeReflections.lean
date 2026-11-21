import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
abbrev timeAxis : Fin 4 := 3
def halfSpacingTimes (a : ℝ) : Set ℝ := {t | ∃ m : ℤ, t = (m : ℝ) * (a / 2)}
variable {a : ℝ}
def equalTimeMirror (t : halfSpacingTimes a) : LatticeMirror a where
  cls := .axial timeAxis
  level := t
  level_mem := t.2
def timeReflect (t : halfSpacingTimes a) : LatticeSymmetry a := (equalTimeMirror t).symmetry
theorem timeReflect_apply (t : halfSpacingTimes a) (x : AmbientSpace) :
    (timeReflect t).toFun x =
      x - (2 * (x timeAxis - t)) • (Pi.single timeAxis 1 : AmbientSpace) := by
  have hnormal : (ReflectionClass.axial timeAxis).realNormal = Pi.single timeAxis 1 := by
    funext i
    by_cases hi : i = timeAxis
    · subst hi
      simp [ReflectionClass.realNormal, ReflectionClass.intNormal]
    · simp [ReflectionClass.realNormal, ReflectionClass.intNormal, Pi.single_eq_of_ne hi]
  change hyperplaneReflect (ReflectionClass.axial timeAxis).realNormal t x = _
  rw [hyperplaneReflect, ReflectionClass.realNormal_dot_axial, hnormal]
  simp
def originTime (a : ℝ) : halfSpacingTimes a := ⟨0, 0, by simp⟩
def timeReflectAtOrigin (a : ℝ) : LatticeSymmetry a := timeReflect (originTime a)
end YangMills.Construction.InfiniteLattice
