import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def axialMirrorAtOrigin (a : ℝ) (μ : Fin 4) : LatticeMirror a :=
  ⟨.axial μ, 0, 0, by simp⟩
def axialReflection (a : ℝ) (μ : Fin 4) : LatticeSymmetry a :=
  (axialMirrorAtOrigin a μ).symmetry
theorem axialReflection_toFun (μ : Fin 4) (x : AmbientSpace) :
    (axialReflection a μ).toFun x = x - (2 * x μ) • (Pi.single μ 1 : AmbientSpace) := by
  have hn : (ReflectionClass.axial μ).realNormal = (Pi.single μ 1 : AmbientSpace) := by
    funext κ
    by_cases h : κ = μ
    · subst h
      simp [ReflectionClass.realNormal, ReflectionClass.intNormal]
    · simp [ReflectionClass.realNormal, ReflectionClass.intNormal, Pi.single_eq_of_ne h]
  change hyperplaneReflect (ReflectionClass.axial μ).realNormal 0 x = _
  rw [hyperplaneReflect, ReflectionClass.realNormal_dot_axial, hn]
  simp
end InfiniteLattice
end YangMills.Construction
end
