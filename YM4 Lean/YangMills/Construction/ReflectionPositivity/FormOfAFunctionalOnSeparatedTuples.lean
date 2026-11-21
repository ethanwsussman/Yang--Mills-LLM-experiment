import YangMills.Construction.HilbertSpace.FormsAndOperators
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOfFourSpaceAndTheirFunctionals
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace ReflectionPositivity.TupleForm
open SeparatedTuples
open InfiniteLattice (AmbientSpace)
abbrev PositiveSpan : Type := spanIn TimeAxis.upperHalfSpace
def reflectConj (F : PositiveSpan) : FormalSpan :=
  pushSpan TimeAxis.timeReflection (conjugation F.1)
variable (σ : TupleFunctional)
def reflectionForm (F F' : PositiveSpan) : ℂ :=
  σ.spanExtension (formalMul (reflectConj F) F'.1)
theorem isSesquilinear_reflectionForm : HilbertSpaceBasics.IsSesquilinear (reflectionForm σ) where
  add_left F₁ F₂ F' := by simp [reflectionForm, reflectConj, map_add, LinearMap.add_apply]
  smul_left z F F' := by simp [reflectionForm, reflectConj, map_smulₛₗ, LinearMap.smul_apply]
  add_right F F₁ F₂ := by simp [reflectionForm, map_add]
  smul_right z F F' := by simp [reflectionForm, map_smul]
def reflectedCorrelation (F : PositiveSpan) (v : AmbientSpace) : ℂ :=
  σ.spanExtension (formalMul (reflectConj F) (pushSpan (translate v) F.1))
end ReflectionPositivity.TupleForm
end YangMills.Construction
