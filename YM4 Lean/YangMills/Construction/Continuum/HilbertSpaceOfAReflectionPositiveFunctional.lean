import YangMills.Construction.HilbertSpace.SemidefiniteFormHilbertSpace
import YangMills.Construction.ReflectionPositivity.PropertiesOfTheFormOfAFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositiveHilbert
variable (σ : SeparatedTuples.TupleFunctional)
abbrev StateSpace : Type :=
  FormCompletion.FormHilbertSpace (ReflectionPositivity.TupleForm.reflectionForm σ)
def stateOf (F : ReflectionPositivity.TupleForm.PositiveSpan) : StateSpace σ :=
  FormCompletion.classVec (ReflectionPositivity.TupleForm.reflectionForm σ) F
def vacuum : StateSpace σ :=
  stateOf σ ReflectionPositivity.FormProperties.unitSpan
end YangMills.Construction.ReflectionPositiveHilbert
end
