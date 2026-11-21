import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOfFourSpaceAndTheirFunctionals
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.ForwardCone
open InfiniteLattice (AmbientSpace)
open SeparatedTuples
def timeZeroHyperplane : Mirrors.ReflectingHyperplane :=
  Mirrors.axialHyperplane TimeAxis.timeIdx 0
def IsRPTimeZero (σ : TupleFunctional) : Prop :=
  σ.IsReflectionPositive timeZeroHyperplane
end YangMills.Construction.ForwardCone
end
