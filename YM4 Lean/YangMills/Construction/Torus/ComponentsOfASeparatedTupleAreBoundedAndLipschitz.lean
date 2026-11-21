import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror (Ambient)
namespace AmbientPoints
def SepTupleEntriesBoundedLipschitz : Prop :=
  ∀ (s : Conventions.StandingParameters) (E : Ambient) (n : ℕ), ∀ f ∈ sepTuples s E n, ∀ i,
    TestFunctions.IsBoundedFun (f i) ∧ TestFunctions.IsLipschitzFor (pointDist s E) (f i)
end AmbientPoints
end YangMills.Construction
