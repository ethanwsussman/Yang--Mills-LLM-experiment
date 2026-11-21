import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open Matrix Set
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
abbrev FieldSpace (a : ℝ) : Type := GaugeField a
def regionObservables (a : ℝ) (S : Set AmbientSpace) : Set (FieldSpace a → ℂ) :=
  {A | IsBoundedObservable A ∧ IsRegionMeasurable S A}
def boundedSubsetObservables (a : ℝ) (S : Set AmbientSpace) : Set (FieldSpace a → ℂ) :=
  ⋃ T ∈ {T : Set AmbientSpace | T ⊆ S ∧ Bornology.IsBounded T}, regionObservables a T
def shiftMap (v : AmbientSpace) : AmbientSpace → AmbientSpace := fun x => x + v
def mirrorPlanes (a : ℝ) : Set (Set AmbientSpace) := range (LatticeMirror.plane (a := a))
end InfiniteLattice
end YangMills.Construction
