import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def LatticeMirror.halfSpaces (P : LatticeMirror a) : Set (Set AmbientSpace) :=
  {H | P.IsHalfSpace H}
def ReflectionPositiveAtMirror (ν : Measure (GaugeField a)) (P : LatticeMirror a) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ A : GaugeField a → ℂ, IsBoundedObservable A → IsLocalObservable A →
    (∃ H ∈ P.halfSpaces, IsRegionMeasurable H A) →
      0 ≤ ∫ U, A U * conj (P.symmetry.actOn A U) ∂ν
end YangMills.Construction.InfiniteLattice
end
