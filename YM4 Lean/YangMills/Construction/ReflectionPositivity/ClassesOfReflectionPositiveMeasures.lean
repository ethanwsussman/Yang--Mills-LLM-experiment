import YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
open YangMills.Construction.InfiniteLattice (GaugeField LatticePoint IsSymmetricUnder
  IsShiftInvariant shift)
def unitPositiveClass : Set (Measure (GaugeField (1 : ℝ))) :=
  {ν | IsProbabilityMeasure ν ∧ IsShiftInvariant ν ∧
    ∀ P : UnitMirrorPair, IsReflectionPositiveAcross ν P}
def positiveClass (a : ℝ) : Set (Measure (GaugeField a)) :=
  {ν | IsProbabilityMeasure ν ∧ (∀ v : LatticePoint a, IsSymmetricUnder ν (shift v)) ∧
    ∀ P : MirrorPair a, IsReflectionPositiveAcross ν P}
end YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
