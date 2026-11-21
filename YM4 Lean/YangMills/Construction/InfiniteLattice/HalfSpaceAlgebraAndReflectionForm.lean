import YangMills.Construction.InfiniteLattice.TimeReflections
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def halfSpaceAbove (t : ℝ) : Set AmbientSpace := {x | t < x timeAxis}
def halfSpaceBelow (t : ℝ) : Set AmbientSpace := {x | x timeAxis < t}
def IsBoundedlyLocalizedIn (H : Set AmbientSpace) (A : GaugeField a → ℂ) : Prop :=
  IsBoundedObservable A ∧ ∃ S ⊆ H, Bornology.IsBounded S ∧ IsRegionMeasurable S A
def upperAlgebra (t : halfSpacingTimes a) : Set (GaugeField a → ℂ) :=
  {A | IsBoundedlyLocalizedIn (halfSpaceAbove t) A}
def reflectionPairing (μ : Measure (GaugeField a)) (t : halfSpacingTimes a)
    (B A : GaugeField a → ℂ) : ℂ :=
  ∫ U, conj ((timeReflect t).actOn B U) * A U ∂μ
def reflectionPairingRoot (μ : Measure (GaugeField a)) (t : halfSpacingTimes a)
    (A : GaugeField a → ℂ) : ℝ :=
  Real.sqrt (reflectionPairing μ t A A).re
def IsLocalizedAbove (t : halfSpacingTimes a) (A : GaugeField a → ℂ) : Prop := A ∈ upperAlgebra t
def IsLocalizedBelow (t : halfSpacingTimes a) (A : GaugeField a → ℂ) : Prop :=
  IsBoundedlyLocalizedIn (halfSpaceBelow t) A
end YangMills.Construction.InfiniteLattice
