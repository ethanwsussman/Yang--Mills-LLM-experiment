import YangMills.Construction.InfiniteLattice.ThreeNamedSetsOfConditionsOnAState
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.LatticeConventions
namespace MirrorSideIndependence
open YangMills.Construction.InfiniteLattice (GaugeField localRegionObservables)
open NormalHyperplane
variable {a : ℝ}
def reflectedPairing {P : NormalHyperplane} (hP : P.IsLatticeMirror a)
    (ν : Measure (GaugeField a)) (f : GaugeField a → ℂ) : ℂ :=
  ∫ U, conjFun ((reflectSymmetry hP).actOn f) U * f U ∂ν
theorem reflectionForm_self_eq_reflectedPairing {P : NormalHyperplane} (hP : P.IsLatticeMirror a)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    (f : localRegionObservables a P.upperHalfSpace) :
    reflectionForm hP ν f f = reflectedPairing hP ν f.1 :=
  rfl
def ReflectBijOnHalfSpaces {P : NormalHyperplane} (hP : P.IsLatticeMirror a) : Prop :=
  Set.BijOn (fun f : GaugeField a → ℂ => (reflectSymmetry hP).actOn f)
    (localRegionObservables a P.lowerHalfSpace) (localRegionObservables a P.upperHalfSpace)
def ReflectedPairingsConj {P : NormalHyperplane} (hP : P.IsLatticeMirror a)
    (ν : Measure (GaugeField a)) : Prop :=
  ∀ f ∈ localRegionObservables a P.lowerHalfSpace,
    reflectedPairing hP ν f =
      (starRingEnd ℂ) (reflectedPairing hP ν ((reflectSymmetry hP).actOn f))
def IsLowerPositive {P : NormalHyperplane} (hP : P.IsLatticeMirror a)
    (ν : Measure (GaugeField a)) : Prop :=
  ∀ f ∈ localRegionObservables a P.lowerHalfSpace,
    (reflectedPairing hP ν f).im = 0 ∧ 0 ≤ (reflectedPairing hP ν f).re
def Statement : Prop :=
  ∀ a : Spacing,
    (∀ (P : NormalHyperplane) (hP : P.IsLatticeMirror (a : ℝ)),
      ReflectBijOnHalfSpaces hP ∧
        ∀ (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν],
          ReflectedPairingsConj hP ν ∧
            (IsReflectionPositiveAcrossMirror hP ν ↔ IsLowerPositive hP ν)) ∧
    (∀ (μ ρ : Direction) (hne : μ ≠ ρ) (c : ℝ), (∃ q : ℤ, c = (q : ℝ) * (a : ℝ)) →
      ∃ (hm : (antidiagonal μ ρ hne c).IsLatticeMirror (a : ℝ))
        (hm' : (antidiagonal ρ μ hne.symm (-c)).IsLatticeMirror (a : ℝ)),
        ∀ (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν],
          IsReflectionPositiveAcrossMirror hm ν ↔ IsReflectionPositiveAcrossMirror hm' ν) ∧
    ∀ (P P' : NormalHyperplane) (hP : P.IsLatticeMirror (a : ℝ))
      (hP' : P'.IsLatticeMirror (a : ℝ)), P.carrier = P'.carrier →
      ∀ (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν],
        IsReflectionPositiveAcrossMirror hP ν ↔ IsReflectionPositiveAcrossMirror hP' ν
end MirrorSideIndependence
end YangMills.Construction.LatticeConventions
end
