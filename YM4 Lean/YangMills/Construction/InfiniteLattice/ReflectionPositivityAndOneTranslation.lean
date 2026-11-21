import YangMills.Construction.InfiniteLattice.HilbertSpaceAtALatticeMirror
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAtAMirrorGivenWithANormal
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
namespace NormalHyperplane
open InfiniteLattice (GaugeField IsSymmetricUnder IsBoundedObservable LatticePoint
  localRegionObservables observableSupNorm shift)
open FormCompletion
variable {a : ℝ}
def FormPositiveAndSupBounded {Q : NormalHyperplane} (hQ : Q.IsLatticeMirror a)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν] : Prop :=
  IsPosSemidefHermitianForm (upperReflectionForm hQ ν) ∧
  ∀ F G : upperObservables a Q,
    ‖upperReflectionForm hQ ν F G‖ ^ 2 ≤
        (upperReflectionForm hQ ν F F).re * (upperReflectionForm hQ ν G G).re ∧
      (upperReflectionForm hQ ν F F).im = 0 ∧
      0 ≤ (upperReflectionForm hQ ν F F).re ∧
      (upperReflectionForm hQ ν F F).re ≤ observableSupNorm F.1 ^ 2
def IsReflectionPositiveOnLowerSide {Q : NormalHyperplane} (hQ : Q.IsLatticeMirror a)
    (ν : Measure (GaugeField a)) : Prop :=
  ∀ F ∈ localRegionObservables a Q.lowerHalfSpace,
    (∫ U, conjFun ((reflectSymmetry hQ).actOn F) U * F U ∂ν).im = 0 ∧
      0 ≤ (∫ U, conjFun ((reflectSymmetry hQ).actOn F) U * F U ∂ν).re
def ReflectedPairingBound {Q : NormalHyperplane} (hQ : Q.IsLatticeMirror a)
    (ν : Measure (GaugeField a)) : Prop :=
  ∀ F G : GaugeField a → ℂ, IsBoundedObservable F → IsBoundedObservable G →
    ‖∫ U, conjFun ((reflectSymmetry hQ).actOn F) U * G U ∂ν‖ ≤
      (∫ U, absFun F U ^ 2 ∂ν) ^ (1 / 2 : ℝ) *
        (∫ U, absFun G U ^ 2 ∂ν) ^ (1 / 2 : ℝ)
end NormalHyperplane
def ReflectionPositivityWithTranslation : Prop :=
  ∀ (a : Spacing) (Q : NormalHyperplane) (hQ : Q.IsLatticeMirror (a : ℝ))
    (ν : Measure (InfiniteLattice.GaugeField (a : ℝ))) [IsProbabilityMeasure ν],
    NormalHyperplane.IsReflectionPositiveAcrossMirror hQ ν →
      NormalHyperplane.FormPositiveAndSupBounded hQ ν ∧
      ∀ h : InfiniteLattice.LatticePoint (a : ℝ), h ≠ 0 → Q.reflectionLinear (h : Point) = -(h : Point) →
        InfiniteLattice.IsSymmetricUnder ν (InfiniteLattice.shift h) →
        InfiniteLattice.IsSymmetricUnder ν (NormalHyperplane.reflectSymmetry hQ) ∧
        NormalHyperplane.IsReflectionPositiveOnLowerSide hQ ν ∧
        NormalHyperplane.ReflectedPairingBound hQ ν
end LatticeConventions
end YangMills.Construction
end
