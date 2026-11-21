import YangMills.Construction.InfiniteLattice.FormAtALatticeMirrorGivenWithANormal
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.LatticeConventions
namespace NormalHyperplane
open YangMills.Construction.InfiniteLattice (GaugeField localRegionObservables)
variable {a : ℝ}
def IsReflectionPositiveAcrossMirror {Q : NormalHyperplane} (hQ : Q.IsLatticeMirror a)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν] : Prop :=
  ∀ F : localRegionObservables a Q.upperHalfSpace,
    (reflectionForm hQ ν F F).im = 0 ∧ 0 ≤ (reflectionForm hQ ν F F).re
def IsReflectionPositiveAcrossFamily (M : Set NormalHyperplane)
    (hM : ∀ Q ∈ M, Q.IsLatticeMirror a) (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν] : Prop :=
  ∀ Q (hQ : Q ∈ M), IsReflectionPositiveAcrossMirror (hM Q hQ) ν
end NormalHyperplane
end YangMills.Construction.LatticeConventions
end
