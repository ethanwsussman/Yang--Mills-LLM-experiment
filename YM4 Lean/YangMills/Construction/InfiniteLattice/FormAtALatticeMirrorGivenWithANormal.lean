import YangMills.Construction.InfiniteLattice.LinkSupportAndRegionObservables
import YangMills.Construction.InfiniteLattice.ReflectionInALatticeMirrorGivenWithANormal
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
namespace NormalHyperplane
open YangMills.Construction.InfiniteLattice (GaugeField localRegionObservables)
variable {a : ℝ}
def reflectionForm {Q : NormalHyperplane} (hQ : Q.IsLatticeMirror a)
    (μ : Measure (GaugeField a)) [IsProbabilityMeasure μ]
    (F G : localRegionObservables a Q.upperHalfSpace) : ℂ :=
  ∫ U, conjFun ((reflectSymmetry hQ).actOn F.1) U * G.1 U ∂μ
end NormalHyperplane
end LatticeConventions
end YangMills.Construction
end
