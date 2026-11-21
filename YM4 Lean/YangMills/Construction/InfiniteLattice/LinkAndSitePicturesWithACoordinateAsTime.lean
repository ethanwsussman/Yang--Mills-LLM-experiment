import YangMills.Construction.InfiniteLattice.SitePictures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open OneLoopNotation
namespace LatticeConventions
open InfiniteLattice (GaugeField localRegionObservables)
namespace SiteFrame
variable (a : Spacing)
def timeReflection : InfiniteLattice.LatticeSymmetry (a : ℝ) :=
  siteReflection a timeAxis
theorem timeReflection_toFun : (timeReflection a).toFun = siteReflectionMap timeAxis :=
  siteReflection_toFun a timeAxis
section TimeFrame
variable (ν : MeasureTheory.Measure (GaugeField (a : ℝ))) [MeasureTheory.IsProbabilityMeasure ν]
abbrev TimeSiteHilbertSpace : Type := SiteHilbertSpace a timeAxis ν
def timeClass (F : upperSpace a timeAxis) : TimeSiteHilbertSpace a ν :=
  siteClass a timeAxis ν F
def timeTransferOperator : BddOp (TimeSiteHilbertSpace a ν) :=
  transferOperator a timeAxis ν
def spatialShift (j : SpatialDirection) : BddOp (TimeSiteHilbertSpace a ν) :=
  transverseShift a timeAxis ν ⟨j.toDirection, (timeAxis_ne_toDirection j).symm⟩
end TimeFrame
end SiteFrame
end LatticeConventions
end YangMills.Construction
end
