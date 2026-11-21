import YangMills.Construction.Conventions.ContinuumLimitsOfLatticeApproximationsDefs
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
noncomputable section
namespace Continuum.AxisPreservingSymmetries
open InfiniteLattice (AmbientSpace hyperoctahedralLinearGroup)
open LimitConventions
def timeBasisVector : AmbientSpace := Pi.single TimeAxis.timeIdx 1
def spatialSlice : Set AmbientSpace := range fun a : SpaceVec => mkPoint a 0
def PreservesTimeLine (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace) : Prop :=
  w '' TimeAxis.timeLine = TimeAxis.timeLine
def PreservesTimeLineFacts (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace) : Prop :=
  (w timeBasisVector = timeBasisVector ∨ w timeBasisVector = -timeBasisVector) ∧
  w '' spatialSlice = spatialSlice ∧
  (∀ a : SpaceVec, w (mkPoint a 0) = mkPoint (spatialRestriction w a) 0) ∧
  (∃ v ∈ octahedralGroup3, ⇑v = ⇑(spatialRestriction w) ∧
    (w timeBasisVector = timeBasisVector → w = timeExtension v) ∧
    (w timeBasisVector = -timeBasisVector →
      ⇑w = TimeAxis.timeReflection ∘ ⇑(timeExtension v))) ∧
  ∀ w' ∈ hyperoctahedralLinearGroup, PreservesTimeLine w' →
    PreservesTimeLine (w * w') ∧
      spatialRestriction (w * w') = spatialRestriction w ∘ₗ spatialRestriction w'
def Classification : Prop :=
  (∀ w ∈ octahedralGroup3, timeExtension w ∈ hyperoctahedralLinearGroup ∧
    timeExtension w timeBasisVector = timeBasisVector) ∧
  (∀ w ∈ octahedralGroup3, ∀ w' ∈ octahedralGroup3,
    ⇑(timeExtension (w * w')) = ⇑(timeExtension w) ∘ ⇑(timeExtension w')) ∧
  timeExtension 1 = 1 ∧
  (∀ w ∈ octahedralGroup3, timeExtension w⁻¹ = (timeExtension w)⁻¹) ∧
  (∀ w ∈ hyperoctahedralLinearGroup, PreservesTimeLine w → PreservesTimeLineFacts w) ∧
  spatialRestriction 1 = LinearMap.id ∧
  (∀ w ∈ octahedralGroup3, spatialRestriction (timeExtension w) = (w : SpaceVec →ₗ[ℝ] SpaceVec)) ∧
  (∀ w : AmbientSpace ≃ₗ[ℝ] AmbientSpace,
    (w ∈ hyperoctahedralLinearGroup ∧ w timeBasisVector = timeBasisVector) ↔
      ∃ v ∈ octahedralGroup3, w = timeExtension v) ∧
  ∀ w ∈ timeLineStabilizer, PreservesTimeLine w ∧ PreservesTimeLineFacts w
end Continuum.AxisPreservingSymmetries
end
end YangMills.Construction
