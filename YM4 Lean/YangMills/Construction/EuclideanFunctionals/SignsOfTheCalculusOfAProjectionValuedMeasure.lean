import YangMills.Construction.EuclideanFunctionals.JointSpectralMeasureOfAReconstructionAndTheConeCondition
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
namespace SpectralPoint
def energyMomentumPlane (x : EMPoints) : EPlanePoints :=
  ⟨![energyOf x, momentumOf x 0], mem_univ _⟩
theorem measurable_energyMomentumPlane : Measurable energyMomentumPlane := by
  refine Measurable.subtype_mk (measurable_pi_iff.mpr fun i => ?_)
  fin_cases i
  · exact measurable_energyOf
  · exact measurable_momentumOf_apply 0
end SpectralPoint
namespace EuclidFunctionalWithRecon
open YangMills.Construction.BorelSpectral YangMills.Construction.EuclideanFunctionals.SpectralPoint
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
def planeIntegralOp (g : EPlanePoints → ℂ) : σ.space →L[ℂ] σ.space :=
  σ.planeMeasure.integralOp g
def planeDiagMeasure (v : σ.space) : Measure EPlanePoints :=
  σ.planeMeasure.diagMeasure v
def wedgeOp (g : wedge.1 → ℂ) : σ.space →L[ℂ] σ.space :=
  σ.planeMeasure.integralOpOn wedge g
end EuclidFunctionalWithRecon
end YangMills.Construction.EuclideanFunctionals
