import YangMills.Construction.EuclideanFunctionals.ConeConditionAndPyramid
import YangMills.Construction.EuclideanFunctionals.JointSpectralMeasureOfASymmetricEuclideanFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
def tubeKernel (v : ℂ × ℂ) (p : MomSpace) : ℂ :=
  Complex.exp (-(v.1 * (energyCoord p : ℂ)) + Complex.I * v.2 * (momCoord 0 p : ℂ))
namespace SymmEuclidFunctional
variable {c : SharpScale} {S : ConnFamily} (σ : SymmEuclidFunctional c S)
def tubeOp (v : ℂ × ℂ) : σ.hilbertSpace →ₗ[ℂ] σ.hilbertSpace :=
  EuclideanSpectral.ProjMeasure.boundedIntegralOn σ.jointSpecMeasure momentumPyramid (tubeKernel v)
end SymmEuclidFunctional
end YangMills.Construction.EuclideanFunctionals
