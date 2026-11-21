import YangMills.Construction.EuclideanFunctionals.JointSpectralMeasureOfAReconstructionAndTheConeCondition
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
namespace SpectralPoint
def lightConePlus (p : EPlanePoints) : ℝ := 1 / 2 * (p.1 0 - p.1 1)
def lightConeMinus (p : EPlanePoints) : ℝ := 1 / 2 * (p.1 0 + p.1 1)
def planeExpKernel (v : ℂ × ℂ) (p : EPlanePoints) : ℂ :=
  Complex.exp (-(v.1 * (p.1 0 : ℂ)) + Complex.I * v.2 * (p.1 1 : ℂ))
end SpectralPoint
namespace EuclidFunctionalWithRecon
open HilbertSpaceBasics (UnboundedOp)
open SpectralPoint
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
def tubeOp (v : ℂ × ℂ) : UnboundedOp σ.space :=
  σ.planeMeasure.setIntegralOp wedge fun p => planeExpKernel v p.1
end EuclidFunctionalWithRecon
end YangMills.Construction.EuclideanFunctionals
