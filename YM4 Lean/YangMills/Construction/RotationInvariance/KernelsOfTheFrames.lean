import YangMills.Construction.RotationInvariance.PlaneKernelsOfTheFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane ForwardTube
namespace EuclideanFunctionals
def frameKernel (S : ConnFamily) (θ : rightAngleMultiples) {q : ℕ}
    (φ : Fin (q + 1) → realLabels) (v : Fin q → ℂ × ℂ) : ℂ :=
  planeKernel S φ (unrotate θ v)
end EuclideanFunctionals
end YangMills.Construction
end
