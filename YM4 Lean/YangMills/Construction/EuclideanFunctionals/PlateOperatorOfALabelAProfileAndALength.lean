import YangMills.Construction.EuclideanFunctionals.BoundedOperatorOfOnePlate
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RealPlane
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
variable {m : SharpScale} {S : ConnFamily}
def productOperator (σ : EuclidFunctionalWithRecon m S) (φ : RealPlane → ℝ)
    (α : RealPlane → ℂ) (η : ℝ) : σ.space →L[ℂ] σ.space :=
  Classical.epsilon (ProductInsertionOp.ActsOnReconClasses σ η α φ)
end YangMills.Construction.EuclideanFunctionals
