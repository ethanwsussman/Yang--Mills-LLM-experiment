import YangMills.Construction.EuclideanFunctionals.JointSpectralMeasureOfAReconstructionAndTheConeCondition
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
open BorelSpectral
namespace EuclidFunctionalWithRecon
open SpectralPoint
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
def pairSpectralMeasure (φ ψ : σ.space) (D : BorelSubsets EMPoints) : ℂ :=
  σ.jointMeasure.matrixCoeff φ ψ D
def spatialShiftOp (v : Fin 3 → ℝ) : σ.space →L[ℂ] σ.space :=
  spatialTranslOp σ.jointMeasure (Fin.snoc (α := fun _ => ℝ) v 0)
end EuclidFunctionalWithRecon
end YangMills.Construction.EuclideanFunctionals
