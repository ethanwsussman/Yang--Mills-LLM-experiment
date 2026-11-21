import YangMills.Construction.EuclideanFunctionals.JointSpectralMeasureOfAReconstructionAndTheConeCondition
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
namespace SpectralPoint
def spatialComplex (z : Fin 4 → ℂ) : Fin 3 → ℂ := fun j => z j.castSucc
def coneMargin (z : Fin 4 → ℂ) : ℝ := (z 3).re - ∑ j, |(spatialComplex z j).im|
def coneExp (z : Fin 4 → ℂ) (p : EMPoints) : ℂ :=
  Complex.exp (-(z 3 * (energyOf p : ℂ)) + Complex.I * ∑ j, spatialComplex z j * (momentumOf p j : ℂ))
theorem continuous_coneExp (z : Fin 4 → ℂ) : Continuous (coneExp z) := by
  have h : ∀ i : Fin 4, Continuous fun p : EMPoints => ((p.1 i : ℝ) : ℂ) := fun i =>
    Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_subtype_val)
  exact Complex.continuous_exp.comp (((continuous_const.mul (h 0)).neg).add
    (continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_const.mul (h j.succ))))
end SpectralPoint
namespace EuclidFunctionalWithRecon
open SpectralPoint
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
def coneOp (z : Fin 4 → ℂ) : σ.space →L[ℂ] σ.space :=
  σ.jointMeasure.integralOpOn pyramid fun p => coneExp z p.1
end EuclidFunctionalWithRecon
end YangMills.Construction.EuclideanFunctionals
