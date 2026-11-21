import YangMills.Construction.EuclideanFunctionals.JointSpectralMeasureOfAReconstructionAndTheConeCondition
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
open YangMills.Construction.BorelSpectral
namespace SpectralPoint
def ltAbsMomentumSet (j : Fin 3) : BorelSubsets EMPoints :=
  ⟨{p | energyOf p < |momentumOf p j|},
    measurableSet_lt measurable_energyOf (measurable_momentumOf_apply j).abs⟩
end SpectralPoint
namespace EuclidFunctionalWithRecon.CarriedByPyramid
open SpectralPoint
def statement : Prop :=
  ∀ {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S),
    σ.ConeCondition →
    (∀ j : Fin 3, σ.HamGeAbsMomentum j ∧
      σ.jointMeasure (ltAbsMomentumSet j) = 0) ∧
    σ.jointMeasure.IsCarriedBy pyramid ∧
    (∀ p ∈ pyramid.1, ∀ u : Fin 3 → ℝ,
      |dot3 u (SpectralPoint.momentumOf p)| ≤ SpectralPoint.energyOf p * ∑ j, |u j|) ∧
    ∀ p ∈ pyramid.1, ∀ z : Fin 4 → ℂ,
      ‖Complex.exp (-(z 3 * (SpectralPoint.energyOf p : ℂ)) +
          Complex.I * ∑ j : Fin 3, z j.castSucc * (SpectralPoint.momentumOf p j : ℂ))‖ =
        Real.exp (-(SpectralPoint.energyOf p * (z 3).re) -
          ∑ j : Fin 3, SpectralPoint.momentumOf p j * (z j.castSucc).im) ∧
      Real.exp (-(SpectralPoint.energyOf p * (z 3).re) -
          ∑ j : Fin 3, SpectralPoint.momentumOf p j * (z j.castSucc).im) ≤
        Real.exp (-(SpectralPoint.energyOf p * ((z 3).re - ∑ j : Fin 3, |(z j.castSucc).im|))) ∧
      (∑ j : Fin 3, |(z j.castSucc).im| ≤ (z 3).re →
        Real.exp (-(SpectralPoint.energyOf p * ((z 3).re - ∑ j : Fin 3, |(z j.castSucc).im|))) ≤ 1)
end EuclidFunctionalWithRecon.CarriedByPyramid
end YangMills.Construction.EuclideanFunctionals
