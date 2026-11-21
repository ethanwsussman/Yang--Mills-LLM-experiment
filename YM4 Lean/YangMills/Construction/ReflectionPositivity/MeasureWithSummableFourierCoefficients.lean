import YangMills.Construction.ReflectionPositivity.SpectralVariablesAsASpaceAndTheMomentumTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Real
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.EnergyMomentum
open YangMills.Construction.ReflectionPositivity.DirectionPictures (angleDot)
variable (μ : Fin 4)
def torusCharacter (w : orthLattice μ) (η : DualTorus μ) : ℂ :=
  Complex.exp (Complex.I * (angleDot μ (boxRep μ η) (w : Fin 4 → ℤ) : ℂ))
def torusFourierCoeff (M : Measure (DualTorus μ)) (w : orthLattice μ) : ℂ :=
  ∫ η, torusCharacter μ w η ∂M
def torusFourierTerm (M : Measure (DualTorus μ)) (w : orthLattice μ)
    (η : DualTorus μ) : ℂ :=
  torusFourierCoeff μ M w *
    Complex.exp (-(Complex.I * (angleDot μ (boxRep μ η) (w : Fin 4 → ℤ) : ℂ)))
def torusFourierSeries (M : Measure (DualTorus μ)) (η : DualTorus μ) : ℂ :=
  (((2 * π) ^ 3)⁻¹ : ℝ) * ∑' w, torusFourierTerm μ M w η
def SummableFourierCoeffTheorem : Prop :=
  ∀ (μ : Fin 4) (M : Measure (DualTorus μ)) [IsFiniteMeasure M],
    Summable (fun w => ‖torusFourierCoeff μ M w‖) →
    (∀ η, Summable fun w => ‖torusFourierTerm μ M w η‖) ∧
    TendstoUniformly
      (fun (s : Finset (orthLattice μ)) (η : DualTorus μ) =>
        (((2 * π) ^ 3)⁻¹ : ℝ) * ∑ w ∈ s, torusFourierTerm μ M w η)
      (torusFourierSeries μ M) atTop ∧
    Continuous (torusFourierSeries μ M) ∧
    M = (torusMeasure μ).withDensity (fun η => ENNReal.ofReal (torusFourierSeries μ M η).re) ∧
    ∀ η, (torusFourierSeries μ M η).im = 0 ∧ 0 ≤ (torusFourierSeries μ M η).re ∧
      (torusFourierSeries μ M η).re ≤ ((2 * π) ^ 3)⁻¹ * ∑' w, ‖torusFourierCoeff μ M w‖
end YangMills.Construction.ReflectionPositivity.EnergyMomentum
