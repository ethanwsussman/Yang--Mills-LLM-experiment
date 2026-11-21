import YangMills.Construction.EuclideanFunctionals.SymmetricEuclideanFunctional
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.FiniteMeasureUniqueness
def laplaceFourierKernel (t : ℕ) (v : EuclideanSpace ℝ (Fin 3)) (p : MomSpace) : ℂ :=
  Complex.exp (-(t : ℂ) * (energyCoord p : ℂ) +
    Complex.I * ((∑ j : Fin 3, v j * momCoord j p : ℝ) : ℂ))
def TransformDeterminesMeasure : Prop :=
  ∀ (μ μ' : Measure MomSpace) [IsFiniteMeasure μ] [IsFiniteMeasure μ'],
    μ negEnergySet.1 = 0 → μ' negEnergySet.1 = 0 →
    (∀ (t : ℕ) (v : EuclideanSpace ℝ (Fin 3)),
      ∫ p in nonnegEnergySet.1, laplaceFourierKernel t v p ∂μ =
        ∫ p in nonnegEnergySet.1, laplaceFourierKernel t v p ∂μ') →
    μ = μ'
end YangMills.Construction.EuclideanFunctionals.FiniteMeasureUniqueness
