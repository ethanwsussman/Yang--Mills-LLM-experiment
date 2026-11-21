import YangMills.Construction.ReflectionPositivity.SpectralVariablesOfTheTwoPictures
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
def siteCone (i : Fin 4) : Set (ℝ≥0∞ × (TransverseAxis i → ℝ)) :=
  {p | p ∈ variableDomain i ∧ ∀ l : TransverseAxis i,
    (1 - ((expNegEnergy p.1 : unitInterval) : ℝ)) ^ 2 ≥
      ((expNegEnergy p.1 : unitInterval) : ℝ) *
        ‖1 - Complex.exp (Complex.I * (p.2 l : ℂ))‖ ^ 2}
end YangMills.Construction.ReflectionPositivity.DirectionPictures
