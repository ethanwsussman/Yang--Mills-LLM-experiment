import YangMills.Construction.Continuum.SpacesOfTheRationalBoxesAndDenseFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Continuum.RationalBoxes
def IsSaturatedDenseInvariant (s : Conventions.StandingParameters)
    (D : boxUnions → Set ((Fin 4 → ℝ) → ℝ)) : Prop :=
  IsDenseInvariantFamily s D ∧ IsSaturatedFamily D
def chosenSaturatedFamily (s : Conventions.StandingParameters) :
    boxUnions → Set ((Fin 4 → ℝ) → ℝ) :=
  Classical.epsilon (IsSaturatedDenseInvariant s)
def ChosenFamilyIsSaturatedDense : Prop :=
  ∀ s : Conventions.StandingParameters, IsSaturatedDenseInvariant s (chosenSaturatedFamily s)
end YangMills.Construction.Continuum.RationalBoxes
