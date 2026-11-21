import YangMills.Construction.TorusOrFourSpace.AdicIsometriesInducedMapsAndActions
import YangMills.Construction.TorusOrFourSpace.ChoicesOfDenseSetsComponentsAndTheirFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (D : Params) (E : Kind)
def IsRatCombination {p : ℕ} (f : Fin p → E.Pt D → ℝ)
    (g : E.Pt D → ℝ) : Prop :=
  1 ≤ p ∧ ∃ c : Fin p → ℚ, g = ∑ i, (c i : ℝ) • f i
def HasClosedValues (C : supportStock D E → Set (E.Pt D → ℝ)) : Prop :=
  (∀ r : E.Pt D ≃ E.Pt D, ⇑r ∈ adicIsometriesQ D E →
    ∀ f ∈ choiceComponents D E C, pushFn D E r f ∈ choiceComponents D E C) ∧
  ∀ (p : ℕ) (f : Fin p → E.Pt D → ℝ) (g : E.Pt D → ℝ),
    (∀ i, f i ∈ choiceComponents D E C) → IsRatCombination D E f g →
      g ∈ choiceComponents D E C
def IsSaturated (C : supportStock D E → Set (E.Pt D → ℝ)) : Prop :=
  ∀ Q : supportStock D E, C Q = choiceComponents D E C ∩ c1VanishingOutside D E Q
end YangMills.Construction.PeriodicSpace.Kind
