import YangMills.Construction.ToriAtArbitraryCouplings.ChoicesOfCountableDenseSets
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace C1NormOnSupport
def Statement : Prop :=
  ∀ (s : TorusSide) (E : Ambient) (Q : Set (s.Point E)), Q ∈ s.supportFamily E →
    (0 : s.Point E → ℝ) ∈ s.c1VanishingOutside E Q ∧
    (∀ f ∈ s.c1VanishingOutside E Q, ∀ g ∈ s.c1VanishingOutside E Q,
      f + g ∈ s.c1VanishingOutside E Q) ∧
    (∀ c : ℝ, ∀ f ∈ s.c1VanishingOutside E Q, c • f ∈ s.c1VanishingOutside E Q) ∧
    (∀ f ∈ s.c1VanishingOutside E Q, s.c1NormOn E f = 0 ↔ f = 0) ∧
    (∀ f ∈ s.c1VanishingOutside E Q, ∀ g ∈ s.c1VanishingOutside E Q,
      s.c1NormOn E (f + g) ≤ s.c1NormOn E f + s.c1NormOn E g) ∧
    ∀ c : ℝ, ∀ f ∈ s.c1VanishingOutside E Q, s.c1NormOn E (c • f) = |c| * s.c1NormOn E f
end C1NormOnSupport
end YangMills.Construction.ToriAtArbitraryCouplings
end
