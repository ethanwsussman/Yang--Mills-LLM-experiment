import YangMills.Construction.ToriAtArbitraryCouplings.ChoicesOfCountableDenseSets
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace C1SupportComplete
def Statement : Prop :=
  ∀ (s : TorusSide) (E : Ambient) (Q : Set (s.Point E)), Q ∈ s.supportFamily E →
    ∀ u : ℕ → s.Point E → ℝ, (∀ k, u k ∈ s.c1VanishingOutside E Q) →
      (∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ j k, K ≤ j → K ≤ k → s.c1NormOn E (u j - u k) < ε) →
      ∃ g ∈ s.c1VanishingOutside E Q, ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k, K ≤ k →
        s.c1NormOn E (u k - g) < ε
end C1SupportComplete
end YangMills.Construction.ToriAtArbitraryCouplings
end
