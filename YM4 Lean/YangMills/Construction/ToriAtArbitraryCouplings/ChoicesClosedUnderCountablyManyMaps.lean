import YangMills.Construction.ToriAtArbitraryCouplings.ChoicesOfCountableDenseSets
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace ChoicesStableUnderCountableMaps
def Statement : Prop :=
  ∀ (s : TorusSide) (E : Ambient) (G : Set (Equiv.Perm (s.Point E))), G.Countable →
    (∀ r ∈ G, ∀ Q ∈ s.supportFamily E, ∃ Q' ∈ s.supportFamily E,
      ∀ f ∈ s.c1VanishingOutside E Q, f ∘ r.symm ∈ s.c1VanishingOutside E Q') →
    ∃ D : s.supportFamily E → Set (s.Point E → ℝ), s.IsCountableC1DenseChoice E D ∧
      (∀ r ∈ G, ∀ f ∈ ⋃ Q, D Q, f ∘ r.symm ∈ ⋃ Q, D Q) ∧
      (∀ (n : ℕ) (c : Fin n → ℚ) (f : Fin n → s.Point E → ℝ), (∀ i, f i ∈ ⋃ Q, D Q) →
        (∑ i, (c i : ℝ) • f i) ∈ ⋃ Q, D Q) ∧
      ∀ Q : s.supportFamily E, D Q = (⋃ Q', D Q') ∩ s.c1VanishingOutside E Q.1
end ChoicesStableUnderCountableMaps
end YangMills.Construction.ToriAtArbitraryCouplings
end
