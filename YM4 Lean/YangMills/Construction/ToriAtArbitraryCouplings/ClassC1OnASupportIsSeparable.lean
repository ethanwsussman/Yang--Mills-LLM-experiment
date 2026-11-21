import YangMills.Construction.ToriAtArbitraryCouplings.ChoicesOfCountableDenseSets
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace C1SupportSeparable
def Statement : Prop :=
  ∀ (s : TorusSide) (E : Ambient) (Q : Set (s.Point E)), Q ∈ s.supportFamily E →
    ∃ A : Set (s.Point E → ℝ), A ⊆ s.c1VanishingOutside E Q ∧ A.Countable ∧
      s.IsC1DenseIn E Q A
end C1SupportSeparable
end YangMills.Construction.ToriAtArbitraryCouplings
end
