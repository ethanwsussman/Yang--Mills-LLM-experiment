import YangMills.Construction.ToriAtArbitraryCouplings.TheCountableFamilyOfSupportsAndCharts
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace SupportsBetweenCompactOpen
def Statement : Prop :=
  ∀ (s : TorusSide) (E : Ambient),
    (∀ K U : Set (s.Point E), s.IsCompactWrt E K → s.IsOpenWrt E U → K ⊆ U →
      ∃ Q ∈ s.supportFamily E, K ⊆ Q ∧ Q ⊆ U) ∧
    ∀ (n : ℕ) (K U : Fin n → Set (s.Point E)), (∀ i, s.IsCompactWrt E (K i)) →
      Pairwise (Function.onFun Disjoint K) → (∀ i, s.IsOpenWrt E (U i)) → (∀ i, K i ⊆ U i) →
      ∃ Q : Fin n → Set (s.Point E), (∀ i, Q i ∈ s.supportFamily E) ∧ (∀ i, K i ⊆ Q i ∧ Q i ⊆ U i) ∧
        Pairwise (Function.onFun Disjoint Q)
end SupportsBetweenCompactOpen
end YangMills.Construction.ToriAtArbitraryCouplings
end
