import YangMills.Construction.TorusOrFourSpace.DistributionsOfAHierarchyOnProductsAndDistinctPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
def EmptyMemberBoxProperties.Statement : Prop :=
  ∀ (D : Params) (E : Kind) (C : BoundFamily) (S : Hierarchy D E),
    S ∈ boundedHierarchies D E C → ∀ (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (R d : ℝ)
      (G : Fin (n : ℕ) → Set (E.Pt D)), AdmissibleWith D E R d G →
      (∃ i, G i = ∅) → S.BoxProperties C hn R d G
end YangMills.Construction.PeriodicSpace.Kind
