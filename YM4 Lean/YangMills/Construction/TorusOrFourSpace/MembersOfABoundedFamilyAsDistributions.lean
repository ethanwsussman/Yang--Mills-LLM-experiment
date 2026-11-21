import YangMills.Construction.TorusOrFourSpace.DistributionsOfAHierarchyOnProductsAndDistinctPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
def BoundedHierarchyMembersAreDistributions : Prop :=
  ∀ (D : Params) (E : Kind) (C : BoundFamily) (H : Hierarchy D E),
    H ∈ boundedHierarchies D E C → ∀ (n : ℕ+) (hn : 2 ≤ (n : ℕ)),
      (∀ (R d : ℝ) (G : Fin (n : ℕ) → Set (E.Pt D)), AdmissibleWith D E R d G →
        H.BoxProperties C hn R d G) ∧
      Tuple.IsOpenT D E (pairwiseDistinct D E n) ∧
      (∀ G : Fin (n : ℕ) → Set (E.Pt D), Admissible D E G →
        Tuple.IsOpenT D E (Tuple.boxSet D E G) ∧
          Tuple.boxSet D E G ⊆ pairwiseDistinct D E n) ∧
      (∃! T, H.IsOffDiagDistrib hn T) ∧
      ∀ T, H.IsOffDiagDistrib hn T → H.OffDiagProperties hn T
end YangMills.Construction.PeriodicSpace.Kind
