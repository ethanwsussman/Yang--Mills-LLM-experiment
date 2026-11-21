import YangMills.Construction.TorusOrFourSpace.DistributionsOfAHierarchyOnProductsAndDistinctPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
def OffDiagDistribGluing : Prop :=
  ∀ (D : Params) (E : Kind) (C : BoundFamily) (S : Hierarchy D E),
    S ∈ boundedHierarchies D E C → ∀ (n : ℕ+) (hn : 2 ≤ (n : ℕ)),
      (∃! T, S.IsOffDiagDistrib hn T) ∧
      ∀ T, S.IsOffDiagDistrib hn T →
        (∀ G : Fin (n : ℕ) → Set (E.Pt D), Admissible D E G →
          ∃ h : Tuple.boxSet D E G ⊆ pairwiseDistinct D E n,
            Tuple.IsDistribOfOrderLE (5 * (n : ℕ) + 1)
              (Tuple.restrictDistrib h T)) ∧
        Tuple.IsDistribOfOrderLE (5 * (n : ℕ) + 1) T
end YangMills.Construction.PeriodicSpace.Kind
