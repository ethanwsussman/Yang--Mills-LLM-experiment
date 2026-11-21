import YangMills.Construction.TorusOrFourSpace.DistributionsOfAHierarchyOnProductsAndDistinctPoints
import YangMills.Construction.TorusOrFourSpace.FourKindsOfMapsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.SeparatedFamiliesOfOpenSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.HierarchyMembersAsDistributions
def Statement : Prop :=
  ∀ (D : Params) (E : Kind) (C : BoundFamily) (Φ : Hierarchy D E),
    Φ ∈ boundedHierarchies D E C → ∀ (n : ℕ+) (hn : 2 ≤ (n : ℕ)),
      (∀ (R d : ℝ) (G : Fin (n : ℕ) → Set (E.Pt D)), IsSeparatedWith D E R d G →
        Φ.BoxProperties C hn R d G) ∧
      (∃! T, Φ.IsOffDiagDistrib hn T) ∧
      (∀ T, Φ.IsOffDiagDistrib hn T →
        Φ.OffDiagProperties hn T ∧ Tuple.HasLocallyFiniteOrder T) ∧
      ∀ ψ : TupleMap D E n,
        Set.BijOn (ExtendedTupleMap.ofTupleMap ψ).actPts (pairwiseDistinct D E n)
            (pairwiseDistinct D E n) ∧
          ∀ F ∈ Tuple.testFns D E (pairwiseDistinct D E n),
            F ∘ (ExtendedTupleMap.ofTupleMap ψ).actPts ∈
              Tuple.testFns D E (pairwiseDistinct D E n)
end YangMills.Construction.PeriodicSpace.Kind.HierarchyMembersAsDistributions
