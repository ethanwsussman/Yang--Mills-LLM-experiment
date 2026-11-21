import YangMills.Construction.TorusOrFourSpace.DistributionsOfAHierarchyOnProductsAndDistinctPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
def OffDiagDistribUniqueInvariant : Prop :=
  ∀ (D : Params) (E : Kind) (C : BoundFamily) (S : Hierarchy D E),
    S ∈ boundedHierarchies D E C → ∀ (n : ℕ+) (hn : 2 ≤ (n : ℕ))
      (T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ),
      S.IsOffDiagDistrib hn T →
        (∀ T' : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ,
          Tuple.IsDistrib T' →
          (∀ f ∈ sepC1Tuples D E (n : ℕ), (∀ i, IsSmoothFn D E (f i)) →
            S.ValueAtTensor hn T' f) → T' = T) ∧
        ∀ ψ : TupleMap D E n, ψ.InvariantFunctional (S.func (n : ℕ) hn) →
          ψ.InvariantDistrib T
end YangMills.Construction.PeriodicSpace.Kind
