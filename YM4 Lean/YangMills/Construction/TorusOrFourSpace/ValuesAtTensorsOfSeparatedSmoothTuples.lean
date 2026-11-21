import YangMills.Construction.TorusOrFourSpace.DistributionsOfAHierarchyOnProductsAndDistinctPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
def SepSmoothTensorValues : Prop :=
  ∀ (P : Params) (K : Kind) (B : BoundFamily) (S : Hierarchy P K),
    S ∈ boundedHierarchies P K B → ∀ (n : ℕ+) (hn : 2 ≤ (n : ℕ))
      (T : Tuple.testFns P K (pairwiseDistinct P K n) → ℂ),
      S.IsOffDiagDistrib hn T →
        ∀ f ∈ sepC1Tuples P K (n : ℕ), (∀ i, IsSmoothFn P K (f i)) →
          S.ValueAtTensor hn T f
end YangMills.Construction.PeriodicSpace.Kind
