import YangMills.Construction.TorusOrFourSpace.BoxesStockOfSupportsAndFamilyOfTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
def DisjointStockMembers.Statement : Prop :=
  ∀ (P : Params) (Y : Kind) (n : ℕ), 1 ≤ n →
    ∀ K W : Fin n → Set (Y.Pt P),
      (∀ i, IsCompactQ P Y (K i)) →
      Pairwise (fun i j => Disjoint (K i) (K j)) →
      (∀ i, IsOpenQ P Y (W i)) →
      (∀ i, K i ⊆ W i) →
      ∃ Q : Fin n → Set (Y.Pt P),
        (∀ i, Q i ∈ supportStock P Y) ∧
        Pairwise (fun i j => Disjoint (Q i) (Q j)) ∧
        ∀ i, K i ⊆ Q i ∧ Q i ⊆ W i
end YangMills.Construction.PeriodicSpace
