import YangMills.Construction.Continuum.RationalBoxesAndSaturatedFamilies
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.Continuum.RationalBoxes
def DisjointUnionsBetweenCompactAndOpen : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ A O : Fin k → Set (Fin 4 → ℝ),
    (∀ i, IsCompact (A i)) → (Pairwise fun i j => Disjoint (A i) (A j)) →
    (∀ i, IsOpen (O i)) → (∀ i, A i ⊆ O i) →
    ∃ Q : Fin k → Set (Fin 4 → ℝ), (∀ i, Q i ∈ boxUnions) ∧
      (Pairwise fun i j => Disjoint (Q i) (Q j)) ∧ ∀ i, A i ⊆ Q i ∧ Q i ⊆ O i
end YangMills.Construction.Continuum.RationalBoxes
