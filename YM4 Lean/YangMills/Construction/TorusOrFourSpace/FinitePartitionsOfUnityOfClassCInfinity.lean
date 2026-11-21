import YangMills.Construction.TorusOrFourSpace.TestFunctionsAndDistributionsOnASet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind Kind.Tuple
def SmoothFinitePartitionOfUnity : Prop :=
  ∀ (D : Params) (n A : ℕ+) (C : Set (euclidean.Tuple D n))
    (P : Fin (A : ℕ) → Set (euclidean.Tuple D n)),
    IsCompactT D euclidean C → (∀ a, IsOpenT D euclidean (P a)) → C ⊆ ⋃ a, P a →
    ∃ ψ : Fin (A : ℕ) → euclidean.Tuple D n → ℂ,
      (∀ a, ψ a ∈ testFns D euclidean (P a)) ∧
      ∃ N : Set (euclidean.Tuple D n),
        IsOpenT D euclidean N ∧ C ⊆ N ∧ ∀ y ∈ N, ∑ a, ψ a y = 1
end YangMills.Construction.PeriodicSpace
