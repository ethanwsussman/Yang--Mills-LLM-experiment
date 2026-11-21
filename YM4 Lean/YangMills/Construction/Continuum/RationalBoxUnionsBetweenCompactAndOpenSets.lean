import YangMills.Construction.TestFunctions.RationalBoxFamilies
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set TestFunctions
namespace RatBoxSeparation
def separationClaim : Prop :=
  (ratBoxUnions.Countable ∧
    ∀ 𝓢 : Set (Set (Fin 4 → ℝ)), 𝓢.Finite → 𝓢 ⊆ ratBoxUnions →
      ⋃₀ 𝓢 ∈ ratBoxUnions) ∧
  (∀ (n : ℕ), 1 ≤ n → ∀ K U : Fin n → Set (Fin 4 → ℝ),
    (∀ i, IsCompact (K i)) → (Pairwise fun i j => Disjoint (K i) (K j)) →
    (∀ i, IsOpen (U i)) → (∀ i, K i ⊆ U i) →
    ∃ Q : Fin n → Set (Fin 4 → ℝ), (∀ i, Q i ∈ ratBoxUnions) ∧
      (Pairwise fun i j => Disjoint (Q i) (Q j)) ∧ ∀ i, K i ⊆ Q i ∧ Q i ⊆ U i) ∧
  (∀ Q ∈ ratBoxUnions, ∃ S : Set ((Fin 4 → ℝ) → ℝ),
    S ⊆ c1ZeroOff Q ∧ S.Countable ∧ IsDenseInC1ZeroOff Q S)
end RatBoxSeparation
end YangMills.Construction
