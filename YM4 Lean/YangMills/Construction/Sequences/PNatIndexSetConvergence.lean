import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Sequences
structure PNatIndexSet where
  carrier : Set ℕ+
  infinite : carrier.Infinite
namespace PNatIndexSet
def TendsTo (A : PNatIndexSet) (w : A.carrier → ℂ) (z : ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ+, ∀ j : A.carrier, N ≤ (j : ℕ+) → ‖w j - z‖ < ε
def HasLimit (A : PNatIndexSet) (w : A.carrier → ℂ) : Prop :=
  ∃ z : ℂ, A.TendsTo w z
theorem infinite_filter_ge (J : PNatIndexSet) (j₀ : ℤ) :
    {j ∈ J.carrier | j₀ ≤ (((j : ℕ+) : ℕ) : ℤ)}.Infinite := by
  have hfin : {j : ℕ+ | ¬ j₀ ≤ (((j : ℕ+) : ℕ) : ℤ)}.Finite := by
    refine ((Set.finite_lt_nat j₀.toNat).preimage
      (f := fun j : ℕ+ => (j : ℕ)) PNat.coe_injective.injOn).subset ?_
    intro j hj
    simp only [Set.mem_ofPred_eq, not_le] at hj
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    omega
  refine (J.infinite.sdiff hfin).mono ?_
  rintro j ⟨hJ, hj⟩
  simp only [Set.mem_ofPred_eq, not_not] at hj
  exact ⟨hJ, hj⟩
def filterGe (J : PNatIndexSet) (j₀ : ℤ) : PNatIndexSet where
  carrier := {j ∈ J.carrier | j₀ ≤ (((j : ℕ+) : ℕ) : ℤ)}
  infinite := J.infinite_filter_ge j₀
end PNatIndexSet
end YangMills.Construction.Sequences
