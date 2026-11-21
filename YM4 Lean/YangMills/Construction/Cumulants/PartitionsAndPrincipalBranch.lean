import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Cumulants
variable {α : Type*} [DecidableEq α]
structure IsFinsetPartition (A : Finset α) (P : Finset (Finset α)) : Prop where
  nonempty : ∀ J ∈ P, J.Nonempty
  subset : ∀ J ∈ P, J ⊆ A
  pairwiseDisjoint : (P : Set (Finset α)).PairwiseDisjoint id
  union : P.biUnion id = A
open Classical in
def finsetPartitions (A : Finset α) : Finset (Finset (Finset α)) :=
  A.powerset.powerset.filter (IsFinsetPartition A)
def blockCount (P : Finset (Finset α)) : ℕ := P.card
def partitionsIcc (n : ℕ) : Finset (Finset (Finset ℕ)) :=
  finsetPartitions (Finset.Icc 1 n)
theorem mem_finsetPartitions {A : Finset α} {P : Finset (Finset α)} :
    P ∈ finsetPartitions A ↔ IsFinsetPartition A P := by
  classical
  simp only [finsetPartitions, Finset.mem_filter, Finset.mem_powerset, and_iff_right_iff_imp]
  intro h J hJ
  exact Finset.mem_powerset.2 (h.subset J hJ)
end YangMills.Construction.Cumulants
