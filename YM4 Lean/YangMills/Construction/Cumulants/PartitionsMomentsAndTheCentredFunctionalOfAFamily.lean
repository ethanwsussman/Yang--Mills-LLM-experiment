import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace SetPartition
variable {α : Type*} [DecidableEq α]
def atLeastTwoPartitions (B : Finset α) : Finset (Partitions B) :=
  Finset.univ.filter fun π => ∀ J ∈ π.parts, 2 ≤ J.card
theorem mem_atLeastTwoPartitions {B : Finset α} {π : Partitions B} :
    π ∈ atLeastTwoPartitions B ↔ ∀ J ∈ π.parts, 2 ≤ J.card := by
  simp only [atLeastTwoPartitions, Finset.mem_filter, Finset.mem_univ, true_and]
theorem two_le_card_of_mem_atLeastTwoPartitions {B : Finset α} {π : Partitions B}
    (hπ : π ∈ atLeastTwoPartitions B) {J : Finset α} (hJ : J ∈ π.parts) :
    2 ≤ J.card :=
  mem_atLeastTwoPartitions.mp hπ J hJ
theorem atLeastTwoPartitions_empty :
    atLeastTwoPartitions (∅ : Finset α) = {⊥} := by
  ext π
  have h : ∀ π : Partitions (∅ : Finset α), π.parts = ∅ := parts_eq_empty_of_empty
  simp only [atLeastTwoPartitions, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, h π, Finset.notMem_empty, false_imp_iff, implies_true, true_iff]
  exact Finpartition.ext (by rw [h π, h ⊥])
theorem prod_parts_of_empty {M : Type*} [CommMonoid M] (π : Partitions (∅ : Finset α))
    (F : Finset α → M) : ∏ J ∈ π.parts, F J = 1 := by
  simp [parts_eq_empty_of_empty π]
theorem nonSingletonPartitions_eq_atLeastTwoPartitions (q : ℕ) :
    nonSingletonPartitions q = atLeastTwoPartitions (Finset.univ : Finset (Fin q)) := by
  ext π
  rw [mem_atLeastTwoPartitions]
  simp only [nonSingletonPartitions, Finset.mem_filter, Finset.mem_univ, true_and]
theorem atLeastTwoPartitions_univ (q : ℕ) :
    atLeastTwoPartitions (Finset.univ : Finset (Fin q)) =
      singletonFree q := by
  rw [singletonFree_eq_nonSingletonPartitions, nonSingletonPartitions_eq_atLeastTwoPartitions]
end SetPartition
namespace TestSpaces
open SetPartition
def blockProductSum (S : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ)
    (X : SepTuple) : ℝ :=
  ∑ π ∈ (atLeastTwoPartitions (Finset.univ : Finset (Fin X.1))).attach,
    ∏ J ∈ π.1.parts.attach,
      S J.1.card (two_le_card_of_mem_atLeastTwoPartitions π.2 J.2) (sepRestrict X.2 J.1)
theorem isPartition_parts {E : Type*} [Fintype E] [DecidableEq E]
    (π : Partitions (Finset.univ : Finset E)) : ClusterExpansion.SymGraph.IsPartition π.parts :=
  ⟨fun _ hb => π.nonempty_of_mem_parts hb, π.disjoint, by convert π.biUnion_parts⟩
def finpartitionOfIsPartition {E : Type*} [Fintype E] [DecidableEq E] {η : Finset (Finset E)}
    (h : ClusterExpansion.SymGraph.IsPartition η) : Partitions (Finset.univ : Finset E) where
  parts := η
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.2 h.2.1
  sup_parts := by rw [Finset.sup_eq_biUnion]; convert h.2.2
  bot_notMem := fun hb => by simpa using h.1 _ hb
theorem mem_partitionsNoSingletons_iff {E : Type*} [Fintype E] {η : Finset (Finset E)} :
    η ∈ partitionsNoSingletons E ↔
      ClusterExpansion.SymGraph.IsPartition η ∧ ∀ J ∈ η, 2 ≤ J.card := by
  simp only [partitionsNoSingletons, ClusterExpansion.SymGraph.partitions, Finset.mem_filter,
    Finset.mem_univ, true_and]
theorem parts_mem_partitionsNoSingletons {k : ℕ} {π : Partitions (Finset.univ : Finset (Fin k))}
    (hπ : π ∈ atLeastTwoPartitions (Finset.univ : Finset (Fin k))) :
    π.parts ∈ partitionsNoSingletons (Fin k) :=
  mem_partitionsNoSingletons_iff.mpr
    ⟨isPartition_parts π, fun _ hJ => two_le_card_of_mem_atLeastTwoPartitions hπ hJ⟩
theorem centredOfCumulants_eq_blockProductSum
    (S : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ) (X : SepTuple) :
    centredOfCumulants S X = blockProductSum S X := by
  symm
  refine Finset.sum_bij
    (fun π _ => (⟨π.1.parts, parts_mem_partitionsNoSingletons π.2⟩ :
      {η // η ∈ partitionsNoSingletons (Fin X.1)}))
    (fun _ _ => Finset.mem_attach _ _) (fun π _ π' _ h => ?_) (fun η _ => ?_)
    (fun _ _ => rfl)
  · exact Subtype.ext (Finpartition.ext (congrArg Subtype.val h))
  · obtain ⟨hset, h2⟩ := mem_partitionsNoSingletons_iff.mp η.2
    exact ⟨⟨finpartitionOfIsPartition hset, mem_atLeastTwoPartitions.mpr h2⟩,
      Finset.mem_attach _ _, Subtype.ext rfl⟩
end TestSpaces
end YangMills.Construction
end
