import YangMills.Construction.Cumulants.NumberOfBlocksAndImagesOfPartitions
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SetPartition
def partitionSets {α : Type*} [DecidableEq α] (A : Finset α) : Set (Finset (Finset α)) :=
  Set.range fun π : Partitions A => π.parts
namespace Elementary
def SmallCases : Prop :=
  (∀ (α : Type) [DecidableEq α], partitionSets (∅ : Finset α) = {∅}) ∧
  partitionSets (Finset.univ : Finset (Fin 0)) = {∅} ∧
  Finpartition.parts '' (singletonFree 0 : Set (PartitionsFin 0)) = {∅} ∧
  singletonFree 1 = ∅ ∧
  ∀ (α : Type) [DecidableEq α] (l : α), partitionSets ({l} : Finset α) = {{{l}}}
def BlockFacts : Prop :=
  ∀ (α : Type) [DecidableEq α] (A : Finset α),
    (∀ π : Partitions A, ∀ l ∈ A, ∃! J, J ∈ π.parts ∧ l ∈ J) ∧
    (A ≠ ∅ → {A} ∈ partitionSets A ∧
      ∀ π : Partitions A, π.parts ≠ {A} → ∀ J ∈ π.parts, J ⊂ A)
def TransportUnderEquiv : Prop :=
  ∀ (α β : Type) [DecidableEq α] [DecidableEq β] (A : Finset α) (A' : Finset β) (ς : A ≃ A'),
    Set.BijOn (partitionImage ς) Set.univ (partitionSets A') ∧
    ∀ π : Partitions A,
      Set.BijOn (blockImage ς) (π.parts : Set (Finset α))
        (partitionImage ς π : Set (Finset β)) ∧
      (∀ J ∈ π.parts, (blockImage ς J).card = J.card) ∧
      (partitionImage ς π).card = blockCount π
def PermsPreservePartitions : Prop :=
  ∀ (q : ℕ), 1 ≤ q → ∀ ς : Equiv.Perm (Finset.univ : Finset (Fin q)),
    partitionImage ς '' Set.univ = partitionSets (Finset.univ : Finset (Fin q)) ∧
    partitionImage ς '' (singletonFree q : Set (PartitionsFin q)) =
      Finpartition.parts '' (singletonFree q : Set (PartitionsFin q))
def BasicFacts : Prop :=
  SmallCases ∧ BlockFacts ∧ TransportUnderEquiv ∧ PermsPreservePartitions
end Elementary
end YangMills.Construction.SetPartition
