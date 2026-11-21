import YangMills.Construction.ComplexAnalysis.PartialDerivativesAndLogarithm
import YangMills.Construction.Cumulants.NumberOfBlocksAndImagesOfPartitions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Cumulants
open ComplexVariables SetPartition
abbrev NonemptyFinSubset (q : ℕ) : Type := {J : Finset (Fin q) // J.Nonempty}
abbrev SubsetFamily (q : ℕ) : Type := NonemptyFinSubset q → ℂ
variable {q : ℕ}
def blockSubset {J : Finset (Fin q)} (π : Partitions J) (B : π.parts) : NonemptyFinSubset q :=
  ⟨B.1, π.nonempty_of_mem_parts B.2⟩
def blockProduct {J : Finset (Fin q)} (a : SubsetFamily q) (π : Partitions J) : ℂ :=
  ∏ B : π.parts, a (blockSubset π B)
def multilinearPoly (k : SubsetFamily q) : Coordinates.ComplexCoordinates q → ℂ :=
  fun z => ∑ J : NonemptyFinSubset q, k J * ∏ l ∈ J.1, z l
def expDerivFamily (k : SubsetFamily q) : SubsetFamily q :=
  fun J => partialOverFinset J.1 (expComp (multilinearPoly k)) 0
def partitionSum (k : SubsetFamily q) : SubsetFamily q :=
  fun J => ∑ π : Partitions J.1, blockProduct k π
def moebiusPartitionSum (m : SubsetFamily q) : SubsetFamily q :=
  fun J => ∑ π : Partitions J.1,
    (-1 : ℂ) ^ (blockCount π - 1) * ((blockCount π - 1).factorial : ℂ) *
      blockProduct m π
def univSubset (hq : 1 ≤ q) : NonemptyFinSubset q :=
  ⟨Finset.univ, ⟨⟨0, hq⟩, Finset.mem_univ _⟩⟩
def PartitionSubstitutionsInverse : Prop :=
  ∀ (q : ℕ) (hq : 1 ≤ q),
    (∀ k : SubsetFamily q,
      multilinearPoly k 0 = 0 ∧
      (∀ J : NonemptyFinSubset q,
        HasPartialOverFinset Set.univ J.1 (multilinearPoly k) ∧
          partialOverFinset J.1 (multilinearPoly k) 0 = k J) ∧
      (∀ J : NonemptyFinSubset q,
        HasPartialOverFinset Set.univ J.1 (expComp (multilinearPoly k)) ∧
          expDerivFamily k J = partitionSum k J) ∧
      (∀ J : NonemptyFinSubset q, k J = moebiusPartitionSum (expDerivFamily k) J)) ∧
    (∀ m : SubsetFamily q, ∃! k : SubsetFamily q, partitionSum k = m) ∧
    Function.Bijective (partitionSum (q := q)) ∧
    Function.Bijective (moebiusPartitionSum (q := q)) ∧
    Function.LeftInverse (moebiusPartitionSum (q := q)) (partitionSum (q := q)) ∧
    Function.RightInverse (moebiusPartitionSum (q := q)) (partitionSum (q := q)) ∧
    (∀ k : SubsetFamily q, partitionSum k (univSubset hq) =
      ∑ π : PartitionsFin q, blockProduct k π) ∧
    (∀ m : SubsetFamily q, moebiusPartitionSum m (univSubset hq) =
      ∑ π : PartitionsFin q,
        (-1 : ℂ) ^ (blockCount π - 1) * ((blockCount π - 1).factorial : ℂ) *
          blockProduct m π)
end YangMills.Construction.Cumulants
