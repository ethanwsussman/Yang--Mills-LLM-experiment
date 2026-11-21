import YangMills.Construction.Cumulants.NumberOfBlocksAndImagesOfPartitions
import YangMills.Construction.Cumulants.PartitionsMomentsAndTheCentredFunctionalOfAFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TestSpaces
open SetPartition
variable {n : ℕ}
def cumulantFamily (s : SepTuple → ℝ) : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ :=
  fun _ _ X => cumulant s X
theorem centredPart_eq_centredOfCumulants (s : SepTuple → ℝ) :
    centredPart s = centredOfCumulants (cumulantFamily s) :=
  rfl
theorem cumulant_eq_sum_partitions (s : SepTuple → ℝ) (X : SepTupleOfCard n) :
    cumulant s X = ∑ π : Partitions (Finset.univ : Finset (Fin n)),
      (-1 : ℝ) ^ (blockCount π - 1) * ((blockCount π - 1).factorial : ℝ) *
        ∏ B ∈ π.parts, s ⟨B.card, sepRestrict X B⟩ := by
  symm
  refine Finset.sum_bij (fun π _ => π.parts) (fun π _ => ?_)
    (fun π _ π' _ h => Finpartition.ext h) (fun η hη => ?_) (fun _ _ => rfl)
  · simp only [ClusterExpansion.SymGraph.partitions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact isPartition_parts π
  · have h : ClusterExpansion.SymGraph.IsPartition η := by
      simpa only [ClusterExpansion.SymGraph.partitions, Finset.mem_filter, Finset.mem_univ,
        true_and] using hη
    exact ⟨finpartitionOfIsPartition h, Finset.mem_univ _, rfl⟩
theorem centredPart_eq_sum_atLeastTwoPartitions (s : SepTuple → ℝ) (X : SepTupleOfCard n) :
    centredPart s ⟨n, X⟩ = ∑ π ∈ atLeastTwoPartitions (Finset.univ : Finset (Fin n)),
      ∏ B ∈ π.parts, cumulant s (sepRestrict X B) := by
  rw [centredPart_eq_centredOfCumulants, centredOfCumulants_eq_blockProductSum,
    blockProductSum]
  refine Eq.trans ?_ (Finset.sum_attach _ _)
  exact Finset.sum_congr rfl fun π _ =>
    Finset.prod_attach π.1.parts fun B => cumulant s (sepRestrict X B)
def singletonSepTuple (f : (Fin 4 → ℝ) → ℝ) (hf : f ∈ c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) :
    SepTupleOfCard 1 :=
  ⟨fun _ => f, fun _ => hf, fun i j h => absurd (Subsingleton.elim i j) h⟩
def cumulantOne (s : SepTuple → ℝ) (f : (Fin 4 → ℝ) → ℝ)
    (hf : f ∈ c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) : ℝ :=
  cumulant s (singletonSepTuple f hf)
end YangMills.Construction.TestSpaces
end
