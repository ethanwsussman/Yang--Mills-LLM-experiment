import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SetPartition
variable {α : Type*} [DecidableEq α]
theorem exists_partition_parts_eq_iff {I : Finset α} {P : Finset (Finset α)} :
    (∃ π : Partitions I, π.parts = P) ↔
      (∀ J ∈ P, J.Nonempty ∧ J ⊆ I) ∧ (P : Set (Finset α)).PairwiseDisjoint id ∧
        P.biUnion id = I := by
  constructor
  · rintro ⟨π, rfl⟩
    refine ⟨fun J hJ => ⟨π.nonempty_of_mem_parts hJ, π.le hJ⟩, π.disjoint, ?_⟩
    rw [← Finset.sup_eq_biUnion]
    exact π.sup_parts
  · rintro ⟨hP, hd, hu⟩
    refine ⟨⟨P, Finset.supIndep_iff_pairwiseDisjoint.mpr hd, ?_, ?_⟩, rfl⟩
    · rw [Finset.sup_eq_biUnion]
      exact hu
    · intro h
      exact Finset.not_nonempty_empty (hP _ h).1
end YangMills.Construction.SetPartition
