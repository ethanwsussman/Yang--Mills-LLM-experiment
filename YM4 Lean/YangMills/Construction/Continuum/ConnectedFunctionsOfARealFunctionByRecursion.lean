import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TestSpaces
open SetPartition
variable {n k : ℕ}
def properPartitions (n : ℕ) : Finset (PartitionsFin n) :=
  Finset.univ.filter fun π => π.parts ≠ {Finset.univ}
theorem card_lt_of_mem_properPartitions {π : PartitionsFin n}
    (hπ : π ∈ properPartitions n) {J : Finset (Fin n)} (hJ : J ∈ π.parts) :
    J.card < n := by
  by_contra hlt
  have hcard : J.card = Fintype.card (Fin n) := by
    have h := Finset.card_le_univ J
    simp only [Fintype.card_fin] at h ⊢
    omega
  have hJu : J = Finset.univ := (Finset.card_eq_iff_eq_univ J).1 hcard
  refine (Finset.mem_filter.1 hπ).2 (Finset.eq_singleton_iff_unique_mem.2 ⟨hJu ▸ hJ, fun K hK => ?_⟩)
  obtain ⟨a, ha⟩ := π.nonempty_of_mem_parts hK
  exact (π.eq_of_mem_parts hK hJ ha (hJu ▸ Finset.mem_univ a)).trans hJu
def cumulantRec (σ : SepTuple → ℝ) (n : ℕ) (X : SepTupleOfCard n) : ℝ :=
  σ ⟨n, X⟩ - ∑ π ∈ (properPartitions n).attach, ∏ J ∈ π.1.parts.attach,
    cumulantRec σ J.1.card (sepRestrict X J.1)
termination_by n
decreasing_by exact card_lt_of_mem_properPartitions π.2 J.2
theorem cumulantRec_eq (σ : SepTuple → ℝ) (X : SepTupleOfCard n) :
    cumulantRec σ n X = σ ⟨n, X⟩ - ∑ π ∈ properPartitions n,
      ∏ J ∈ π.parts, cumulantRec σ J.card (sepRestrict X J) := by
  rw [cumulantRec]
  congr 1
  refine Eq.trans ?_ (Finset.sum_attach _ fun π : PartitionsFin n =>
    ∏ J ∈ π.parts, cumulantRec σ J.card (sepRestrict X J))
  exact Finset.sum_congr rfl fun π _ => Finset.prod_attach π.1.parts fun J =>
    cumulantRec σ J.card (sepRestrict X J)
def SatisfiesCumulantRecursionAt (σ : SepTuple → ℝ) (X : SepTupleOfCard k) : Prop :=
  ∀ I : Finset (Fin k), I.Nonempty → σ ⟨I.card, sepRestrict X I⟩ =
    ∑ π : Partitions I, ∏ J ∈ π.parts, cumulantRec σ J.card (sepRestrict X J)
def centredOfRec (σ : SepTuple → ℝ) : SepTuple → ℝ :=
  centredOfCumulants fun m _ X => cumulantRec σ m X
end YangMills.Construction.TestSpaces
