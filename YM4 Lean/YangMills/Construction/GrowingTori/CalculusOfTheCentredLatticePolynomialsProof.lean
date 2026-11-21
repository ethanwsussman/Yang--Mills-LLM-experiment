import YangMills.Construction.Cumulants.PartitionsMomentsAndTheCentredFunctionalOfAFamily
import YangMills.Construction.GrowingTori.CalculusOfTheCentredLatticePolynomials
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ToriLimits.LatticePolynomialCalculus
open CentredTensorMoments
open BallTuples (FnTuple subTupleOn)
open SetPartition
theorem partitionSum_connected_eq_centred (D : Setup) (K m : ℕ+) (β : ℝ) (hβ : 0 < β) {q : ℕ}
    (X : FnTuple q) :
    ∑ π ∈ singletonFree q, ∏ J ∈ π.parts,
        BallTuples.connectedFn (D.momentSetup K m β hβ).toParams K β (subTupleOn X J) =
      D.centredOnFourSpace K m β X := by
  match q, X with
  | 0, X =>
    have hzero : singletonFree 0 = {⊥} := by
      rw [← atLeastTwoPartitions_univ]
      exact atLeastTwoPartitions_empty (α := Fin 0)
    rw [hzero, Finset.sum_singleton]
    exact prod_parts_of_empty (α := Fin 0) _ _
  | 1, X =>
    rw [← atLeastTwoPartitions_univ]
    refine Finset.sum_eq_zero fun π hπ => ?_
    exfalso
    obtain ⟨J, hJ, -⟩ := π.exists_mem (Finset.mem_univ (0 : Fin 1))
    have htwo := mem_atLeastTwoPartitions.1 hπ J hJ
    have hone : J.card ≤ 1 := by simpa using J.card_le_univ
    omega
  | q + 2, X =>
    rw [← atLeastTwoPartitions_univ]
    change _ = SchwingerFunctions.partitionSum (fun _ g => SchwingerFunctions.connectedSchwinger D.L m K β g)
      (SchwingerFunctions.periodizeAll D.L m X)
    unfold SchwingerFunctions.partitionSum
    exact Finset.sum_congr (by ext π; simp [mem_atLeastTwoPartitions])
      fun π _ => rfl
theorem holds_of_torusFunctionals (h : TorusFunctionals.Statement) : Holds := by
  intro D K m β hβ
  obtain ⟨-, hM, hC, -, -⟩ :=
    h (D.momentSetup K m β hβ) (D.latticeRadius m) (D.isRadius_latticeRadius K m β hβ)
  refine ⟨hC.map_linComb, hC.mul_eq, hC.conj_eq, hC.tensor_eq, ?_⟩
  intro q n c X hX
  rw [Setup.tensorMoment_eq_centredTensorMoment, ← hC.moment_linComb q n c X hX]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hM q (X b) (hX b), partitionSum_connected_eq_centred D K m β hβ (X b)]
end YangMills.Construction.ToriLimits.LatticePolynomialCalculus
end
