import YangMills.Construction.Continuum.ConnectedFunctionsOfARealFunctionByRecursion
import YangMills.Construction.Continuum.RulesOfTheOrthogonalAction
import YangMills.Construction.Continuum.SeparatedTuplesAsListsAndAsMaps
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.OrthogonalAction
open YangMills.Construction.Orthogonal YangMills.Construction.SeparatedTuples
open YangMills.Construction.SetPartition (PartitionsFin)
theorem eq_sum_partitions_prod_cumulant (σ : TestSpaces.SepTuple → ℝ) {n : ℕ} (hn : 1 ≤ n)
    (X : TestSpaces.SepTupleOfCard n) :
    σ ⟨n, X⟩ = ∑ P : PartitionsFin n, ∏ B ∈ P.parts,
      TestSpaces.cumulantRec σ B.card (TestSpaces.sepRestrict X B) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hne : (Finset.univ : Finset (Fin n)) ≠ ⊥ := Finset.univ_nonempty.ne_empty
  let P₀ : PartitionsFin n := Finpartition.indiscrete hne
  have hparts : P₀.parts = {Finset.univ} := rfl
  have hrest : (Finset.univ : Finset (PartitionsFin n)).erase P₀ =
      TestSpaces.properPartitions n := by
    ext P
    simp only [TestSpaces.properPartitions, Finset.mem_erase, Finset.mem_univ,
      and_true, Finset.mem_filter, true_and, ne_eq]
    exact not_congr ⟨fun hP => hP ▸ hparts, fun hP => Finpartition.ext (hP.trans hparts.symm)⟩
  have hone : TestSpaces.cumulantRec σ (Finset.univ : Finset (Fin n)).card
      (TestSpaces.sepRestrict X Finset.univ) = TestSpaces.cumulantRec σ n X :=
    congrArg (fun Y : TestSpaces.SepTuple => TestSpaces.cumulantRec σ Y.1 Y.2)
      (TestSpaces.sepRestrict_univ X)
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ P₀), hrest, hparts,
    Finset.prod_singleton, hone, TestSpaces.cumulantRec_eq σ X]
  ring
def cumulantAt (σ : TupleFunctional) (X : SepTuple) : ℝ :=
  TestSpaces.cumulantRec (fun Y => σ (TupleLists.toList Y)) (TupleLists.ofList X).1
    (TupleLists.ofList X).2
def singletonTuple (f : RealValued) (hf : IsC1c f) : SepTuple :=
  ⟨[f], by simpa [IsDisjointlySupported] using hf⟩
def CumulantsInvariant (σ : TupleFunctional) (Q : orthogonalGroupFour) : Prop :=
  σ.IsInvariant (matMap Q) →
    ∀ X : SepTuple, 1 ≤ X.size → cumulantAt σ (push (matMap Q) X) = cumulantAt σ X
def InvariantOfCumulants (σ : TupleFunctional) (Q : orthogonalGroupFour) : Prop :=
  (∃ c : ℝ, ∀ (f : RealValued) (hf : IsC1c f),
    cumulantAt σ (singletonTuple f hf) = σ (singletonTuple f hf) ∧
      σ (singletonTuple f hf) = c * ∫ x, f x) →
  (∀ X : SepTuple, 2 ≤ X.size →
    cumulantAt σ (push (matMap Q) X) = cumulantAt σ X) →
  σ.IsInvariant (matMap Q)
def OnePointIrrelevance : Prop :=
  ∀ (σ : TupleFunctional) (Q : orthogonalGroupFour),
    CumulantsInvariant σ Q ∧ InvariantOfCumulants σ Q
end YangMills.Construction.OrthogonalAction
