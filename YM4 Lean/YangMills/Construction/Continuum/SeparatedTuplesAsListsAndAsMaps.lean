import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOfFourSpaceAndTheirFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TupleLists
theorem isDisjointlySupported_ofFn {n : ℕ} (X : TestSpaces.SepTupleOfCard n) :
    SeparatedTuples.IsDisjointlySupported (List.ofFn X.1) := by
  refine ⟨fun f hf => ?_, List.pairwise_ofFn.2 fun i j hij => X.2.2 hij.ne⟩
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
  obtain ⟨h₁, h₂, -⟩ := X.2.1 i
  exact ⟨h₁, h₂⟩
theorem get_mem_disjointSupportTuples (X : SeparatedTuples.SepTuple) :
    X.1.get ∈ TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) X.1.length := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · obtain ⟨h₁, h₂⟩ := X.2.1 _ (List.get_mem X.1 i)
    exact ⟨h₁, h₂, Set.subset_univ _⟩
  · have hp := List.pairwise_iff_get.1 X.2.2
    rcases lt_or_gt_of_ne hij with h | h
    · exact hp i j h
    · exact (hp j i h).symm
def toList (X : TestSpaces.SepTuple) : SeparatedTuples.SepTuple :=
  ⟨List.ofFn X.2.1, isDisjointlySupported_ofFn X.2⟩
def ofList (X : SeparatedTuples.SepTuple) : TestSpaces.SepTuple :=
  ⟨X.1.length, X.1.get, get_mem_disjointSupportTuples X⟩
theorem toList_ofList (X : SeparatedTuples.SepTuple) : toList (ofList X) = X :=
  Subtype.ext (List.ofFn_get X.1)
theorem ofList_toList (X : TestSpaces.SepTuple) : ofList (toList X) = X := by
  obtain ⟨n, Y⟩ := X
  exact TestSpaces.sepTuple_ext _ _ List.length_ofFn fun k => List.get_ofFn Y.1 k
def sepTupleEquivList : TestSpaces.SepTuple ≃ SeparatedTuples.SepTuple where
  toFun := toList
  invFun := ofList
  left_inv := ofList_toList
  right_inv := toList_ofList
theorem toList_sepTupleNil : toList TestSpaces.sepTupleNil = SeparatedTuples.SepTuple.nil :=
  Subtype.ext (by simp [toList, TestSpaces.sepTupleNil, SeparatedTuples.SepTuple.nil])
end TupleLists
end YangMills.Construction
