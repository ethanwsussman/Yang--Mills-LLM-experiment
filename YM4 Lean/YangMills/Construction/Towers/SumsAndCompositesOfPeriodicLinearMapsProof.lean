import YangMills.Construction.Towers.SumsAndCompositesOfPeriodicLinearMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.UnitScale.PeriodicOperatorAlgebra.Derivation
open OneStepChart
section Evaluation
variable {S : PairedFunctionSpace} {I : Type}
  {ev : (S.index → Matrices.ComplexMatrix2) → I → Matrices.ComplexMatrix2}
theorem slotEvaluation_eval_zero (hr : IsSlotEvaluation S I ev) : ev 0 = 0 := by
  simpa using hr.eval_smul 0 0 S.complexSubmodule.zero_mem
theorem slotEvaluation_eval_sub (hr : IsSlotEvaluation S I ev) {u w : S.index → Matrices.ComplexMatrix2}
    (hu : u ∈ S.complexSubmodule) (hw : w ∈ S.complexSubmodule) : ev (u - w) = ev u - ev w := by
  have h := hr.eval_add u hu ((-1 : ℂ) • w) (S.complexSubmodule.smul_mem _ hw)
  rw [hr.eval_smul (-1) w hw] at h
  simpa [sub_eq_add_neg] using h
end Evaluation
theorem finsum_eq_sum_of_nonzero_mem {ι : Type} (c : ι → ℝ) (x : ι → Matrices.ComplexMatrix2)
    (F : Finset ι) (hc : ∀ i, c i ≠ 0 → i ∈ F) :
    ∑ᶠ i, c i • x i = ∑ i ∈ F, c i • x i := by
  refine finsum_eq_sum_of_support_subset _ fun i hi => hc i fun hz => hi ?_
  simp [hz]
variable {n : ℕ} {X Y Z : TwoScaleFunctions}
theorem extend_zero (C : CellCoordinates n X) : X.extend 0 = 0 := by
  have h0 := X.torusSpace.complexSubmodule.zero_mem
  refine C.full_basis.eq_of_eval_eq _ (C.extend_mem _ h0) _
    X.fullSpace.complexSubmodule.zero_mem ?_
  funext i
  rw [C.eval_extend _ h0, slotEvaluation_eval_zero C.torus_coordinates, slotEvaluation_eval_zero C.full_basis]
  rfl
theorem extend_add (C : CellCoordinates n X) {u w : X.torusSpace.index → Matrices.ComplexMatrix2}
    (hu : u ∈ X.torusSpace.complexSubmodule) (hw : w ∈ X.torusSpace.complexSubmodule) :
    X.extend (u + w) = X.extend u + X.extend w := by
  have hu' := C.extend_mem u hu
  have hw' := C.extend_mem w hw
  have hs := X.torusSpace.complexSubmodule.add_mem hu hw
  refine C.full_basis.eq_of_eval_eq _ (C.extend_mem _ hs) _
    (X.fullSpace.complexSubmodule.add_mem hu' hw') ?_
  funext i
  rw [C.full_basis.eval_add _ hu' _ hw', Pi.add_apply, C.eval_extend _ hs, C.eval_extend _ hu,
    C.eval_extend _ hw, C.torus_coordinates.eval_add _ hu _ hw, Pi.add_apply]
theorem extend_sub (C : CellCoordinates n X) {u w : X.torusSpace.index → Matrices.ComplexMatrix2}
    (hu : u ∈ X.torusSpace.complexSubmodule) (hw : w ∈ X.torusSpace.complexSubmodule) :
    X.extend (u - w) = X.extend u - X.extend w := by
  have hu' := C.extend_mem u hu
  have hw' := C.extend_mem w hw
  have hs := X.torusSpace.complexSubmodule.sub_mem hu hw
  refine C.full_basis.eq_of_eval_eq _ (C.extend_mem _ hs) _
    (X.fullSpace.complexSubmodule.sub_mem hu' hw') ?_
  funext i
  rw [slotEvaluation_eval_sub C.full_basis hu' hw', Pi.sub_apply, C.eval_extend _ hs,
    C.eval_extend _ hu, C.eval_extend _ hw, slotEvaluation_eval_sub C.torus_coordinates hu hw, Pi.sub_apply]
theorem shift_zero (C : CellCoordinates n X) (a : Fin 4 → ℤ) : X.shift a 0 = 0 := by
  have h0 := X.fullSpace.complexSubmodule.zero_mem
  refine C.full_basis.eq_of_eval_eq _ (C.shift_mem a _ h0) _ h0 ?_
  funext i
  rw [C.eval_shift a _ h0, slotEvaluation_eval_zero C.full_basis]
  rfl
theorem shift_add (C : CellCoordinates n X) (a : Fin 4 → ℤ)
    {u w : X.fullSpace.index → Matrices.ComplexMatrix2}
    (hu : u ∈ X.fullSpace.complexSubmodule) (hw : w ∈ X.fullSpace.complexSubmodule) :
    X.shift a (u + w) = X.shift a u + X.shift a w := by
  have hu' := C.shift_mem a u hu
  have hw' := C.shift_mem a w hw
  have hs := X.fullSpace.complexSubmodule.add_mem hu hw
  refine C.full_basis.eq_of_eval_eq _ (C.shift_mem a _ hs) _
    (X.fullSpace.complexSubmodule.add_mem hu' hw') ?_
  funext i
  rw [C.full_basis.eval_add _ hu' _ hw', Pi.add_apply, C.eval_shift a _ hs, C.eval_shift a _ hu,
    C.eval_shift a _ hw, C.full_basis.eval_add _ hu _ hw, Pi.add_apply]
theorem shift_sub (C : CellCoordinates n X) (a : Fin 4 → ℤ)
    {u w : X.fullSpace.index → Matrices.ComplexMatrix2}
    (hu : u ∈ X.fullSpace.complexSubmodule) (hw : w ∈ X.fullSpace.complexSubmodule) :
    X.shift a (u - w) = X.shift a u - X.shift a w := by
  have hu' := C.shift_mem a u hu
  have hw' := C.shift_mem a w hw
  have hs := X.fullSpace.complexSubmodule.sub_mem hu hw
  refine C.full_basis.eq_of_eval_eq _ (C.shift_mem a _ hs) _
    (X.fullSpace.complexSubmodule.sub_mem hu' hw') ?_
  funext i
  rw [slotEvaluation_eval_sub C.full_basis hu' hw', Pi.sub_apply, C.eval_shift a _ hs,
    C.eval_shift a _ hu, C.eval_shift a _ hw, slotEvaluation_eval_sub C.full_basis hu hw, Pi.sub_apply]
theorem realKernel_id : HasRealFiniteKernel X X (fun u => u) := by
  classical
  refine ⟨fun j i => if i = j then 1 else 0, fun j => ?_, fun u _ j => ?_⟩
  · refine (Set.finite_singleton j).subset fun i hi => ?_
    by_contra hne
    exact hi (if_neg hne)
  · rw [finsum_eq_sum_of_nonzero_mem _ _ {j} fun i hi => ?_]
    · simp
    · by_contra hne
      exact hi (if_neg (by simpa using hne))
theorem realKernel_zero (C : CellCoordinates n Y) : HasRealFiniteKernel X Y (fun _ => 0) := by
  refine ⟨fun _ _ => 0, fun j => by simp, fun u _ j => ?_⟩
  rw [slotEvaluation_eval_zero C.full_basis]
  simp
theorem realKernel_comp
    {A : (X.fullSpace.index → Matrices.ComplexMatrix2) → Y.fullSpace.index → Matrices.ComplexMatrix2}
    {B : (Y.fullSpace.index → Matrices.ComplexMatrix2) → Z.fullSpace.index → Matrices.ComplexMatrix2}
    (hA : ∀ u ∈ X.fullSpace.complexSubmodule, A u ∈ Y.fullSpace.complexSubmodule)
    (kA : HasRealFiniteKernel X Y A) (kB : HasRealFiniteKernel Y Z B) :
    HasRealFiniteKernel X Z (fun u => B (A u)) := by
  classical
  obtain ⟨G₁, s₁, h₁⟩ := kA
  obtain ⟨G₂, s₂, h₂⟩ := kB
  have hrow : ∀ k i, (∑ j ∈ (s₂ k).toFinset, G₂ k j * G₁ j i) ≠ 0 →
      i ∈ (s₂ k).toFinset.biUnion fun j => (s₁ j).toFinset := by
    intro k i hi
    obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    exact Finset.mem_biUnion.2 ⟨j, hj, by simpa using right_ne_zero_of_mul hne⟩
  refine ⟨fun k i => ∑ j ∈ (s₂ k).toFinset, G₂ k j * G₁ j i, fun k => ?_, fun u hu k => ?_⟩
  · exact ((s₂ k).toFinset.biUnion fun j => (s₁ j).toFinset).finite_toSet.subset
      fun i hi => hrow k i hi
  · rw [finsum_eq_sum_of_nonzero_mem _ _ _ (hrow k), h₂ (A u) (hA u hu) k,
      finsum_eq_sum_of_nonzero_mem _ _ (s₂ k).toFinset fun j hj => by simpa using hj]
    have hin : ∀ j ∈ (s₂ k).toFinset, Y.eval (A u) j =
        ∑ i ∈ (s₂ k).toFinset.biUnion (fun j => (s₁ j).toFinset), G₁ j i • X.eval u i := by
      intro j hj
      rw [h₁ u hu j]
      exact finsum_eq_sum_of_nonzero_mem _ _ _ fun i hi => Finset.mem_biUnion.2 ⟨j, hj, by simpa using hi⟩
    rw [Finset.sum_congr rfl fun j hj => by rw [hin j hj]]
    simp only [Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm
theorem realKernel_add (C : CellCoordinates n Y)
    {A B : (X.fullSpace.index → Matrices.ComplexMatrix2) → Y.fullSpace.index → Matrices.ComplexMatrix2}
    (hA : ∀ u ∈ X.fullSpace.complexSubmodule, A u ∈ Y.fullSpace.complexSubmodule)
    (hB : ∀ u ∈ X.fullSpace.complexSubmodule, B u ∈ Y.fullSpace.complexSubmodule)
    (kA : HasRealFiniteKernel X Y A) (kB : HasRealFiniteKernel X Y B) :
    HasRealFiniteKernel X Y (fun u => A u + B u) := by
  classical
  obtain ⟨G₁, s₁, h₁⟩ := kA
  obtain ⟨G₂, s₂, h₂⟩ := kB
  have hrow : ∀ j i, G₁ j i + G₂ j i ≠ 0 → i ∈ (s₁ j).toFinset ∪ (s₂ j).toFinset := by
    intro j i hi
    by_contra hne
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_or, not_not] at hne
    exact hi (by rw [hne.1, hne.2, add_zero])
  refine ⟨fun j i => G₁ j i + G₂ j i, fun j => ?_, fun u hu j => ?_⟩
  · exact ((s₁ j).toFinset ∪ (s₂ j).toFinset).finite_toSet.subset fun i hi => hrow j i hi
  · rw [C.full_basis.eval_add _ (hA u hu) _ (hB u hu), Pi.add_apply, h₁ u hu j, h₂ u hu j,
      finsum_eq_sum_of_nonzero_mem _ _ _ (hrow j),
      finsum_eq_sum_of_nonzero_mem _ _ ((s₁ j).toFinset ∪ (s₂ j).toFinset)
        fun i hi => Finset.mem_union_left _ (by simpa using hi),
      finsum_eq_sum_of_nonzero_mem (G₂ j) _ ((s₁ j).toFinset ∪ (s₂ j).toFinset)
        fun i hi => Finset.mem_union_right _ (by simpa using hi),
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (add_smul _ _ _).symm
theorem realKernel_sub (C : CellCoordinates n Y)
    {A B : (X.fullSpace.index → Matrices.ComplexMatrix2) → Y.fullSpace.index → Matrices.ComplexMatrix2}
    (hA : ∀ u ∈ X.fullSpace.complexSubmodule, A u ∈ Y.fullSpace.complexSubmodule)
    (hB : ∀ u ∈ X.fullSpace.complexSubmodule, B u ∈ Y.fullSpace.complexSubmodule)
    (kA : HasRealFiniteKernel X Y A) (kB : HasRealFiniteKernel X Y B) :
    HasRealFiniteKernel X Y (fun u => A u - B u) := by
  classical
  obtain ⟨G₁, s₁, h₁⟩ := kA
  obtain ⟨G₂, s₂, h₂⟩ := kB
  have hrow : ∀ j i, G₁ j i - G₂ j i ≠ 0 → i ∈ (s₁ j).toFinset ∪ (s₂ j).toFinset := by
    intro j i hi
    by_contra hne
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_or, not_not] at hne
    exact hi (by rw [hne.1, hne.2, sub_zero])
  refine ⟨fun j i => G₁ j i - G₂ j i, fun j => ?_, fun u hu j => ?_⟩
  · exact ((s₁ j).toFinset ∪ (s₂ j).toFinset).finite_toSet.subset fun i hi => hrow j i hi
  · rw [slotEvaluation_eval_sub C.full_basis (hA u hu) (hB u hu), Pi.sub_apply, h₁ u hu j, h₂ u hu j,
      finsum_eq_sum_of_nonzero_mem _ _ _ (hrow j),
      finsum_eq_sum_of_nonzero_mem _ _ ((s₁ j).toFinset ∪ (s₂ j).toFinset)
        fun i hi => Finset.mem_union_left _ (by simpa using hi),
      finsum_eq_sum_of_nonzero_mem (G₂ j) _ ((s₁ j).toFinset ∪ (s₂ j).toFinset)
        fun i hi => Finset.mem_union_right _ (by simpa using hi),
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
theorem statement_holds : Statement := by
  intro n _
  refine
    { id := fun X _ =>
        { full_mem := fun _ hu => hu
          torus_mem := fun _ hu => hu
          map_extend := fun _ _ => rfl
          commutes := fun _ _ _ => rfl
          realKernel := realKernel_id }
      zero := fun X Y CX CY =>
        { full_mem := fun _ _ => Y.fullSpace.complexSubmodule.zero_mem
          torus_mem := fun _ _ => Y.torusSpace.complexSubmodule.zero_mem
          map_extend := fun _ _ => (extend_zero CY).symm
          commutes := fun a _ _ => (shift_zero CY a).symm
          realKernel := realKernel_zero CY }
      comp := fun X Y Z CX CY CZ A A' B B' hA hB =>
        { full_mem := fun u hu => hB.full_mem _ (hA.full_mem u hu)
          torus_mem := fun u hu => hB.torus_mem _ (hA.torus_mem u hu)
          map_extend := fun u hu => by
            show B (A (X.extend u)) = Z.extend (B' (A' u))
            rw [hA.map_extend u hu, hB.map_extend _ (hA.torus_mem u hu)]
          commutes := fun a u hu => by
            show B (A (X.shift a u)) = Z.shift a (B (A u))
            rw [hA.commutes a u hu, hB.commutes a _ (hA.full_mem u hu)]
          realKernel := realKernel_comp hA.full_mem hA.realKernel hB.realKernel }
      add := fun X Y CX CY A B A' B' hA hB =>
        { full_mem := fun u hu =>
            Y.fullSpace.complexSubmodule.add_mem (hA.full_mem u hu) (hB.full_mem u hu)
          torus_mem := fun u hu =>
            Y.torusSpace.complexSubmodule.add_mem (hA.torus_mem u hu) (hB.torus_mem u hu)
          map_extend := fun u hu => by
            show A (X.extend u) + B (X.extend u) = Y.extend (A' u + B' u)
            rw [hA.map_extend u hu, hB.map_extend u hu,
              extend_add CY (hA.torus_mem u hu) (hB.torus_mem u hu)]
          commutes := fun a u hu => by
            show A (X.shift a u) + B (X.shift a u) = Y.shift a (A u + B u)
            rw [hA.commutes a u hu, hB.commutes a u hu,
              shift_add CY a (hA.full_mem u hu) (hB.full_mem u hu)]
          realKernel := realKernel_add CY hA.full_mem hB.full_mem hA.realKernel hB.realKernel }
      sub := fun X Y CX CY A B A' B' hA hB =>
        { full_mem := fun u hu =>
            Y.fullSpace.complexSubmodule.sub_mem (hA.full_mem u hu) (hB.full_mem u hu)
          torus_mem := fun u hu =>
            Y.torusSpace.complexSubmodule.sub_mem (hA.torus_mem u hu) (hB.torus_mem u hu)
          map_extend := fun u hu => by
            show A (X.extend u) - B (X.extend u) = Y.extend (A' u - B' u)
            rw [hA.map_extend u hu, hB.map_extend u hu,
              extend_sub CY (hA.torus_mem u hu) (hB.torus_mem u hu)]
          commutes := fun a u hu => by
            show A (X.shift a u) - B (X.shift a u) = Y.shift a (A u - B u)
            rw [hA.commutes a u hu, hB.commutes a u hu,
              shift_sub CY a (hA.full_mem u hu) (hB.full_mem u hu)]
          realKernel := realKernel_sub CY hA.full_mem hB.full_mem hA.realKernel hB.realKernel }
      congr := fun X Y CX CY A B A' B' hA e e' =>
        { full_mem := fun u hu => by
            rw [e u hu]
            exact hA.full_mem u hu
          torus_mem := fun u hu => by
            rw [e' u hu]
            exact hA.torus_mem u hu
          map_extend := fun u hu => by
            rw [e _ (CX.extend_mem u hu), e' u hu]
            exact hA.map_extend u hu
          commutes := fun a u hu => by
            rw [e _ (CX.shift_mem a u hu), e u hu]
            exact hA.commutes a u hu
          realKernel := by
            obtain ⟨G, s, h⟩ := hA.realKernel
            exact ⟨G, s, fun u hu j => by rw [e u hu]; exact h u hu j⟩ } }
end YangMills.Construction.Tower.UnitScale.PeriodicOperatorAlgebra.Derivation
end
