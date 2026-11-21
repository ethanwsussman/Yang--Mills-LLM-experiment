import YangMills.Construction.EuclideanFunctionals.FirstValuesOfTheCentredFunctional
import YangMills.Construction.LimitTheorem.RepresentativeAndTheIdentificationsProof
import YangMills.Construction.LimitsOfLatticeFamilies.TensorsOfSeparatedTuplesAndCentredFunctionals
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.EuclideanFunctionals.CenteredInitialValues
open ReflectionPositivity.AxisMirror
theorem finpartition_fin_zero_parts_eq_empty (P : Finpartition (Finset.univ : Finset (Fin 0))) :
    P.parts = ∅ := by apply _root_.YangMills.Construction.LatticeLimits.ModelSpace.finpartition_fin_zero_parts <;> assumption
theorem nonSingletonPartitions_zero : SetPartition.nonSingletonPartitions 0 = {⊥} := by
  ext P
  simp only [SetPartition.nonSingletonPartitions, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro _
    exact Finpartition.ext (by
      rw [finpartition_fin_zero_parts_eq_empty, finpartition_fin_zero_parts_eq_empty])
  · intro _ B hB
    rw [finpartition_fin_zero_parts_eq_empty] at hB
    simp at hB
theorem nonSingletonPartitions_one : SetPartition.nonSingletonPartitions 1 = ∅ := by apply _root_.YangMills.SharedProofs.p2697 <;> assumption
theorem univ_fin_two_ne_bot : (Finset.univ : Finset (Fin 2)) ≠ ⊥ :=
  Finset.univ_nonempty.ne_empty
theorem nonSingletonPartitions_two :
    SetPartition.nonSingletonPartitions 2 = {Finpartition.indiscrete univ_fin_two_ne_bot} := by
  ext P
  simp only [SetPartition.nonSingletonPartitions, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hP
    obtain ⟨B, hB, -⟩ := P.exists_mem (Finset.mem_univ (0 : Fin 2))
    have hcard : B.card = Fintype.card (Fin 2) :=
      le_antisymm (Finset.card_le_univ B) (by simpa using hP B hB)
    have huniv : B = Finset.univ := (Finset.card_eq_iff_eq_univ B).1 hcard
    subst huniv
    refine Finpartition.ext ?_
    rw [Finpartition.indiscrete_parts]
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨hB, fun C hC => ?_⟩
    by_contra hne
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hC
    exact Finset.disjoint_left.1 (P.disjoint hC hB hne) ha (Finset.mem_univ a)
  · rintro rfl B hB
    rw [Finpartition.indiscrete_parts, Finset.mem_singleton] at hB
    subst hB
    simp
theorem subList_univ {α : Type*} (L : List α) : Ambient.subList L Finset.univ = L := by
  have hcard : (Finset.univ : Finset (Fin L.length)).card = L.length := by simp
  have hemb : ((Finset.univ : Finset (Fin L.length)).orderEmbOfFin rfl : _ → Fin L.length) =
      Fin.cast hcard :=
    (Finset.orderEmbOfFin_unique rfl (f := Fin.cast hcard) (fun _ => Finset.mem_univ _)
      (fun _ _ h => h)).symm
  rw [Ambient.subList, hemb]
  refine List.ext_get (by simp) fun i h₁ h₂ => ?_
  simp
  rfl
theorem initialValues_holds : InitialValues := by
  intro S
  refine ⟨?_, fun u hu => ?_, fun u v hu hv hdisj => ?_⟩
  · change ∑ P ∈ SetPartition.nonSingletonPartitions 0, ∏ B ∈ P.parts,
      S.evalAt B.card (Ambient.subList ([] : FnList) B) = 1
    rw [nonSingletonPartitions_zero, Finset.sum_singleton, finpartition_fin_zero_parts_eq_empty,
      Finset.prod_empty]
  · change ∑ P ∈ SetPartition.nonSingletonPartitions 1, ∏ B ∈ P.parts,
      S.evalAt B.card (Ambient.subList ([u] : FnList) B) = 0
    rw [nonSingletonPartitions_one, Finset.sum_empty]
  · change ∑ P ∈ SetPartition.nonSingletonPartitions 2, ∏ B ∈ P.parts,
      S.evalAt B.card (Ambient.subList ([u, v] : FnList) B) = _
    rw [nonSingletonPartitions_two, Finset.sum_singleton, Finpartition.indiscrete_parts,
      Finset.prod_singleton]
    have key : ∀ n, n = 2 → ∀ L : FnList, L = [u, v] →
        S.evalAt n L = S.fn 2 le_rfl ⟨[u, v], pair_mem_sepN hu hv hdisj⟩ := by
      rintro _ rfl _ rfl
      exact S.evalAt_of_mem le_rfl (pair_mem_sepN hu hv hdisj)
    exact key _ (by simp) _ (subList_univ _)
end YangMills.Construction.EuclideanFunctionals.CenteredInitialValues
