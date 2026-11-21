import YangMills.Construction.Continuum.ConnectedFunctionsAndCentredFunctionalOfAFunctional
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOfFourSpaceAndTheirFunctionals
import YangMills.Construction.Torus.SeparatedTuplesAndIsometriesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open YangMills.Construction.AmbientPoints
noncomputable section
namespace YangMills.Construction.Continuum.SeparatedFourTuples
theorem mem_image_val_succ_iff {k : ℕ} (A : Finset (Fin k)) (i : Fin k) :
    (i : ℕ) + 1 ∈ A.image (fun j : Fin k => (j : ℕ) + 1) ↔ i ∈ A := by
  simp [Fin.val_inj]
theorem sublistOn_ofFn {k : ℕ} (f : Fin k → SeparatedTuples.RealValued) (A : Finset (Fin k)) :
    SeparatedTuples.SepTuple.sublistOn (List.ofFn f) (A.image fun i : Fin k => (i : ℕ) + 1) =
      List.ofFn (restrictTuple f A) := by
  have h₁ : (List.ofFn f).zipIdx 1 = (List.finRange k).map fun i => (f i, (i : ℕ) + 1) := by
    refine List.ext_getElem (by simp) fun n h₁ h₂ => ?_
    simp [List.getElem_zipIdx, add_comm]
  have h₂ : (List.finRange k).filter (· ∈ A) = A.sort (· ≤ ·) := by
    refine List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun _ _ _ _ => le_antisymm) ?_ ?_ ?_
    · exact (List.pairwise_le_finRange k).filter _
    · exact A.pairwise_sort (· ≤ ·)
    · refine (List.perm_ext_iff_of_nodup ((List.nodup_finRange k).filter _) (A.sort_nodup _)).2
        fun a => ?_
      simp
  have h₃ : List.ofFn (restrictTuple f A) = (A.sort (· ≤ ·)).map f := by
    refine List.ext_getElem (by simp) fun n h₁ h₂ => ?_
    simp [restrictTuple, Finset.orderEmbOfFin, Finset.orderIsoOfFin]
    rfl
  have h₅ : ((fun p : SeparatedTuples.RealValued × ℕ =>
      decide (p.2 ∈ A.image fun i : Fin k => (i : ℕ) + 1)) ∘ fun i : Fin k => (f i, (i : ℕ) + 1)) =
      fun x => decide (x ∈ A) :=
    funext fun i => by simp only [Function.comp, mem_image_val_succ_iff]
  rw [h₃, ← h₂, SeparatedTuples.SepTuple.sublistOn, h₁, List.filter_map, List.map_map, h₅]
  rfl
theorem cumulantOne_congr (s : TestSpaces.SepTuple → ℝ)
    {f g : (Fin 4 → ℝ) → ℝ} (h : f = g)
    (hf : f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)))
    (hg : g ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) :
    TestSpaces.cumulantOne s f hf = TestSpaces.cumulantOne s g hg := by
  subst h
  rfl
theorem get_eq_of_eq_ofFn {k : ℕ} (f : Fin k → SeparatedTuples.RealValued)
    {L : List SeparatedTuples.RealValued} (hL : L = List.ofFn f) (l : Fin L.length)
    (i : Fin k) (h : (l : ℕ) = i) : L.get l = f i := by
  subst hL
  rw [List.get_ofFn]
  exact congrArg f (Fin.ext h)
end YangMills.Construction.Continuum.SeparatedFourTuples
end
