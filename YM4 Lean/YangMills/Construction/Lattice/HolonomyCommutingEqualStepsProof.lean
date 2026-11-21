import YangMills.Construction.Lattice.HolonomyCommutingEqualSteps
import YangMills.Construction.Lattice.PathRearrangement
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
open YangMills.Construction.Matrices
namespace YangMills.Construction.PeriodicLattice.EqualStepFlows
variable {L m : ℕ} {j : ℤ}
def wordDisplacement (u : StepWord L m j) : Site L m j := (u.map fun s => (s : Site L m j)).sum
theorem wordDisplacement_eq_sum_map (u : StepWord L m j) :
    wordDisplacement u = (List.map (fun s : UnitStepVec L m j => (s : Site L m j)) u).sum := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    have e : wordDisplacement (a :: u) = (a : Site L m j) + wordDisplacement u := by
      simp [wordDisplacement]
    rw [e, ih, List.map_cons, List.sum_cons]
theorem wordDisplacement_perm {u v : StepWord L m j} (h : u.Perm v) :
    wordDisplacement u = wordDisplacement v := by
  rw [wordDisplacement_eq_sum_map, wordDisplacement_eq_sum_map]
  exact (h.map fun s : UnitStepVec L m j => (s : Site L m j)).sum_eq
theorem exists_finset_wordDisplacement_eq_of_sublist {u s : StepWord L m j} (h : u.Sublist s) :
    ∃ I : Finset (Fin s.length), wordDisplacement u = ∑ i ∈ I, (s.get i : Site L m j) := by
  induction h with
  | slnil => exact ⟨∅, by simp [wordDisplacement]⟩
  | @cons u s a _ ih =>
    obtain ⟨I, hI⟩ := ih
    refine ⟨I.map (Fin.succEmb _), ?_⟩
    rw [Finset.sum_map, hI]
    simp
  | @cons_cons u s a _ ih =>
    obtain ⟨I, hI⟩ := ih
    refine ⟨insert 0 (I.map (Fin.succEmb _)), ?_⟩
    rw [Finset.sum_insert (by simp [Fin.succ_ne_zero]), Finset.sum_map]
    have e : wordDisplacement (a :: u) = (a : Site L m j) + wordDisplacement u := by
      simp [wordDisplacement]
    rw [e, hI]
    simp
theorem add_wordDisplacement_mem_partialSumSites {u s : StepWord L m j} (h : u.Subperm s)
    (z : Site L m j) : z + wordDisplacement u ∈ partialSumSites z s := by
  obtain ⟨u', hp, hs⟩ := h
  obtain ⟨I, hI⟩ := exists_finset_wordDisplacement_eq_of_sublist hs
  exact ⟨I, by rw [← wordDisplacement_perm hp, hI]⟩
theorem nonParallelStepCount_cons (a : UnitStepVec L m j) (A : StepWord L m j)
    (f : UnitStepVec L m j) :
    nonParallelStepCount (a :: A) f = nonParallelStepCount [a] f + nonParallelStepCount A f := by
  classical
  simp only [nonParallelStepCount]
  rw [show ((a :: A : StepWord L m j) : List (Site L m j)) =
      (a : Site L m j) :: (A : List (Site L m j)) from rfl,
    show (([a] : StepWord L m j) : List (Site L m j)) = [(a : Site L m j)] from rfl,
    List.countP_cons, List.countP_cons, List.countP_nil]
  omega
theorem nonParallelStepCount_singleton {a f : UnitStepVec L m j}
    (h : (a : Site L m j) ≠ f ∧ (a : Site L m j) ≠ -(f : Site L m j)) :
    nonParallelStepCount [a] f = 1 := by
  classical
  simp only [nonParallelStepCount]
  rw [show (([a] : StepWord L m j) : List (Site L m j)) = [(a : Site L m j)] from rfl,
    List.countP_cons, List.countP_nil]
  simp [h]
theorem operatorNorm_sub_le_add (A B C : ComplexMatrix2) :
    ComplexMatrix2.operatorNorm (A - C) ≤
      ComplexMatrix2.operatorNorm (A - B) + ComplexMatrix2.operatorNorm (B - C) := by
  have h := norm_add_le (A - B) (B - C)
  rwa [sub_add_sub_cancel] at h
structure FlowHypotheses (U : Bond L m j → ComplexMatrix2) (z : Site L m j) (W : StepWord L m j)
    (ω : ℝ) : Prop where
  oddSide : Odd L
  largeSide : 13 ≤ L
  posExponent : 0 < m
  levelBound : -(m : ℤ) ≤ j
  isCompact : U ∈ compactGaugeFields L m j
  nonneg : 0 ≤ ω
  plaquetteBound : ∀ p : Plaquette L m j, p.vertices ⊆ partialSumSites z W →
    ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) ≤ ω
variable {U : Bond L m j → ComplexMatrix2} {z : Site L m j} {W : StepWord L m j} {ω : ℝ}
theorem norm_sub_wordHolonomy_swap_le (hR : PathRearrangementBound) (S : FlowHypotheses U z W ω)
    (P Q : StepWord L m j) (a f : UnitStepVec L m j) (hW : (P ++ a :: f :: Q).Perm W) :
    ComplexMatrix2.operatorNorm
        (wordHolonomy U z (P ++ a :: f :: Q) - wordHolonomy U z (P ++ f :: a :: Q)) ≤
      (nonParallelStepCount [a] f : ℝ) * ω := by
  classical
  let ex : AdjacentSwap L m j := ⟨P, a, f, Q⟩
  have hRR := hR L m S.oddSide S.largeSide S.posExponent j S.levelBound Set.univ U
    (fun _ _ => trivial) S.isCompact z
  have hone := hRR.1 ex (fun _ _ => trivial) (fun _ _ => trivial)
  by_cases hpar : ex.IsCollinear
  · have e₁ : wordHolonomy U z (P ++ a :: f :: Q) = wordHolonomy U z (P ++ f :: a :: Q) :=
      hone.1 hpar
    rw [e₁, sub_self]
    have h0 : ComplexMatrix2.operatorNorm (0 : ComplexMatrix2) = 0 := by
      simp [ComplexMatrix2.operatorNorm]
    rw [h0]
    exact mul_nonneg (Nat.cast_nonneg _) S.nonneg
  · obtain ⟨p, hp⟩ := (hone.2 hpar).1
    have hnot : (a : Site L m j) ≠ f ∧ (a : Site L m j) ≠ -(f : Site L m j) := by
      refine ⟨fun h => hpar (Or.inl h.symm), fun h => hpar (Or.inr ?_)⟩
      change (f : Site L m j) = -(a : Site L m j)
      rw [h, neg_neg]
    have hsub : ∀ u : StepWord L m j, u.Sublist (P ++ a :: f :: Q) →
        z + wordDisplacement u ∈ partialSumSites z W := fun u hu =>
      add_wordDisplacement_mem_partialSumSites (hu.subperm.trans hW.subperm) z
    have hstart : ex.cornerSite z = z + wordDisplacement P := rfl
    have hcorners : p.vertices ⊆ partialSumSites z W := by
      intro w hw
      have hw' : w ∈ ({ex.cornerSite z, ex.cornerSite z + ex.fst, ex.cornerSite z + ex.snd,
          ex.cornerSite z + ex.fst + ex.snd} : Set (Site L m j)) := by
        rw [← hp]
        exact hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw'
      rcases hw' with rfl | rfl | rfl | rfl
      · rw [hstart]
        exact hsub P (List.sublist_append_left _ _)
      · have e₂ : ex.cornerSite z + ex.fst = z + wordDisplacement (P ++ [a]) := by
          simp [hstart, ex, wordDisplacement, add_assoc]
        rw [e₂]
        exact hsub _ (List.Sublist.append_left (by simp) P)
      · have e₂ : ex.cornerSite z + ex.snd = z + wordDisplacement (P ++ [f]) := by
          simp [hstart, ex, wordDisplacement, add_assoc]
        rw [e₂]
        exact hsub _ (List.Sublist.append_left (by simp) P)
      · have e₂ : ex.cornerSite z + ex.fst + ex.snd = z + wordDisplacement (P ++ [a, f]) := by
          simp [hstart, ex, wordDisplacement, add_assoc]
        rw [e₂]
        exact hsub _ (List.Sublist.append_left (by simp) P)
    have hchain := (hRR.2 1 ![ex.original, ex.swapped] (fun _ => ex) (fun _ => p)
      (fun l => by
        obtain rfl := Subsingleton.elim l 0
        exact ⟨rfl, rfl⟩)
      (fun _ _ _ => trivial)
      (fun _ _ => ⟨hp, fun _ _ => trivial⟩)).2
    have hsum : (∑ l ∈ Finset.univ.filter (fun _ : Fin 1 => ¬ ex.IsCollinear),
        ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1)) =
          ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) := by
      simp [hpar]
    rw [hsum] at hchain
    rw [nonParallelStepCount_singleton hnot, Nat.cast_one, one_mul]
    exact hchain.trans (S.plaquetteBound p hcorners)
theorem norm_sub_wordHolonomy_move_le (hR : PathRearrangementBound) (S : FlowHypotheses U z W ω)
    (f : UnitStepVec L m j) (A : StepWord L m j) :
    ∀ P Q : StepWord L m j, (P ++ A ++ f :: Q).Perm W →
      ComplexMatrix2.operatorNorm (wordHolonomy U z (P ++ A ++ f :: Q) -
          wordHolonomy U z (P ++ f :: A ++ Q)) ≤
        (nonParallelStepCount A f : ℝ) * ω := by
  induction A with
  | nil =>
    intro P Q _
    have h0 : ComplexMatrix2.operatorNorm (0 : ComplexMatrix2) = 0 := by
      simp [ComplexMatrix2.operatorNorm]
    have hc : nonParallelStepCount ([] : StepWord L m j) f = 0 := rfl
    simp [hc, h0]
  | cons a A ih =>
    intro P Q hW
    have e₁ : P ++ (a :: A) ++ f :: Q = P ++ [a] ++ A ++ f :: Q := by simp
    have e₂ : P ++ [a] ++ f :: A ++ Q = P ++ a :: f :: (A ++ Q) := by simp
    have e₃ : P ++ f :: (a :: A) ++ Q = P ++ f :: a :: (A ++ Q) := by simp
    have h₁ := ih (P ++ [a]) Q (e₁ ▸ hW)
    have hW₂ : (P ++ a :: f :: (A ++ Q)).Perm W := by
      refine List.Perm.trans ?_ hW
      have h : (f :: (A ++ Q)).Perm (A ++ f :: Q) := List.perm_middle.symm
      simpa using (h.cons a).append_left P
    have h₂ := norm_sub_wordHolonomy_swap_le hR S P (A ++ Q) a f hW₂
    rw [e₂] at h₁
    rw [e₁, e₃, nonParallelStepCount_cons, Nat.cast_add, add_mul]
    refine (operatorNorm_sub_le_add _ (wordHolonomy U z (P ++ a :: f :: (A ++ Q))) _).trans ?_
    linarith
theorem replicate_append_replicate_perm (f : UnitStepVec L m j) (A : StepWord L m j)
    {i k n : ℕ} (h : i + k = n) :
    (List.replicate i f ++ A ++ List.replicate k f).Perm (A ++ List.replicate n f) := by
  subst h
  rw [List.replicate_add, ← List.append_assoc]
  exact List.perm_append_comm.append_right _
theorem norm_sub_pathHolonomy_flow_le (hR : PathRearrangementBound) {f : UnitStepVec L m j}
    {A : StepWord L m j} {n : ℕ} (S : FlowHypotheses U z (A ++ List.replicate n f) ω) (k : ℕ) :
    ∀ i : ℕ, i + k = n →
      ComplexMatrix2.operatorNorm
          (wordHolonomy U z (List.replicate i f ++ A ++ List.replicate k f) -
            wordHolonomy U z (List.replicate n f ++ A)) ≤
        (k : ℝ) * (nonParallelStepCount A f : ℝ) * ω := by
  induction k with
  | zero =>
    intro i hi
    have h0 : ComplexMatrix2.operatorNorm (0 : ComplexMatrix2) = 0 := by
      simp [ComplexMatrix2.operatorNorm]
    obtain rfl : i = n := by omega
    simp [h0]
  | succ k ih =>
    intro i hi
    have hp := replicate_append_replicate_perm f A hi
    rw [List.replicate_succ] at hp ⊢
    have h₁ := norm_sub_wordHolonomy_move_le hR S f A (List.replicate i f) (List.replicate k f) hp
    have h₂ := ih (i + 1) (by omega)
    have e : List.replicate (i + 1) f ++ A ++ List.replicate k f =
        List.replicate i f ++ f :: A ++ List.replicate k f := by
      rw [List.replicate_succ']
      simp
    rw [e] at h₂
    refine (operatorNorm_sub_le_add _
      (wordHolonomy U z (List.replicate i f ++ f :: A ++ List.replicate k f)) _).trans ?_
    have e₂ : ((k + 1 : ℕ) : ℝ) * (nonParallelStepCount A f : ℝ) * ω =
        (nonParallelStepCount A f : ℝ) * ω + (k : ℝ) * (nonParallelStepCount A f : ℝ) * ω := by
      push_cast
      ring
    rw [e₂]
    exact add_le_add h₁ h₂
theorem holonomyCommutesWithEqualSteps (hR : PathRearrangementBound) :
    HolonomyCommutesWithEqualSteps := by
  intro L m hodd h13 hm j hj U hU z w f n ω hω0 hω
  have S : FlowHypotheses U z (w ++ List.replicate n f) ω := ⟨hodd, h13, hm, hj, hU, hω0, hω⟩
  simpa using norm_sub_pathHolonomy_flow_le hR S n 0 (by simp)
end YangMills.Construction.PeriodicLattice.EqualStepFlows
