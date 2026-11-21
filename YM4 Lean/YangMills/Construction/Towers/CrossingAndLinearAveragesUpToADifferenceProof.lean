import YangMills.Construction.Towers.ClosedFormsUnderTheLinearAverageProof
import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import YangMills.Construction.Towers.CrossingAndLinearAveragesUpToADifference
import YangMills.Construction.Towers.LinearMapsBetweenTwoLevelsOfATower
import YangMills.Construction.Towers.RelationAndBoundsOfTheIteratesOfTheLinearMapsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
namespace CoboundaryDifference
open TwoLevelMaps
theorem ofReal_smul_mem (r : ℝ) {M : Matrices.ComplexMatrix2}
    (hM : M ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    (r : ℂ) • M ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.IterateBounds.ofReal_smul_mem_hermitianTraceless <;> assumption
section Edges
variable {L n k j : ℕ}
theorem apply_mem_of_mem {B : Edge L n k j → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) (e : Edge L n k j) :
    B e ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.SmoothingIterProof.edgeForm_apply_mem <;> assumption
theorem mem_complexEdgeForms {B : Edge L n k j → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) : B ∈ complexEdgeForms L n k j := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_complexEdgeForms_of_mem <;> assumption
theorem mem_tracelessFunctions {f : Vertex L n k j → Matrices.ComplexMatrix2}
    (hf : f ∈ vertexFunctionSpace L n k j) :
    f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L n k j) :=
  fun x _ => (hf x (mem_univ x)).2
theorem vertexCoboundary_mem {f : Vertex L n k j → Matrices.ComplexMatrix2}
    (hf : f ∈ vertexFunctionSpace L n k j) : vertexCoboundary f ∈ edgeFormSpace L n k j := by apply _root_.YangMills.Construction.Tower.ClosedFormsSmoothing.vertexCoboundary_mem <;> assumption
theorem vertexCoboundary_sub (f g : Vertex L n k j → Matrices.ComplexMatrix2) :
    vertexCoboundary (f - g) = vertexCoboundary f - vertexCoboundary g := by
  funext e
  simp only [vertexCoboundary, Pi.sub_apply]
  abel
end Edges
section Averages
variable {L m : ℕ}
theorem sumAlong_add {i : ℤ} (A A' : PeriodicLattice.Bond L m i → Matrices.ComplexMatrix2)
    (γ : List (PeriodicLattice.Bond L m i)) :
    PeriodicLattice.bondFormSumAlong (A + A') γ =
      PeriodicLattice.bondFormSumAlong A γ + PeriodicLattice.bondFormSumAlong A' γ := by apply _root_.YangMills.Construction.PeriodicLattice.ClosedFormsSmoothing.bondFormSumAlong_add <;> assumption
theorem sumAlong_mem {i : ℤ} {A : PeriodicLattice.Bond L m i → Matrices.ComplexMatrix2}
    (hA : ∀ e, A e ∈ Matrices.ComplexMatrix2.hermitianTraceless)
    (γ : List (PeriodicLattice.Bond L m i)) :
    PeriodicLattice.bondFormSumAlong A γ ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  unfold PeriodicLattice.bondFormSumAlong
  refine list_sum_mem ?_
  intro x hx
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
  exact hA e
theorem contourFormAverage_add {i i' : ℤ}
    (A A' : PeriodicLattice.Bond L m i' → Matrices.ComplexMatrix2)
    (y : PeriodicLattice.Site L m i) (x : PeriodicLattice.Site L m i') :
    PeriodicLattice.contourFormAverage (A + A') y x =
      PeriodicLattice.contourFormAverage A y x + PeriodicLattice.contourFormAverage A' y x := by apply _root_.YangMills.Construction.PeriodicLattice.ClosedFormsSmoothing.contourFormAverage_add <;> assumption
theorem contourFormAverage_mem {i i' : ℤ}
    {A : PeriodicLattice.Bond L m i' → Matrices.ComplexMatrix2}
    (hA : ∀ e, A e ∈ Matrices.ComplexMatrix2.hermitianTraceless)
    (y : PeriodicLattice.Site L m i) (x : PeriodicLattice.Site L m i') :
    PeriodicLattice.contourFormAverage A y x ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  unfold PeriodicLattice.contourFormAverage
  exact ofReal_smul_mem _ (Submodule.sum_mem _ fun σ _ => sumAlong_mem hA _)
end Averages
section Iterates
variable {L n k : ℕ}
theorem linearSmoothing_add (hfin : ∀ j : ℤ, Finite (PeriodicLattice.Site L n j)) {j : ℕ}
    (A A' : Edge L n k j → Matrices.ComplexMatrix2) :
    linearSmoothing L n k j (A + A') = linearSmoothing L n k j A + linearSmoothing L n k j A' := by
  have := hfin (PeriodicLattice.levelDepth k j)
  funext c
  simp only [linearSmoothing, PeriodicLattice.scaledLinearBlockStep,
    PeriodicLattice.scaledLinearBlockAverage, PeriodicLattice.linearBlockSum, Pi.add_apply]
  rw [← smul_add, ← finsum_mem_add_distrib (Set.toFinite _)]
  congr 1
  refine finsum_mem_congr rfl fun x _ => ?_
  rw [contourFormAverage_add, sumAlong_add, contourFormAverage_add]
  abel
theorem linearSmoothingIter_add (hfin : ∀ j : ℤ, Finite (PeriodicLattice.Site L n j)) (m : ℕ)
    (A A' : Edge L n k 0 → Matrices.ComplexMatrix2) :
    linearSmoothingIter L n k m (A + A') =
      linearSmoothingIter L n k m A + linearSmoothingIter L n k m A' := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change linearSmoothing L n k m (linearSmoothingIter L n k m (A + A')) =
      linearSmoothing L n k m (linearSmoothingIter L n k m A) +
        linearSmoothing L n k m (linearSmoothingIter L n k m A')
    rw [ih, linearSmoothing_add hfin]
theorem crossingSmoothing_mem {j : ℕ} {B : Edge L n k j → Matrices.ComplexMatrix2}
    (hB : ∀ e, B e ∈ Matrices.ComplexMatrix2.hermitianTraceless) (c : Edge L n k (j + 1)) :
    crossingSmoothing L n k j B c ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  unfold crossingSmoothing PeriodicLattice.inverseFourthPowerWeight
  exact ofReal_smul_mem _ (finsum_mem_induction (· ∈ Matrices.ComplexMatrix2.hermitianTraceless)
    Matrices.ComplexMatrix2.hermitianTraceless.zero_mem
    (fun _ _ => Matrices.ComplexMatrix2.hermitianTraceless.add_mem) fun x _ => sumAlong_mem hB _)
theorem crossingSmoothingIter_mem {A : Edge L n k 0 → Matrices.ComplexMatrix2}
    (hA : ∀ e, A e ∈ Matrices.ComplexMatrix2.hermitianTraceless) (m : ℕ) :
    ∀ e, crossingSmoothingIter L n k m A e ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  induction m with
  | zero => exact hA
  | succ m ih => exact crossingSmoothing_mem ih
theorem cubeContourAverage_mem {j : ℕ} {B : Edge L n k j → Matrices.ComplexMatrix2}
    (hB : ∀ e, B e ∈ Matrices.ComplexMatrix2.hermitianTraceless) (y : Vertex L n k (j + 1)) :
    cubeContourAverage L n k j B y ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  unfold cubeContourAverage PeriodicLattice.inverseFourthPowerWeight
  exact ofReal_smul_mem _ (finsum_mem_induction (· ∈ Matrices.ComplexMatrix2.hermitianTraceless)
    Matrices.ComplexMatrix2.hermitianTraceless.zero_mem
    (fun _ _ => Matrices.ComplexMatrix2.hermitianTraceless.add_mem)
    fun x _ => contourFormAverage_mem hB _ _)
theorem restrictVertexFunction_mem {i j : ℕ} {f : Vertex L n k j → Matrices.ComplexMatrix2}
    (hf : ∀ x, f x ∈ Matrices.ComplexMatrix2.hermitianTraceless) (y : Vertex L n k i) :
    restrictVertexFunction i f y ∈ Matrices.ComplexMatrix2.hermitianTraceless :=
  hf _
theorem cubeContourAverageIter_mem {A : Edge L n k 0 → Matrices.ComplexMatrix2}
    (hA : ∀ e, A e ∈ Matrices.ComplexMatrix2.hermitianTraceless) (m : ℕ) (y : Vertex L n k m) :
    cubeContourAverageIter L n k m A y ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  unfold cubeContourAverageIter
  rw [Finset.sum_apply]
  exact Submodule.sum_mem _ fun i _ =>
    restrictVertexFunction_mem (cubeContourAverage_mem (crossingSmoothingIter_mem hA i)) y
theorem extendByZero_mem {i l : ℕ} {g : Vertex L n k l → Matrices.ComplexMatrix2}
    (hg : ∀ y, g y ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    (_root_.YangMills.Construction.Tower.TwoLevelMaps.extendByZero g : Vertex L n k i → Matrices.ComplexMatrix2) ∈ vertexFunctionSpace L n k i := by
  intro x _
  unfold _root_.YangMills.Construction.Tower.TwoLevelMaps.extendByZero
  split_ifs with h
  · exact hg _
  · exact Matrices.ComplexMatrix2.hermitianTraceless.zero_mem
end Iterates
theorem of_sub_self {m : ℕ} (P : ∀ i, i ≤ m → Prop) (h : P (m - m) (Nat.sub_le m m)) :
    P 0 (Nat.zero_le m) := by
  have key : ∀ i (hi : i ≤ m), i = m - m → P i hi := by
    intro i hi e
    subst e
    exact h
  exact key 0 _ (Nat.sub_self m).symm
section Composites
variable {L n k m : ℕ}
theorem linearSmoothingIter_eq (hR : CompositeRelations L n k m m) (hP : CompositesFromBase L n k m)
    {A : Edge L n k 0 → Matrices.ComplexMatrix2} (hA : A ∈ edgeFormSpace L n k 0) :
    linearSmoothingIter L n k m A =
      crossingSmoothingIter L n k m A - vertexCoboundary (cubeContourAverageIter L n k m A) := by
  have h := of_sub_self (fun i hi => ∀ B ∈ complexEdgeForms L n k i,
    linearSmoothingBetween L n k hi B = crossingSmoothingBetween L n k hi B -
      vertexCoboundary (cubeContourAverageBetween L n k hi B)) hR.linearSmoothing_eq
  have e := h A (mem_complexEdgeForms hA)
  rwa [hP.linearSmoothing_eq A hA, hP.crossingSmoothing_eq A hA,
    hP.cubeContourAverage_eq A hA] at e
theorem linearSmoothingIter_coboundary (hR : CompositeRelations L n k m m)
    (hP : CompositesFromBase L n k m) {f : Vertex L n k 0 → Matrices.ComplexMatrix2}
    (hf : f ∈ vertexFunctionSpace L n k 0) :
    linearSmoothingIter L n k m (vertexCoboundary f) =
      vertexCoboundary (restrictVertexFunction m f) := by
  have h := of_sub_self (fun i hi =>
    ∀ g ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L n k i),
      linearSmoothingBetween L n k hi (vertexCoboundary g) =
        vertexCoboundary (restrictVertexFunction m g))
    hR.linearSmoothing_coboundary
  have e := h f (mem_tracelessFunctions hf)
  rwa [hP.linearSmoothing_eq _ (vertexCoboundary_mem hf)] at e
theorem restrict_extendByZero (hR : CompositeRelations L n k m m)
    {g : Vertex L n k m → Matrices.ComplexMatrix2}
    (hg : ∀ y, g y ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    restrictVertexFunction m (_root_.YangMills.Construction.Tower.TwoLevelMaps.extendByZero g : Vertex L n k 0 → Matrices.ComplexMatrix2) = g := by
  have hc : g ∈ (pairedFunctions (Vertex L n k m)).complexSubmodule := fun y _ => (hg y).2
  have h := of_sub_self (m := m) (fun i _ =>
    restrictVertexFunction m (_root_.YangMills.Construction.Tower.TwoLevelMaps.extendByZero g : Vertex L n k i → Matrices.ComplexMatrix2) = g) (by
      have e := hR.restrict_transposeMap ⟨g, hc⟩
      rwa [hR.transposeMap_eq ⟨g, hc⟩] at e)
  exact h
end Composites
end CoboundaryDifference
open CoboundaryDifference in
theorem CoboundaryDifference.statement_holds (hMaps : TwoLevelMaps.Statement) :
    CrossingAndLinearSmoothingDifferByCoboundary := by
  intro L hL k n hk hn
  have hfin : ∀ j : ℤ, Finite (PeriodicLattice.Site L n j) := fun j =>
    SeparatedSequences.BaseParameters.site_finite (by have := hL.2; omega) n j
  obtain ⟨hComp, hBase⟩ := (((hMaps L hL k hk).1 n hn).2)
  refine ⟨fun m hm A hA f hf => ?_, fun A hA => ?_⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm1
    · exact ⟨f, hf, rfl⟩
    · have hR := hComp m m hm1 le_rfl hm
      have hP := hBase m hm
      refine ⟨restrictVertexFunction m f - cubeContourAverageIter L n k m A, ?_, ?_⟩
      · intro y _
        exact Matrices.ComplexMatrix2.hermitianTraceless.sub_mem
          (restrictVertexFunction_mem (fun x => hf x (mem_univ x)) y)
          (cubeContourAverageIter_mem (apply_mem_of_mem hA) m y)
      · rw [linearSmoothingIter_add hfin, linearSmoothingIter_eq hR hP hA,
          linearSmoothingIter_coboundary hR hP hf, vertexCoboundary_sub]
        abel
  · have hR := hComp k k hk le_rfl le_rfl
    have hP := hBase k le_rfl
    have hg := cubeContourAverageIter_mem (k := k) (apply_mem_of_mem hA) k
    refine ⟨TwoLevelMaps.extendByZero
      (cubeContourAverageIter L n k k A), extendByZero_mem hg, ?_⟩
    rw [linearSmoothingIter_add hfin, linearSmoothingIter_eq hR hP hA,
      linearSmoothingIter_coboundary hR hP (extendByZero_mem hg), restrict_extendByZero hR hg]
    abel
end YangMills.Construction.Tower
end
