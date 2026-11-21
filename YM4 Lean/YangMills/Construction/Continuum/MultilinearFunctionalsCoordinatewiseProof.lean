import YangMills.Construction.Continuum.DisjointCompactSetsAreSeparated
import YangMills.Construction.Continuum.MultilinearFunctionalsCoordinatewise
import Mathlib
set_option autoImplicit false
open YangMills.Construction.AmbientPoints
open YangMills.Construction.TestSpaces.UnifiedSeparatedTuples
noncomputable section
namespace YangMills.Construction.EntrywiseMultilinearity
variable {s : Conventions.StandingParameters} {n : ℕ}
theorem pairSupports_self (i : Fin n) (f f' : Fin n → Pt s .euclidean → ℝ) :
    pairSupports i f f' i = tsupport (f i) ∪ tsupport (f' i) := by
  simp [pairSupports]
theorem pairSupports_of_ne {i l : Fin n} (hl : l ≠ i) (f f' : Fin n → Pt s .euclidean → ℝ) :
    pairSupports i f f' l = tsupport (f l) := by
  simp [pairSupports, Function.update_of_ne hl]
theorem isCompact_pairSupports {i : Fin n} {f f' : Fin n → Pt s .euclidean → ℝ}
    (hd : AgreeOffComponent s i f f') (l : Fin n) : IsCompact (pairSupports i f f' l) := by
  by_cases hl : l = i
  · subst hl
    rw [pairSupports_self]
    exact (hd.1.1 l).2.union (hd.2.1.1 l).2
  · rw [pairSupports_of_ne hl]
    exact (hd.1.1 l).2
theorem disjoint_pairSupports_self {i l : Fin n} {f f' : Fin n → Pt s .euclidean → ℝ}
    (hd : AgreeOffComponent s i f f') (hl : l ≠ i) :
    Disjoint (pairSupports i f f' i) (pairSupports i f f' l) := by
  rw [pairSupports_self, pairSupports_of_ne hl]
  refine Set.disjoint_union_left.2 ⟨hd.1.2 hl.symm, ?_⟩
  rw [hd.2.2 l hl]
  exact hd.2.1.2 hl.symm
theorem disjoint_pairSupports {i : Fin n} {f f' : Fin n → Pt s .euclidean → ℝ}
    (hd : AgreeOffComponent s i f f') {l l' : Fin n} (hne : l ≠ l') :
    Disjoint (pairSupports i f f' l) (pairSupports i f f' l') := by
  by_cases hl : l = i
  · subst hl
    exact disjoint_pairSupports_self hd hne.symm
  · by_cases hl' : l' = i
    · subst hl'
      exact (disjoint_pairSupports_self hd hl).symm
    · rw [pairSupports_of_ne hl, pairSupports_of_ne hl']
      exact hd.1.2 hne
theorem positivelySeparated_pairSupports
    (hsep : CompactSeparation.CompactSetsSeparated) {i : Fin n}
    {f f' : Fin n → Pt s .euclidean → ℝ} (hd : AgreeOffComponent s i f f') :
    Pairwise fun l l' => PositivelySeparated s .euclidean
      (pairSupports i f f' l) (pairSupports i f f' l') := fun _ _ hne =>
  ((hsep s).1 _ _ (isCompact_pairSupports hd _) (isCompact_pairSupports hd _)
    (disjoint_pairSupports hd hne)).ne'
theorem left_mem_c1Product {i : Fin n} {f f' : Fin n → Pt s .euclidean → ℝ}
    (hd : AgreeOffComponent s i f f') : f ∈ c1Product (pairSupports i f f') := by
  intro l _
  refine ⟨(hd.1.1 l).1, (hd.1.1 l).2, ?_⟩
  by_cases hl : l = i
  · subst hl
    rw [pairSupports_self]
    exact Set.subset_union_left
  · rw [pairSupports_of_ne hl]
theorem right_mem_c1Product {i : Fin n} {f f' : Fin n → Pt s .euclidean → ℝ}
    (hd : AgreeOffComponent s i f f') : f' ∈ c1Product (pairSupports i f f') := by
  intro l _
  refine ⟨(hd.2.1.1 l).1, (hd.2.1.1 l).2, ?_⟩
  by_cases hl : l = i
  · subst hl
    rw [pairSupports_self]
    exact Set.subset_union_right
  · rw [pairSupports_of_ne hl, hd.2.2 l hl]
theorem updateLinComb_mem_c1Product {i : Fin n} {f f' : Fin n → Pt s .euclidean → ℝ}
    (hd : AgreeOffComponent s i f f') (a b : ℝ) :
    updateLinComb i a b f f' ∈ c1Product (pairSupports i f f') := by
  intro l hmem
  by_cases hl : l = i
  · subst hl
    have k₁ : f l ∈ c1Submodule (pairSupports l f f' l) :=
      left_mem_c1Product hd l hmem
    have k₂ : f' l ∈ c1Submodule (pairSupports l f f' l) :=
      right_mem_c1Product hd l hmem
    have k₃ := (c1Submodule (pairSupports l f f' l)).add_mem
      ((c1Submodule _).smul_mem a k₁) ((c1Submodule _).smul_mem b k₂)
    have e : updateLinComb l a b f f' l = a • f l + b • f' l := by
      simp [updateLinComb]
    rw [e]
    exact k₃
  · simpa [updateLinComb, Function.update_of_ne hl] using left_mem_c1Product hd l hmem
theorem memCommonProduct_of_separated (hsep : CompactSeparation.CompactSetsSeparated)
    (s : Conventions.StandingParameters) (n : ℕ) : MemCommonProduct s n := fun _ _ _ a b hd =>
  ⟨positivelySeparated_pairSupports hsep hd, left_mem_c1Product hd,
    right_mem_c1Product hd, updateLinComb_mem_c1Product hd a b,
    fun _ hg => mem_separatedTuples_of_forall_mem_c1
      (positivelySeparated_pairSupports hsep hd) fun l => hg l (Set.mem_univ l)⟩
theorem isLinearInEachArgument_of_isTupleMultilinear (hsep : CompactSeparation.CompactSetsSeparated)
    {Ψ : separatedTuples s .euclidean n → ℝ} (hΨ : IsTupleMultilinear Ψ) :
    IsLinearInEachComponent Ψ := by
  classical
  intro i a b f f' f'' hd hf''
  obtain ⟨L, hL⟩ := hΨ _ (positivelySeparated_pairSupports hsep hd)
  let g : (l : Fin n) → c1Submodule (pairSupports i f.1 f'.1 l) :=
    fun l => ⟨f.1 l, left_mem_c1Product hd l (Set.mem_univ l)⟩
  let g' : (l : Fin n) → c1Submodule (pairSupports i f.1 f'.1 l) :=
    fun l => ⟨f'.1 l, right_mem_c1Product hd l (Set.mem_univ l)⟩
  have e₁ : L g = Ψ f := hL g
  have e₂ : L (Function.update g i (g' i)) = Ψ f' := by
    rw [hL]
    congr 1
    refine Subtype.ext (funext fun l => ?_)
    by_cases hl : l = i
    · subst hl
      simp [g']
    · simp [Function.update_of_ne hl, g, hd.2.2 l hl]
  have e₃ : L (Function.update g i (a • g i + b • g' i)) = Ψ f'' := by
    rw [hL]
    congr 1
    refine Subtype.ext (funext fun l => ?_)
    rw [hf'']
    by_cases hl : l = i
    · subst hl
      simp [updateLinComb, g, g']
    · simp [updateLinComb, Function.update_of_ne hl, g]
  rw [← e₃, L.map_update_add, L.map_update_smul, L.map_update_smul, e₂, Function.update_eq_self,
    e₁, smul_eq_mul, smul_eq_mul]
theorem isTupleMultilinear_of_isLinearInEachArgument {Ψ : separatedTuples s .euclidean n → ℝ}
    (hΨ : IsLinearInEachComponent Ψ) : IsTupleMultilinear Ψ := by
  intro K hK
  let e : ((l : Fin n) → c1Submodule (K l)) → separatedTuples s .euclidean n :=
    fun g => ⟨fun l => (g l : Pt s .euclidean → ℝ),
      mem_separatedTuples_of_forall_mem_c1 hK fun l => (g l).2⟩
  have hdiff : ∀ (m : (l : Fin n) → c1Submodule (K l)) (i : Fin n)
      (x y : c1Submodule (K i)),
      AgreeOffComponent s i (e (Function.update m i x)).1 (e (Function.update m i y)).1 := by
    intro m i x y
    refine ⟨(e _).2, (e _).2, fun l hl => ?_⟩
    simp [e, Function.update_of_ne hl]
  have hcomb : ∀ (m : (l : Fin n) → c1Submodule (K l)) (i : Fin n)
      (a b : ℝ) (x y z : c1Submodule (K i)),
      (z : Pt s .euclidean → ℝ) = a • (x : Pt s .euclidean → ℝ) + b • (y : _) →
      (e (Function.update m i z)).1 =
        updateLinComb i a b (e (Function.update m i x)).1 (e (Function.update m i y)).1 := by
    intro m i a b x y z hz
    funext l
    by_cases hl : l = i
    · subst hl
      have hu : ∀ w : c1Submodule (K l),
          (e (Function.update m l w)).1 l = (w : Pt s .euclidean → ℝ) := fun w => by
        simp [e]
      simp only [updateLinComb, Function.update_self]
      rw [hu, hu, hu, hz]
    · have hu : ∀ w : c1Submodule (K i),
          (e (Function.update m i w)).1 l = (m l : Pt s .euclidean → ℝ) := fun w => by
        simp [e, Function.update_of_ne hl]
      simp only [updateLinComb]
      rw [Function.update_of_ne hl, hu, hu]
  refine ⟨{ toFun := fun g => Ψ (e g), map_update_add' := ?_, map_update_smul' := ?_ },
    fun g => rfl⟩
  · intro inst m i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    have k := hΨ i 1 1 _ _ (e (Function.update m i (x + y))) (hdiff m i x y)
      (hcomb m i 1 1 x y (x + y) (by simp))
    simpa using k
  · intro inst m i a x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    have k := hΨ i a 0 _ _ (e (Function.update m i (a • x))) (hdiff m i x x)
      (hcomb m i a 0 x x (a • x) (by simp))
    simpa using k
theorem separatedTuples_eq_disjointSupportTuples
    (hU : TestSpaces.UnifiedSeparatedTuples.AllConditionsHold)
    (s : Conventions.StandingParameters) (u : ℕ) :
    (separatedTuples s .euclidean u : Set (Fin u → (Fin 4 → ℝ) → ℝ)) =
      TestSpaces.disjointSupportTuples Set.univ u := by
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · exact (separatedTuples_zero (s := s) (E := .euclidean)).trans
      (TestSpaces.disjointSupportTuples_zero Set.univ).symm
  · exact ((hU s).1 u hu).1.1
theorem tuplesAgreeOnEuclidean_of_unified
    (hU : TestSpaces.UnifiedSeparatedTuples.AllConditionsHold) (s : Conventions.StandingParameters) :
    TuplesAgreeOnEuclidean s := by
  refine ⟨separatedTuples_eq_disjointSupportTuples hU s, rfl, ?_, ?_⟩
  · ext ⟨m, f⟩
    constructor
    · intro hf
      have hf' : f ∈ TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) m := by
        rw [← separatedTuples_eq_disjointSupportTuples hU s m]
        exact hf
      exact ⟨⟨m, ⟨f, hf'⟩⟩, rfl⟩
    · rintro ⟨⟨m', Y⟩, hY⟩
      cases hY
      change Y.1 ∈ (separatedTuples s .euclidean m' : Set (Fin m' → (Fin 4 → ℝ) → ℝ))
      rw [separatedTuples_eq_disjointSupportTuples hU s m']
      exact Y.2
  · intro u f X hfX J
    exact congrArg (Sigma.mk J.card) (funext fun k => congrFun hfX _)
theorem symGraph_partitions_eq_image (u : ℕ) : ClusterExpansion.SymGraph.partitions (Fin u) =
    (Finset.univ : Finset (SetPartition.PartitionsFin u)).image fun π => π.parts := by
  ext η
  simp only [ClusterExpansion.SymGraph.partitions, ClusterExpansion.SymGraph.IsPartition,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hne, hdis, hcov⟩
    refine ⟨⟨η, Finset.supIndep_iff_pairwiseDisjoint.2 hdis, ?_, ?_⟩, rfl⟩
    · rw [Finset.sup_eq_biUnion]
      convert hcov
    · intro hb
      simpa using hne _ hb
  · rintro ⟨π, rfl⟩
    refine ⟨fun _ hb => π.nonempty_of_mem_parts hb, π.disjoint, ?_⟩
    convert π.biUnion_parts
theorem partitionsAgree_holds : PartitionsAgree := by
  refine ⟨fun n _ => symGraph_partitions_eq_image n, fun u => ?_⟩
  ext η
  simp only [TestSpaces.partitionsNoSingletons, Finset.mem_filter, symGraph_partitions_eq_image,
    Finset.mem_image, Finset.mem_univ, true_and, SetPartition.singletonFree]
  constructor
  · rintro ⟨⟨π, rfl⟩, h2⟩
    exact ⟨π, fun J hJ => by have := h2 J hJ; omega, rfl⟩
  · rintro ⟨π, h2, rfl⟩
    refine ⟨⟨π, rfl⟩, fun J hJ => ?_⟩
    have k₁ := h2 J hJ
    have k₀ : 0 < J.card := Finset.card_pos.2 (π.nonempty_of_mem_parts hJ)
    omega
theorem statement_of_unified_of_separated
    (hU : TestSpaces.UnifiedSeparatedTuples.AllConditionsHold)
    (hsep : CompactSeparation.CompactSetsSeparated) : Statement := fun s =>
  ⟨fun n hn => ⟨memCommonProduct_of_separated hsep s n,
      fun _ => ⟨isLinearInEachArgument_of_isTupleMultilinear hsep,
        isTupleMultilinear_of_isLinearInEachArgument⟩,
      fun Ψ Φ h => (((hU s).1 n hn).2 Ψ Φ h).1⟩,
    tuplesAgreeOnEuclidean_of_unified hU s, (hU s).2.2.1, partitionsAgree_holds,
    fun F G h => (hU s).2.2.2.1.2 F G h⟩
end YangMills.Construction.EntrywiseMultilinearity
end
