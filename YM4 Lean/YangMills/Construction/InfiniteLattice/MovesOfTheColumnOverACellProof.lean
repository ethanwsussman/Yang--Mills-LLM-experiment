import YangMills.Construction.InfiniteLattice.ChessboardEstimateAndRulesOnMirrorGridsProof
import YangMills.Construction.InfiniteLattice.IsometriesOnPlaquetteTermsAndReflectionIdentities
import YangMills.Construction.InfiniteLattice.MomentsOfTheColumnOverACellProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open InfiniteLattice (IsRegionMeasurable IsBoundedObservable IsBoundedlyLocalizedIn IsLocalizedAbove
  IsLocalizedBelow AmbientSpace halfSpacingTimes spacingMultiples halfSpaceAbove halfSpaceBelow
  regionSigma timeAxis timeReflect timeAxisPoint shift)
open scoped ComplexConjugate
noncomputable section
namespace MultipleReflections
namespace StackMoves
variable {D : Setup} (G : D.Grid) (k : Fin 4 → ℤ)
theorem symmetry_ext {r s : D.LatticeSymmetry} (h : r.toFun = s.toFun) : r = s := by apply _root_.YangMills.Construction.MultipleReflections.ChessboardBoundProof.latticeSymmetry_ext <;> assumption
def stackStep (i : ℤ) : spacingMultiples D.mesh :=
  ⟨(i : ℝ) * G.edge, by
    obtain ⟨N, -, hN⟩ := G.edgeMultiple.2
    have hs : G.edge = (N : ℝ) * D.mesh := hN
    refine ⟨i * N, ?_⟩
    rw [hs]
    push_cast
    ring⟩
theorem shift_eq_stackShift (w : spacingMultiples D.mesh) (i : ℤ) (h : (w : ℝ) = (i : ℝ) * G.edge) :
    shift (timeAxisPoint w) = G.stackShift i := by
  apply symmetry_ext
  funext x
  rw [G.stackShift_apply]
  change x + (Pi.single timeAxis (w : ℝ) : AmbientSpace) = _
  rw [h]
  congr 1
  funext μ
  by_cases hμ : μ = timeAxis
  · subst hμ
    simp
  · simp [Pi.single_eq_of_ne hμ]
theorem shift_neg_eq_stackShift (w : spacingMultiples D.mesh) (i : ℤ)
    (h : (w : ℝ) = (i : ℝ) * G.edge) :
    shift (-timeAxisPoint w) = G.stackShift (-i) := by
  apply symmetry_ext
  funext x
  rw [G.stackShift_apply]
  change x + -(Pi.single timeAxis (w : ℝ) : AmbientSpace) = _
  rw [h]
  congr 1
  funext μ
  by_cases hμ : μ = timeAxis
  · subst hμ
    simp
  · simp [Pi.single_eq_of_ne hμ]
theorem halfTimeAdd_wallTimeHalf (n i : ℤ) :
    InfiniteLattice.halfTimeAdd (G.wallTimeHalf k n) (stackStep G i) = G.wallTimeHalf k (n + i) := by
  apply Subtype.ext
  change G.wallTime k n + (i : ℝ) * G.edge = G.wallTime k (n + i)
  simp only [Setup.Grid.wallTime]
  push_cast
  ring
theorem stackReflect_eq_signedConj (n : ℤ) (B : D.GaugeField → ℂ) :
    G.stackReflect k n B =
      Conventions.signedConjFun (-1) ((timeReflect (G.wallTimeHalf k n)).actOn B) := by
  funext U
  simp [Setup.Grid.stackReflect, Conventions.signedConjFun, Conventions.signedConj]
theorem stackReflectionsCompose_holds
    (hAlg : SymmetriesOnFacesAndReflectionIdentities.Statement) :
    G.StackReflectionsCompose k := by
  have hid := (hAlg D).2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n n' A hA
    have h := (hid (G.wallTimeHalf k n) (G.wallTimeHalf k n') (stackStep G 0)).2.1.2 A hA
    rw [shift_eq_stackShift G _ (2 * (n - n')) (by
      change 2 * (G.wallTime k n - G.wallTime k n') = _
      simp only [Setup.Grid.wallTime]
      push_cast
      ring)] at h
    rw [← h]
    funext U
    exact Complex.conj_conj _
  · intro n i A hA
    have h := (hid (G.wallTimeHalf k n) (G.wallTimeHalf k n) (stackStep G i)).2.2.1.2 A hA
    rw [shift_eq_stackShift G _ i rfl, shift_neg_eq_stackShift G _ i rfl] at h
    funext U
    exact congrArg conj (congrFun h U)
  · intro n i A hA
    have h := (hid (G.wallTimeHalf k n) (G.wallTimeHalf k n) (stackStep G i)).2.2.2.2 A hA
    rw [shift_eq_stackShift G _ i rfl, halfTimeAdd_wallTimeHalf] at h
    funext U
    exact congrArg conj (congrFun h U)
  · intro n A A' _ _
    funext U
    exact map_mul (starRingEnd ℂ) _ _
  · intro i A A' _ _
    rfl
theorem isBounded_image_of_abs_le {S : Set AmbientSpace} (hS : Bornology.IsBounded S)
    (f : AmbientSpace → AmbientSpace) (c : ℝ)
    (h : ∀ x μ, |f x μ| ≤ |x μ| + c) : Bornology.IsBounded (f '' S) := by
  obtain ⟨R, hR⟩ := hS.exists_norm_le
  refine isBounded_iff_forall_norm_le.2 ⟨max R 0 + |c|, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun μ => ?_
  have h1 : |x μ| ≤ R := (norm_le_pi_norm x μ).trans (hR x hx)
  have h2 := h x μ
  rw [Real.norm_eq_abs]
  linarith [le_max_left R 0, le_abs_self c]
theorem abs_timeReflect_le (s : halfSpacingTimes D.mesh) (x : AmbientSpace) (μ : Fin 4) :
    |(timeReflect s).toFun x μ| ≤ |x μ| + 2 * |(s : ℝ)| := by
  rw [InfiniteLattice.timeReflect_apply]
  by_cases hμ : μ = timeAxis
  · subst hμ
    have h : (x - (2 * (x timeAxis - (s : ℝ))) • (Pi.single timeAxis 1 : AmbientSpace))
        timeAxis = 2 * (s : ℝ) - x timeAxis := by
      simp
      ring
    rw [h]
    have := abs_sub (2 * (s : ℝ)) (x timeAxis)
    rw [abs_mul, abs_two] at this
    linarith
  · have h : (x - (2 * (x timeAxis - (s : ℝ))) • (Pi.single timeAxis 1 : AmbientSpace)) μ =
        x μ := by
      simp [Pi.single_eq_of_ne hμ]
    rw [h]
    have := abs_nonneg (s : ℝ)
    linarith
theorem timeReflect_apply_timeAxis (s : halfSpacingTimes D.mesh) (x : AmbientSpace) :
    (timeReflect s).toFun x timeAxis = 2 * (s : ℝ) - x timeAxis := by
  rw [InfiniteLattice.timeReflect_apply]
  simp
  ring
theorem conj_isBoundedObservable {S : Set AmbientSpace} {A : D.GaugeField → ℂ}
    (hA : IsBoundedObservable A) (hS : IsRegionMeasurable S A) :
    IsBoundedObservable (fun U => conj (A U)) ∧ IsRegionMeasurable S (fun U => conj (A U)) := by
  obtain ⟨hm, C, hC⟩ := hA
  exact ⟨⟨Complex.continuous_conj.measurable.comp hm, C, fun U => by simpa using hC U⟩,
    Complex.continuous_conj.measurable.comp hS⟩
theorem stackReflectionsCrossWalls_holds
    (hObs : InfiniteLattice.SmearedEnergyAndSymmetryAction.Main) :
    G.StackReflectionsCrossWalls k := by
  have ha : 0 < D.mesh :=
    CutoffLattice.spacingAt_pos D.isAdmissible (D.K : ℕ)
  have hAct := (hObs D.mesh ha).2.1
  refine ⟨?_, ?_, ?_⟩
  · rintro n Z ⟨hZ, S, hS, hB, hM⟩
    obtain ⟨-, -, -, h⟩ := hAct (timeReflect (G.wallTimeHalf k n))
    obtain ⟨h1, h2, -⟩ := h S Z hZ hM
    obtain ⟨h3, h4⟩ := conj_isBoundedObservable h1 h2
    refine ⟨h3, _, ?_, isBounded_image_of_abs_le hB _ _ (abs_timeReflect_le _), h4⟩
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x timeAxis < (G.wallTimeHalf k n : ℝ) := hS hx
    change ((G.wallTimeHalf k n : ℝ)) < (timeReflect (G.wallTimeHalf k n)).toFun x timeAxis
    rw [timeReflect_apply_timeAxis]
    linarith
  · rintro n Z ⟨hZ, S, hS, hB, hM⟩
    obtain ⟨-, -, -, h⟩ := hAct (timeReflect (G.wallTimeHalf k n))
    obtain ⟨h1, h2, -⟩ := h S Z hZ hM
    obtain ⟨h3, h4⟩ := conj_isBoundedObservable h1 h2
    refine ⟨h3, _, ?_, isBounded_image_of_abs_le hB _ _ (abs_timeReflect_le _), h4⟩
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (G.wallTimeHalf k n : ℝ) < x timeAxis := hS hx
    change (timeReflect (G.wallTimeHalf k n)).toFun x timeAxis < (G.wallTimeHalf k n : ℝ)
    rw [timeReflect_apply_timeAxis]
    linarith
  · rintro i A ⟨hA, S, hS, hB, hM⟩
    obtain ⟨-, -, -, h⟩ := hAct (G.stackShift i)
    obtain ⟨h1, h2, -⟩ := h S A hA hM
    refine ⟨h1, _, ?_, isBounded_image_of_abs_le hB _ |(i : ℝ) * G.edge| ?_, h2⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : (G.wallTimeHalf k 0 : ℝ) < x timeAxis := hS hx
      have hz : (G.wallTimeHalf k 0 : ℝ) = G.baseTime k := G.wallTimeHalf_zero k
      change G.wallTime k i < (G.stackShift i).toFun x timeAxis
      rw [G.stackShift_apply]
      simp only [Setup.Grid.wallTime]
      simp
      linarith
    · intro x μ
      rw [G.stackShift_apply]
      by_cases hμ : μ = timeAxis
      · subst hμ
        simpa using abs_add_le (x timeAxis) ((i : ℝ) * G.edge)
      · simp [Pi.single_eq_of_ne hμ]
        positivity
theorem stackIndex_sub (i i' : ℤ) (α : Fin 4) :
    Setup.Grid.stackIndex k i' α - Setup.Grid.stackIndex k i α =
      if α = timeAxis then i' - i else 0 := by
  by_cases hα : α = timeAxis
  · subst hα
    simp [Setup.Grid.stackIndex]
  · simp [Setup.Grid.stackIndex, hα]
theorem tileSign_stackIndex (i i' : ℤ) :
    Setup.Grid.tileSign (Setup.Grid.stackIndex k i) (Setup.Grid.stackIndex k i') =
      (-1) ^ (i' - i) := by
  unfold Setup.Grid.tileSign
  congr 1
  simp only [stackIndex_sub]
  simp
theorem tileSymmetry_eq_timeReflect (n i : ℤ) :
    G.tileSymmetry (Setup.Grid.stackIndex k i) (Setup.Grid.stackIndex k (2 * n + 1 - i)) =
      timeReflect (G.wallTimeHalf k n) := by
  apply symmetry_ext
  funext x α
  change G.tileReflection _ _ x α = _
  rw [InfiniteLattice.timeReflect_apply]
  simp only [Setup.Grid.tileReflection, stackIndex_sub]
  by_cases hα : α = timeAxis
  · subst hα
    have hodd : ¬ Even (2 * n + 1 - i - i) := by
      rw [Int.not_even_iff_odd]
      exact ⟨n - i, by ring⟩
    have hc : (G.wallTimeHalf k n : ℝ) = G.wallTime k n := rfl
    rw [if_pos rfl, if_neg hodd, hc]
    simp only [Setup.Grid.wallTime, Setup.Grid.baseTime_eq, Setup.Grid.stackIndex]
    simp
    ring
  · simp [hα]
theorem tileSymmetry_eq_stackShift (m i : ℤ) :
    G.tileSymmetry (Setup.Grid.stackIndex k i) (Setup.Grid.stackIndex k (i + 2 * m)) =
      G.stackShift (2 * m) := by
  apply symmetry_ext
  funext x α
  change G.tileReflection _ _ x α = _
  rw [G.stackShift_apply]
  simp only [Setup.Grid.tileReflection, stackIndex_sub]
  by_cases hα : α = timeAxis
  · subst hα
    have heven : Even (i + 2 * m - i) := ⟨m, by ring⟩
    rw [if_pos rfl, if_pos heven]
    simp
  · simp [hα]
theorem reflectedCopy_move (hRule : G.ReflectedCopyRules) (hOne : G.UniqueElementBetweenTiles)
    {F : D.GaugeField → ℂ} (hF : F ∈ G.tileAlgebra k) (k' k'' : Fin 4 → ℤ) :
    Conventions.signedConjFun (Setup.Grid.tileSign k' k'')
      ((G.tileSymmetry k' k'').actOn (G.reflectedCopy k k' F)) = G.reflectedCopy k k'' F := by
  obtain ⟨g, hg, hmap, hsign⟩ := hOne k' k''
  have himg := (hg g).2 rfl
  have h := (hRule k k' F hF).2.2.2 g k'' himg
  have hunit : G.orientationUnit g = Setup.Grid.tileSign k' k'' := by
    unfold Setup.Grid.orientationUnit
    rcases Int.units_eq_one_or (Setup.Grid.tileSign k' k'') with h1 | h1
    · rw [h1] at hsign ⊢
      simp [hsign]
    · rw [h1] at hsign ⊢
      have : G.orientation g ≠ 1 := by
        rw [hsign]
        norm_num
      simp [this]
  have hiso : G.toLatticeSymmetry D.isAdmissible g = G.tileSymmetry k' k'' :=
    symmetry_ext hmap
  rw [hunit, hiso] at h
  exact h
theorem stackReflect_stackCopy (hRule : G.ReflectedCopyRules) (hOne : G.UniqueElementBetweenTiles)
    {F : D.GaugeField → ℂ} (hF : F ∈ G.tileAlgebra k) (n i : ℤ) :
    G.stackReflect k n (G.stackCopy k F i) = G.stackCopy k F (2 * n + 1 - i) := by
  have h := reflectedCopy_move G k hRule hOne hF (Setup.Grid.stackIndex k i)
    (Setup.Grid.stackIndex k (2 * n + 1 - i))
  rw [tileSymmetry_eq_timeReflect, tileSign_stackIndex] at h
  have hs : (-1 : ℤˣ) ^ (2 * n + 1 - i - i) = -1 :=
    Odd.neg_one_zpow ⟨n - i, by ring⟩
  rw [hs] at h
  rw [stackReflect_eq_signedConj]
  exact h
theorem stackShift_stackCopy (hRule : G.ReflectedCopyRules) (hOne : G.UniqueElementBetweenTiles)
    {F : D.GaugeField → ℂ} (hF : F ∈ G.tileAlgebra k) (m i : ℤ) :
    (G.stackShift (2 * m)).actOn (G.stackCopy k F i) =
      G.stackCopy k F (i + 2 * m) := by
  have h := reflectedCopy_move G k hRule hOne hF (Setup.Grid.stackIndex k i)
    (Setup.Grid.stackIndex k (i + 2 * m))
  rw [tileSymmetry_eq_stackShift, tileSign_stackIndex] at h
  have hs : (-1 : ℤˣ) ^ (i + 2 * m - i) = 1 :=
    Even.neg_one_zpow ⟨m, by ring⟩
  rw [hs] at h
  have h1 : ∀ f : D.GaugeField → ℂ, Conventions.signedConjFun (1 : ℤˣ) f = f := fun f => by
    funext U
    simp [Conventions.signedConjFun, Conventions.signedConj]
  rw [h1] at h
  exact h
theorem prod_isBoundedObservable {S : Set AmbientSpace} (f : ℤ → D.GaugeField → ℂ) (s : Finset ℤ)
    (h : ∀ i ∈ s, IsBoundedObservable (f i) ∧ IsRegionMeasurable S (f i)) :
    IsBoundedObservable (fun U => ∏ i ∈ s, f i U) ∧
      IsRegionMeasurable S (fun U => ∏ i ∈ s, f i U) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact ⟨⟨measurable_const, 1, fun _ => by simp⟩, measurable_const⟩
  | insert i s hi ih =>
    obtain ⟨⟨hm, C, hC⟩, hS⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨⟨hm', C', hC'⟩, hS'⟩ := h i (Finset.mem_insert_self i s)
    simp only [Finset.prod_insert hi]
    refine ⟨⟨hm'.mul hm, |C'| * |C|, fun U => ?_⟩, Measurable.mul hS' hS⟩
    rw [norm_mul]
    exact mul_le_mul ((hC' U).trans (le_abs_self C')) ((hC U).trans (le_abs_self C))
      (norm_nonneg _) (abs_nonneg _)
theorem regionSigma_mono {S S' : Set AmbientSpace} (h : S ⊆ S') :
    (regionSigma S : MeasurableSpace D.GaugeField) ≤ regionSigma S' := by apply _root_.YangMills.Construction.MultipleReflections.StackCorrelations.regionSigma_mono <;> assumption
theorem tileInterior_isBounded (q : Fin 4 → ℤ) : Bornology.IsBounded (G.tileInterior q) := by
  refine (Metric.isBounded_Icc (G.cornerAt q) (fun μ => G.cornerAt q μ + G.edge)).subset ?_
  intro x hx
  exact ⟨fun μ => (hx μ).1.le, fun μ => (hx μ).2.le⟩
theorem tileInterior_subset_stackSlab {i₁ i₂ i : ℤ} (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) :
    G.tileInterior (Setup.Grid.stackIndex k i) ⊆ G.stackSlab k i₁ i₂ := by
  intro x hx
  have hs := G.edge_pos
  have hc : G.cornerAt (Setup.Grid.stackIndex k i) timeAxis = G.wallTime k (i - 1) := by
    simp only [Setup.Grid.wallTime, Setup.Grid.baseTime_eq, InfiniteLattice.ReflectionGrid.cornerAt,
      Setup.Grid.stackIndex]
    simp
    ring
  obtain ⟨hx1, hx2⟩ := hx timeAxis
  rw [hc] at hx1 hx2
  have h₁' : ((i₁ : ℝ)) ≤ i := by exact_mod_cast h₁
  have h₂' : ((i : ℝ)) ≤ i₂ := by exact_mod_cast h₂
  simp only [Setup.Grid.wallTime] at hx1 hx2
  refine ⟨?_, ?_⟩
  · simp only [Setup.Grid.wallTime]
    push_cast at hx1 ⊢
    nlinarith
  · simp only [Setup.Grid.wallTime]
    push_cast at hx2 ⊢
    nlinarith
theorem stackCopiesMove_holds (hRule : G.ReflectedCopyRules)
    (hOne : G.UniqueElementBetweenTiles) {F : D.GaugeField → ℂ}
    (hF : F ∈ G.tileAlgebra k) : G.StackCopiesMove k F := by
  refine ⟨?_, stackReflect_stackCopy G k hRule hOne hF,
    fun m i => stackShift_stackCopy G k hRule hOne hF m i, ?_, ?_, ?_⟩
  · change G.reflectedCopy k (Setup.Grid.stackIndex k 1) F = F
    rw [Setup.Grid.stackIndex_one]
    exact (hRule k k F hF).2.1
  · intro n i₁ i₂ _
    funext U
    have h : ∀ i, conj (G.stackCopy k F i
        ((timeReflect (G.wallTimeHalf k n)).pullbackField U)) =
        G.stackCopy k F (2 * n + 1 - i) U := fun i =>
      congrFun (stackReflect_stackCopy G k hRule hOne hF n i) U
    change conj (∏ i ∈ Finset.Icc i₁ i₂, G.stackCopy k F i
      ((timeReflect (G.wallTimeHalf k n)).pullbackField U)) =
        ∏ i ∈ Finset.Icc (2 * n + 1 - i₂) (2 * n + 1 - i₁), G.stackCopy k F i U
    rw [map_prod]
    simp only [h]
    refine Finset.prod_nbij' (fun i => 2 * n + 1 - i) (fun i => 2 * n + 1 - i) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_Icc] at hi ⊢
      omega
    · intro i hi
      rw [Finset.mem_Icc] at hi ⊢
      omega
    · intro i _
      ring
    · intro i _
      ring
    · intro i _
      rfl
  · intro m i₁ i₂ _
    funext U
    have h : ∀ i, G.stackCopy k F i ((G.stackShift (2 * m)).pullbackField U) =
        G.stackCopy k F (i + 2 * m) U := fun i =>
      congrFun (stackShift_stackCopy G k hRule hOne hF m i) U
    change ∏ i ∈ Finset.Icc i₁ i₂, G.stackCopy k F i
      ((G.stackShift (2 * m)).pullbackField U) =
        ∏ i ∈ Finset.Icc (i₁ + 2 * m) (i₂ + 2 * m), G.stackCopy k F i U
    simp only [h]
    refine Finset.prod_nbij' (fun i => i + 2 * m) (fun i => i - 2 * m) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_Icc] at hi ⊢
      omega
    · intro i hi
      rw [Finset.mem_Icc] at hi ⊢
      omega
    · intro i _
      ring
    · intro i _
      ring
    · intro i _
      rfl
  · intro i₁ i₂ _
    set S : Set AmbientSpace :=
      ⋃ i ∈ Finset.Icc i₁ i₂, G.tileInterior (Setup.Grid.stackIndex k i) with hSdef
    have hp := prod_isBoundedObservable (S := S) (fun i => G.stackCopy k F i) (Finset.Icc i₁ i₂)
      (fun i hi => by
        obtain ⟨h1, h2⟩ : G.IsTileObservable (Setup.Grid.stackIndex k i) (G.stackCopy k F i) :=
          (hRule k _ F hF).1
        exact ⟨h1, Measurable.mono h2 (regionSigma_mono (Set.subset_biUnion_of_mem
          (u := fun i => G.tileInterior (Setup.Grid.stackIndex k i)) (by exact_mod_cast hi)))
            le_rfl⟩)
    refine ⟨hp.1, S, ?_, ?_, hp.2⟩
    · refine Set.iUnion₂_subset fun i hi => ?_
      rw [Finset.mem_Icc] at hi
      exact tileInterior_subset_stackSlab G k hi.1 hi.2
    · exact (Bornology.isBounded_biUnion_finset _).2 fun i _ => tileInterior_isBounded G _
end StackMoves
theorem stackMovesHold_proof
    (hAlg : SymmetriesOnFacesAndReflectionIdentities.Statement)
    (hRules : GridGroupAndBoxTiles)
    (hFacts : GridElementaryFacts)
    (hObs : InfiniteLattice.SmearedEnergyAndSymmetryAction.Main) :
    StackMovesHold := by
  intro D G k
  obtain ⟨⟨q, hq⟩, -⟩ := G.isTileEdge_edge
  obtain ⟨-, -, -, hRule, -⟩ := hRules D G q hq
  obtain ⟨-, -, -, hOne, -⟩ := hFacts D G q hq
  exact ⟨StackMoves.stackReflectionsCompose_holds G k hAlg,
    StackMoves.stackReflectionsCrossWalls_holds G k hObs,
    fun F hF => StackMoves.stackCopiesMove_holds G k hRule hOne hF⟩
end MultipleReflections
end
end YangMills.Construction
