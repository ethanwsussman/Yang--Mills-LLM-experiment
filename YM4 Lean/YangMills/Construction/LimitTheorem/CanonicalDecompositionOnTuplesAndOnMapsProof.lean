import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBoundedProof
import YangMills.Construction.SystemsWithFiveBounds.CanonicalDecompositionAlongStatesProof
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
namespace YangMills.Construction.LimitTheorem.DecompositionOnListsAndMaps
open YangMills.Construction.TestSpaces (SepTupleOfCard sepTupleNil centredOfCumulants)
open YangMills.Construction.SeparatedTuples (DecompositionData TupleFunctional IterLimitsExist
  iterLimitValue iteratedLimitAtInfinity measureSupport atInfinityWithin_univ
  eventually_cons_mem_iterLimitDomain)
open YangMills.Construction.CanonicalDecomposition (DecompositionTriple IteratedLimitsExist
  IsAdmissibleShifts iterLimit partialLimit)
open YangMills.Construction.TupleLists (toList ofList toList_ofList ofList_toList)
open YangMills.Construction.WightmanReconstruction (permuteComponents IsPermutationInvariant)
theorem evalOnMap_ofList (F : TupleFunctional) (X : SeparatedTuples.SepTuple) :
    evalOnMap F (ofList X) = F X := by apply _root_.YangMills.SharedProofs.p25328 <;> assumption
theorem evalOnMap_injective : Function.Injective evalOnMap := by
  intro F F' h
  have hf : ∀ X, F X = F' X := fun X => by
    rw [← evalOnMap_ofList F X, h, evalOnMap_ofList]
  obtain ⟨f, hf₀⟩ := F
  obtain ⟨g, hg₀⟩ := F'
  obtain rfl : f = g := funext hf
  rfl
theorem measureSupport_eq_probabilitySupport {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.MetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] :
    measureSupport μ = Measures.probabilitySupport μ := by
  ext y
  simp only [measureSupport, Measures.probabilitySupport, Set.mem_compl_iff,
    Set.mem_sUnion, Set.mem_ofPred_eq, not_exists, not_and]
  constructor
  · intro h O hO hy
    exact pos_iff_ne_zero.2 fun h0 => h O ⟨hO, h0⟩ hy
  · rintro h O ⟨hO, h0⟩ hy
    exact (h O hO hy).ne' h0
theorem ofFn_eq_take_append_cons_drop {α : Type*} {n : ℕ} (Y Z : Fin n → α) (i : Fin n)
    (h : ∀ j, j ≠ i → Y j = Z j) :
    List.ofFn Y = (List.ofFn Z).take i ++ Y i :: (List.ofFn Z).drop (i + 1) := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.ofFn_eq_take_append_cons_drop_of_eq <;> assumption
theorem isMultilinearOnSep_evalOnMap {F : TupleFunctional} (h : F.IsEntrywiseLinear) (n : ℕ) :
    TestSpaces.IsMultilinearOnSep fun X : SepTupleOfCard n => evalOnMap F ⟨n, X⟩ := by
  intro i b b' X X' X'' hXX' hi hj
  have e₁ := ofFn_eq_take_append_cons_drop X.1 X.1 i fun _ _ => rfl
  have e₂ := ofFn_eq_take_append_cons_drop X'.1 X.1 i fun j hj => (hXX' j hj).symm
  have e₃ := ofFn_eq_take_append_cons_drop X''.1 X.1 i hj
  rw [hi] at e₃
  exact h _ _ _ _ b b' (toList ⟨n, X⟩) (toList ⟨n, X'⟩) (toList ⟨n, X''⟩) e₁ e₂ e₃
theorem exists_eq_ofList_of_length_eq (T : SeparatedTuples.SepTuple) {n : ℕ} (h : T.1.length = n) :
    ∃ Y : SepTupleOfCard n, ofList T = ⟨n, Y⟩ ∧ ∀ k : Fin n, T.1[k.1]? = some (Y.1 k) := by
  subst h
  refine ⟨(ofList T).2, rfl, fun k => ?_⟩
  simp [ofList]
theorem getElem?_append_cons_congr {α : Type*} (A B : List α) (f f' : α) {j : ℕ}
    (hj : j ≠ A.length) : (A ++ f :: B)[j]? = (A ++ f' :: B)[j]? := by
  rcases lt_or_gt_of_ne hj with h | h
  · rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · obtain ⟨m, rfl⟩ : ∃ m, j = A.length + (m + 1) := ⟨j - A.length - 1, by omega⟩
    have hm : A.length + (m + 1) - A.length = m + 1 := by omega
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hm]
    simp only [List.getElem?_cons_succ]
theorem getElem?_append_cons_self {α : Type*} (A B : List α) (f : α) :
    (A ++ f :: B)[A.length]? = some f := by
  simp
theorem isEntrywiseLinear_of_evalOnMap {F : TupleFunctional}
    (h : ∀ n, 1 ≤ n → TestSpaces.IsMultilinearOnSep fun X : SepTupleOfCard n => evalOnMap F ⟨n, X⟩) :
    F.IsEntrywiseLinear := by
  intro A B f f' α α' X X' Z hX hX' hZ
  obtain ⟨n, hn⟩ : ∃ n, n = A.length + 1 + B.length := ⟨_, rfl⟩
  obtain ⟨Y, eY, gY⟩ := exists_eq_ofList_of_length_eq X (n := n) (by simp [hX, hn]; omega)
  obtain ⟨Y', eY', gY'⟩ := exists_eq_ofList_of_length_eq X' (n := n) (by simp [hX', hn]; omega)
  obtain ⟨W, eW, gW⟩ := exists_eq_ofList_of_length_eq Z (n := n) (by simp [hZ, hn]; omega)
  rw [hX] at gY
  rw [hX'] at gY'
  rw [hZ] at gW
  have key := h n (by omega) ⟨A.length, by omega⟩ α α' Y Y' W ?_ ?_ ?_
  · simp only at key
    rw [← eY, ← eY', ← eW, evalOnMap_ofList, evalOnMap_ofList, evalOnMap_ofList] at key
    exact key
  · intro j hj
    have hj' : j.1 ≠ A.length := fun e => hj (Fin.ext e)
    have e₁ := gY j
    have e₂ := gY' j
    rw [getElem?_append_cons_congr A B f f' hj', e₂] at e₁
    exact (Option.some.inj e₁).symm
  · have e₁ := gY ⟨A.length, by omega⟩
    have e₂ := gY' ⟨A.length, by omega⟩
    have e₃ := gW ⟨A.length, by omega⟩
    simp only [getElem?_append_cons_self] at e₁ e₂ e₃
    rw [← Option.some.inj e₁, ← Option.some.inj e₂, ← Option.some.inj e₃]
  · intro j hj
    have hj' : j.1 ≠ A.length := fun e => hj (Fin.ext e)
    have e₁ := gY j
    have e₃ := gW j
    rw [getElem?_append_cons_congr A B _ f hj', e₁] at e₃
    exact (Option.some.inj e₃).symm
theorem toList_permuteComponents (T : SeparatedTuples.SepTuple) (ς : Equiv.Perm (Fin T.1.length)) :
    toList ⟨T.1.length, permuteComponents (ofList T).2 ς⟩ = T.reorder ς :=
  Subtype.ext rfl
theorem isPermutationInvariant_evalOnMap {F : TupleFunctional} (h : F.IsPermInvariant) :
    IsPermutationInvariant (evalOnMap F) := by apply _root_.YangMills.SharedProofs.p108250 <;> assumption
theorem isPermInvariant_of_evalOnMap {F : TupleFunctional}
    (h : IsPermutationInvariant (evalOnMap F)) : F.IsPermInvariant := by
  intro T ς
  by_cases hn : 1 ≤ T.1.length
  · have key := h T.1.length hn (ofList T).2 ς
    have e : evalOnMap F ⟨T.1.length, permuteComponents (ofList T).2 ς⟩ = F (T.reorder ς) :=
      congrArg (fun Z : SeparatedTuples.SepTuple => F Z) (toList_permuteComponents T ς)
    exact e.symm.trans (key.trans (evalOnMap_ofList F T))
  · have h0 : T.1 = [] := List.eq_nil_of_length_eq_zero (by omega)
    have e₁ : (T.reorder ς).1 = [] :=
      List.eq_nil_of_length_eq_zero (by simp [SeparatedTuples.SepTuple.reorder]; omega)
    have e : T.reorder ς = T := Subtype.ext (e₁.trans h0.symm)
    rw [e]
theorem iteratedLimitsExist_of_iterLimitsExist (S : CumulantFamily) (X : TestSpaces.SepTuple)
    (Y : List TestSpaces.SepTuple)
    (h : IterLimitsExist (centredOf S) (toList X) (Y.map toList) Set.univ) :
    IteratedLimitsExist X Y (centredOfCumulants S) := by
  intro k hk vs hvs
  have hk' : k < (Y.map toList).length := by simpa using hk
  refine ⟨?_, ?_⟩
  · have hev := eventually_cons_mem_iterLimitDomain (toList X) (Y.map toList) Set.univ hk' hvs
    rw [atInfinityWithin_univ] at hev
    obtain ⟨t, ht, hsub⟩ := Filter.mem_comap.1 hev
    obtain ⟨a, ha⟩ := mem_atTop_sets.1 ht
    exact ⟨a, fun v hv => hsub (ha _ hv)⟩
  · obtain ⟨c, hc⟩ := h k hk' vs hvs
    rw [atInfinityWithin_univ] at hc
    exact ⟨c, hc⟩
theorem map_toList_map_ofList (Y : List SeparatedTuples.SepTuple) :
    (Y.map ofList).map toList = Y := by
  simp [List.map_map, Function.comp_def, toList_ofList]
theorem iterLimitsExist_of_iteratedLimitsExist (S : CumulantFamily) (X : SeparatedTuples.SepTuple)
    (Y : List SeparatedTuples.SepTuple)
    (h : IteratedLimitsExist (ofList X) (Y.map ofList) (centredOfCumulants S)) :
    IterLimitsExist (centredOf S) X Y Set.univ := by
  intro k hk vs hvs
  have hk' : k < (Y.map ofList).length := by simpa using hk
  have hvs' : IsAdmissibleShifts (ofList X) (Y.map ofList) (k + 1) vs := by
    unfold IsAdmissibleShifts
    rw [toList_ofList, map_toList_map_ofList]
    exact hvs
  obtain ⟨c, hc⟩ := (h k hk' vs hvs').2
  refine ⟨c, ?_⟩
  rw [atInfinityWithin_univ]
  unfold partialLimit at hc
  rw [toList_ofList, map_toList_map_ofList] at hc
  exact hc
theorem iterLimit_eq_iteratedLimitAtInfinity (S : CumulantFamily) (X : TestSpaces.SepTuple)
    (Y : List TestSpaces.SepTuple) :
    iterLimit X Y (centredOfCumulants S) =
      iteratedLimitAtInfinity (centredOf S) (toList X) (Y.map toList) Set.univ := by
  unfold iteratedLimitAtInfinity
  rw [List.length_map]
  rfl
theorem isCanonical_iff_mapTriple (S : CumulantFamily) (A : DecompositionData) :
    A.IsCanonical (centredOf S) ↔ (mapTriple A).IsCanonical S := by
  constructor
  · intro h
    have := h.metrizable
    have := h.isProb
    refine
      { compact := h.compact
        metrizable := h.metrizable
        isProbability := h.isProb
        support_eq_univ := (measureSupport_eq_probabilitySupport A.law).symm.trans h.measureSupport_eq
        comp_isSepFunctional := fun ξ =>
          ⟨?_, fun n _ => isMultilinearOnSep_evalOnMap (h.comp_entrywiseLinear ξ) n⟩
        comp_invariant := fun ξ => isPermutationInvariant_evalOnMap (h.comp_permInvariant ξ)
        continuous_comp := fun X => h.continuous_comp (toList X)
        injective_comp := fun ξ ξ' e => h.comp_injective (evalOnMap_injective e)
        limitsExist := fun X Y => iteratedLimitsExist_of_iterLimitsExist S X Y
          (h.iterLimits_exist (toList X) (Y.map toList))
        integral_prod_eq := fun X Y => ?_ }
    · change (A.comp ξ) (toList sepTupleNil) = 1
      rw [TupleLists.toList_sepTupleNil]
      exact (A.comp ξ).map_nil
    · have key := h.integral_comp_prod (toList X) (Y.map toList)
      rw [iterLimit_eq_iteratedLimitAtInfinity, ← key]
      simp only [List.map_map]
      rfl
  · intro h
    have := h.metrizable
    have := h.isProbability
    have : TopologicalSpace.MetrizableSpace A.space := h.metrizable
    have : IsProbabilityMeasure A.law := h.isProbability
    refine
      { compact := h.compact
        metrizable := h.metrizable
        isProb := h.isProbability
        measureSupport_eq := (measureSupport_eq_probabilitySupport A.law).trans h.support_eq_univ
        comp_permInvariant := fun ξ => isPermInvariant_of_evalOnMap (h.comp_invariant ξ)
        comp_entrywiseLinear := fun ξ => isEntrywiseLinear_of_evalOnMap (h.comp_isSepFunctional ξ).2
        continuous_comp := fun X => ?_
        comp_injective := fun ξ ξ' e => h.injective_comp (congrArg evalOnMap e)
        iterLimits_exist := fun X Y => iterLimitsExist_of_iteratedLimitsExist S X Y
          (h.limitsExist (ofList X) (Y.map ofList))
        integral_comp_prod := fun X Y => ?_ }
    · have key := h.continuous_comp (ofList X)
      have e : (fun ξ => (mapTriple A).comp ξ (ofList X)) = fun ξ => A.comp ξ X :=
        funext fun ξ => evalOnMap_ofList _ X
      rw [e] at key
      exact key
    · have key := h.integral_prod_eq (ofList X) (Y.map ofList)
      rw [iterLimit_eq_iteratedLimitAtInfinity, toList_ofList, map_toList_map_ofList] at key
      rw [← key]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      change A.comp ξ X * _ =
        evalOnMap (A.comp ξ) (ofList X) *
          ((Y.map ofList).map fun Z => evalOnMap (A.comp ξ) Z).prod
      rw [evalOnMap_ofList, List.map_map]
      congr 2
      exact List.map_congr_left fun Z _ => (evalOnMap_ofList _ Z).symm
theorem mapTriple_listData (B : DecompositionTriple) (h : ∀ ξ, B.comp ξ sepTupleNil = 1) :
    mapTriple (listData B h) = B := by
  obtain ⟨sp, μ, c⟩ := B
  have e : (fun ξ => evalOnMap (listFunctional (c ξ) (h ξ))) = c := by
    funext ξ X
    change c ξ (ofList (toList X)) = c ξ X
    rw [ofList_toList]
  simp only [mapTriple, listData, e]
theorem isomorphic_iff_mapTriple (A A' : DecompositionData) :
    A.Isomorphic A' ↔ (mapTriple A).Isomorphic (mapTriple A') := by
  constructor
  · rintro ⟨h, hm, hc⟩
    exact ⟨h, hm, fun ξ => congrArg evalOnMap (hc ξ)⟩
  · rintro ⟨h, hm, hc⟩
    exact ⟨h, hm, fun ξ => evalOnMap_injective (hc ξ)⟩
theorem listAndMapFormsAgree : ListAndMapFormsAgree :=
  ⟨isCanonical_iff_mapTriple, fun _ B _ => mapTriple_listData B _, isomorphic_iff_mapTriple⟩
end YangMills.Construction.LimitTheorem.DecompositionOnListsAndMaps
