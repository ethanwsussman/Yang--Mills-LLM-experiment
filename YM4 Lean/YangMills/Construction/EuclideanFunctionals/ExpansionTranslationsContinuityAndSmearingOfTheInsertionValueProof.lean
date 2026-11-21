import YangMills.Construction.TwoPoints.ConvolutionIsOfClassC1Proof
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.EuclideanFunctionals.BoundsAndContinuityOfTheMomentsProof
import YangMills.Construction.EuclideanFunctionals.ExpansionTranslationsContinuityAndSmearingOfTheInsertionValue
import YangMills.Construction.EuclideanFunctionals.InvarianceOfTheMomentsAndReductionToTheTimePlane
import YangMills.Construction.EuclideanFunctionals.SmearingOfTheMoments
import YangMills.Construction.RotationInvariance.FunctionalOnTuplesOfRealFunctionsProof
import Mathlib
set_option autoImplicit false
open Filter Topology MeasureTheory
open scoped ComplexConjugate Pointwise ENNReal
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.InsertionForm
open MotionMulRules (shiftFree shiftFn)
open Moments (momentAt)
open TensorComponents (IsComplexMultilinear)
theorem supp_eq_tsupport {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) : supp f = tsupport f :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
theorem mem_C1c_iff {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) :
    f ∈ C1c 𝕜 ↔ ContDiff ℝ 1 f ∧ HasCompactSupport f := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.mem_C1c_iff_contDiff <;> assumption
theorem ofRealFn_mem_C1c {f : R4 → ℝ} (hf : f ∈ C1c ℝ) :
    ofRealFn f ∈ C1c ℂ := by apply _root_.YangMills.Construction.EuclideanFunctionals.RealTuples.ofReal_mem_C1c <;> assumption
theorem supp_ofRealFn (f : R4 → ℝ) : supp (ofRealFn f) = supp f := by apply _root_.YangMills.Construction.EuclideanFunctionals.RealTuples.supp_ofReal <;> assumption
theorem re_mem_C1c {h : R4 → ℂ} (hh : h ∈ C1c ℂ) :
    (fun x => (h x).re) ∈ C1c ℝ := by
  rw [mem_C1c_iff] at hh ⊢
  exact ⟨Complex.reCLM.contDiff.comp hh.1, hh.2.comp_left (g := Complex.re) (by simp)⟩
theorem im_mem_C1c {h : R4 → ℂ} (hh : h ∈ C1c ℂ) :
    (fun x => (h x).im) ∈ C1c ℝ := by
  rw [mem_C1c_iff] at hh ⊢
  exact ⟨Complex.imCLM.contDiff.comp hh.1, hh.2.comp_left (g := Complex.im) (by simp)⟩
theorem supp_re_subset (h : R4 → ℂ) : supp (fun x => (h x).re) ⊆ supp h := by
  rw [supp_eq_tsupport, supp_eq_tsupport]
  refine closure_mono fun x hx hz => hx ?_
  simp [hz]
theorem supp_im_subset (h : R4 → ℂ) : supp (fun x => (h x).im) ⊆ supp h := by
  rw [supp_eq_tsupport, supp_eq_tsupport]
  refine closure_mono fun x hx hz => hx ?_
  simp [hz]
theorem tsupport_linComb_subset (z z' : ℂ) (h h' : R4 → ℂ) :
    tsupport (z • h + z' • h') ⊆ tsupport h ∪ tsupport h' := by
  refine closure_minimal (fun x hx => ?_) ((isClosed_tsupport h).union (isClosed_tsupport h'))
  by_contra hn
  rw [Set.mem_union, not_or] at hn
  apply hx
  simp [image_eq_zero_of_notMem_tsupport hn.1, image_eq_zero_of_notMem_tsupport hn.2]
theorem linComb_mem_C1c {h h' : R4 → ℂ} (hh : h ∈ C1c ℂ)
    (hh' : h' ∈ C1c ℂ) (z z' : ℂ) :
    z • h + z' • h' ∈ C1c ℂ := by
  rw [mem_C1c_iff] at hh hh' ⊢
  exact ⟨(contDiff_const.smul hh.1).add (contDiff_const.smul hh'.1),
    IsCompact.of_isClosed_subset (hh.2.union hh'.2) (isClosed_tsupport _)
      (tsupport_linComb_subset z z' h h')⟩
theorem supp_linComb_subset (z z' : ℂ) (h h' : R4 → ℂ) :
    supp (z • h + z' • h') ⊆ supp h ∪ supp h' := by
  simp only [supp_eq_tsupport]
  exact tsupport_linComb_subset z z' h h'
theorem isSlabInsert_linComb {c : ℝ} {h h' : R4 → ℂ} (hh : IsSlabInsert c h)
    (hh' : IsSlabInsert c h') (z z' : ℂ) : IsSlabInsert c (z • h + z' • h') :=
  ⟨linComb_mem_C1c hh.1 hh'.1 z z',
    (supp_linComb_subset z z' h h').trans (Set.union_subset hh.2 hh'.2)⟩
theorem isSlabInsert_zero {c : ℝ} : IsSlabInsert c 0 := by
  refine ⟨(mem_C1c_iff _).2 ⟨contDiff_const, HasCompactSupport.zero⟩, ?_⟩
  rw [supp_eq_tsupport]
  simp [tsupport]
theorem termFns_length (X Y : FnList) (h : R4 → ℂ) :
    (termFns X Y h).length = X.length + 1 + Y.length := by
  simp [termFns]
  omega
def insertIdx (X Y : FnList) : Fin (X.length + 1 + Y.length) := ⟨X.length, by omega⟩
def entryFn (X Y : FnList) (h : R4 → ℂ) (l : Fin (X.length + 1 + Y.length)) : R4 → ℂ :=
  (termFns X Y h)[l.1]'(by rw [termFns_length]; exact l.2)
theorem momentAt_eq_of_getElem (S : ConnFamily) (L : List (R4 → ℂ)) {n : ℕ} (e : L.length = n)
    (f : Fin n → R4 → ℂ) (hf : ∀ l : Fin n, f l = L[l.1]'(by omega)) :
    momentAt S L.get = momentAt S f := by
  subst e
  have : f = L.get := funext fun l => by rw [hf]; rfl
  rw [this]
theorem termMoment_eq (S : ConnFamily) (X Y : FnList) (h : R4 → ℂ) :
    termMoment S X Y h = momentAt S (entryFn X Y h) :=
  momentAt_eq_of_getElem S _ (termFns_length X Y h) _ fun _ => rfl
theorem componentFn_insertIdx (X Y : FnList) (h : R4 → ℂ) : entryFn X Y h (insertIdx X Y) = h := by
  simp [entryFn, insertIdx, termFns]
theorem componentFn_of_ne (X Y : FnList) (h h' : R4 → ℂ) {l : Fin (X.length + 1 + Y.length)}
    (hl : l ≠ insertIdx X Y) : entryFn X Y h l = entryFn X Y h' l := by
  have hne : l.1 ≠ X.length := fun e => hl (Fin.ext e)
  rcases lt_or_gt_of_ne hne with h1 | h1
  · simp [entryFn, termFns, List.getElem_append_left, h1]
  · have h0 : l.1 - X.length ≠ 0 := by omega
    simp [entryFn, termFns, List.getElem_append, List.getElem_cons, h0, Nat.not_lt.2 h1.le]
theorem componentFn_eq_update (X Y : FnList) (h h' : R4 → ℂ) :
    entryFn X Y h = Function.update (entryFn X Y h') (insertIdx X Y) h := by
  funext l
  by_cases hl : l = insertIdx X Y
  · subst hl
    simp [componentFn_insertIdx]
  · rw [Function.update_of_ne hl, componentFn_of_ne X Y h h' hl]
theorem complexFamily_of_list (L : List (R4 → ℂ)) {n : ℕ} (e : L.length = n) (hn : 1 ≤ n)
    (f : Fin n → R4 → ℂ) (hf : ∀ l : Fin n, f l = L[l.1]'(by omega))
    (hm : ∀ g ∈ L, g ∈ C1c ℂ)
    (hp : L.Pairwise fun a b => Disjoint (supp a) (supp b)) : ComplexComponents f := by
  subst e
  refine ⟨hn, fun l => ?_, fun k l hkl => ?_⟩
  · rw [hf]
    exact hm _ (List.getElem_mem _)
  · change Disjoint (supp (f k)) (supp (f l))
    rw [hf, hf]
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkl) with h1 | h1
    · exact (List.pairwise_iff_getElem.1 hp) k.1 l.1 _ _ h1
    · exact ((List.pairwise_iff_getElem.1 hp) l.1 k.1 _ _ h1).symm
theorem termFns_eq (X Y : FnList) (h : R4 → ℂ) :
    termFns X Y h =
      (X.map timeFlip.actFn).map ofRealFn ++ h :: Y.map ofRealFn := by
  simp [termFns, List.map_map, Function.comp_def]
theorem disjoint_lowerHalf_timeSlab {c : ℝ} : Disjoint (lowerHalf (-c)) (timeSlab c) :=
  Set.disjoint_left.2 fun x h1 h2 => by
    have h1' : x 3 < -c := h1
    have h2' : |x 3| < c := h2
    have := abs_lt.1 h2'
    linarith [this.1]
theorem disjoint_timeSlab_upperHalf {c : ℝ} : Disjoint (timeSlab c) (upperOpenHalf c) :=
  Set.disjoint_left.2 fun x h1 h2 => by
    have h1' : |x 3| < c := h1
    have h2' : c < x 3 := h2
    have := abs_lt.1 h1'
    linarith [this.2]
theorem disjoint_lowerHalf_upperHalf {c : ℝ} (hc : 0 < c) :
    Disjoint (lowerHalf (-c)) (upperOpenHalf c) :=
  Set.disjoint_left.2 fun x h1 h2 => by
    have h1' : x 3 < -c := h1
    have h2' : c < x 3 := h2
    linarith
structure PairSpec (c : ℝ) (X Y : FnList) : Prop where
  left_mem : X ∈ sepIn (upperOpenHalf c)
  flip_mem : X.map timeFlip.actFn ∈ sepIn (lowerHalf (-c))
  right_mem : Y ∈ sepIn (upperOpenHalf c)
section Entries
variable {c : ℝ} {X Y : FnList} {h : R4 → ℂ}
theorem termFns_mem (t : PairSpec c X Y) (hh : h ∈ C1c ℂ) :
    ∀ g ∈ termFns X Y h, g ∈ C1c ℂ := by
  intro g hg
  rw [termFns_eq] at hg
  rcases List.mem_append.1 hg with hg | hg
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    exact ofRealFn_mem_C1c ((isSeparatedList_of_mem_sepAll t.flip_mem.1).1 f hf)
  · rcases List.mem_cons.1 hg with rfl | hg
    · exact hh
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
      exact ofRealFn_mem_C1c ((isSeparatedList_of_mem_sepAll t.right_mem.1).1 f hf)
theorem termFns_pairwise (hc : 0 < c) (t : PairSpec c X Y)
    (hh : supp h ⊆ timeSlab c) :
    (termFns X Y h).Pairwise fun a b => Disjoint (supp a) (supp b) := by
  rw [termFns_eq]
  have sU := isSeparatedList_of_mem_sepAll t.flip_mem.1
  have sY := isSeparatedList_of_mem_sepAll t.right_mem.1
  have hd : ∀ a b : R4 → ℝ, Disjoint (supp a) (supp b) →
      Disjoint (supp (ofRealFn a)) (supp (ofRealFn b)) := fun a b hab => by
    rw [supp_ofRealFn, supp_ofRealFn]
    exact hab
  refine List.pairwise_append.2 ⟨List.pairwise_map.2 ?_, List.pairwise_cons.2 ⟨?_,
    List.pairwise_map.2 ?_⟩, ?_⟩
  · exact sU.2.imp (hd _ _)
  · intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    rw [supp_ofRealFn]
    exact disjoint_timeSlab_upperHalf.mono hh (t.right_mem.2 f hf)
  · exact sY.2.imp (hd _ _)
  · intro a ha b hb
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 ha
    rw [supp_ofRealFn]
    rcases List.mem_cons.1 hb with rfl | hb
    · exact disjoint_lowerHalf_timeSlab.mono (t.flip_mem.2 f hf) hh
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hb
      rw [supp_ofRealFn]
      exact (disjoint_lowerHalf_upperHalf hc).mono (t.flip_mem.2 f hf) (t.right_mem.2 g hg)
theorem complexFamily_componentFn (hc : 0 < c) (t : PairSpec c X Y)
    (hh : IsSlabInsert c h) : ComplexComponents (entryFn X Y h) :=
  complexFamily_of_list _ (termFns_length X Y h) (by omega) _ (fun _ => rfl)
    (termFns_mem t hh.1) (termFns_pairwise hc t hh.2)
theorem complexFamily_get (hc : 0 < c) (t : PairSpec c X Y)
    (hh : IsSlabInsert c h) : ComplexComponents (termFns X Y h).get :=
  complexFamily_of_list _ rfl (by rw [termFns_length]; omega) _ (fun _ => rfl)
    (termFns_mem t hh.1) (termFns_pairwise hc t hh.2)
theorem termFnsSpec_of (hc : 0 < c) (t : PairSpec c X Y) (hh : IsSlabInsert c h) :
    TermEntriesSpec c X Y h := by
  refine ⟨complexFamily_get hc t hh, fun l => ?_, fun f hf => ?_, hh.2,
    fun g hg => t.right_mem.2 g hg⟩
  · have hm := (complexFamily_get hc t hh).mem l
    rw [mem_C1c_iff] at hm
    rw [supp_eq_tsupport]
    exact hm.2
  · exact t.flip_mem.2 _ (List.mem_map.2 ⟨f, hf, rfl⟩)
end Entries
theorem freeMul_toFree {U V : FnList} (hU : U ∈ sepAll) (hV : V ∈ sepAll) :
    freeMul (toFree U) (toFree V) = toFree (U ++ V) := by apply _root_.YangMills.Construction.EuclideanFunctionals.RealTuples.freeMul_toFree <;> assumption
theorem singleton_mem_sepIn {f : R4 → ℝ} (hf : f ∈ C1c ℝ) {O : Set R4}
    (hO : supp f ⊆ O) : [f] ∈ sepIn O := by
  refine ⟨Set.mem_iUnion.2 ⟨1, rfl, ?_, List.pairwise_singleton _ _⟩, ?_⟩
  · intro g hg
    have hg' : g = f := List.mem_singleton.1 hg
    subst hg'
    exact hf
  · intro g hg
    have hg' : g = f := List.mem_singleton.1 hg
    subst hg'
    exact hO
theorem pairSpec_of (htuple : TupleRules.TupleSpanActionRules) {c : ℝ} {X Y : FnList}
    (hX : X ∈ sepIn (upperOpenHalf c)) (hY : Y ∈ sepIn (upperOpenHalf c)) :
    PairSpec c X Y := by
  refine ⟨hX, ?_, hY⟩
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hX.1
  have himg := (htuple.2.1 timeFlip (upperOpenHalf c) (isOpen_upperHalf c)).2.1 n
  have hmap := himg.1.mapsTo (show X ∈ sepNIn n (upperOpenHalf c) from ⟨hn, hX⟩)
  have hmir := htuple.2.2.2.2.2.2.2.2.1.2 c
  have h2 := hmap.2
  rw [hmir] at h2
  exact h2
theorem flipConj_toFree {X : FnList} (hX : X ∈ sepAll) :
    flipConj (toFree X) = toFree (X.map timeFlip.actFn) := by
  have h1 : freeConj (toFree X) = toFree X := by
    rw [toFree_of_mem hX, freeConj]
    simp
  rw [flipConj, h1]
  exact liftLin_toFree _ ⟨X, hX⟩
theorem freeConj_add (F G : FreeSep) : freeConj (F + G) = freeConj F + freeConj G :=
  Finsupp.mapRange_add (map_add _) F G
theorem freeConj_smul (z : ℂ) (F : FreeSep) : freeConj (z • F) = conj z • freeConj F := by
  ext X
  simp [freeConj]
def freeConjHom : FreeSep →+ FreeSep := AddMonoidHom.mk' freeConj freeConj_add
theorem flipConj_eval (s : FnListSum) (hs : ∀ ι, s.list ι ∈ sepAll) :
    flipConj s.eval =
      ∑ ι, conj (s.coeff ι) • toFree ((s.list ι).map timeFlip.actFn) := by
  have h1 : freeConj s.eval = ∑ ι, conj (s.coeff ι) • freeConj (toFree (s.list ι)) := by
    change freeConjHom s.eval = _
    rw [FnListSum.eval, map_sum]
    exact Finset.sum_congr rfl fun ι _ => freeConj_smul _ _
  rw [flipConj, h1, map_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [map_smul]
  congr 1
  exact flipConj_toFree (hs ι)
theorem singleComponent_ofRealFn (f : R4 → ℝ) :
    singleComponent (ofRealFn f) = toFree [f] := by
  have hr : ∀ _ : Fin 1, IsRealValued (ofRealFn f) := fun _ x => by
    simp [ofRealFn]
  rw [singleComponent, complexTuple, if_pos hr]
  simp [ofRealFn]
theorem singleComponent_of_not_real {h : R4 → ℂ} (hr : ¬ IsRealValued h) :
    singleComponent h =
      toFree [fun x => (h x).re] + Complex.I • toFree [fun x => (h x).im] := by
  classical
  rw [singleComponent, complexTuple, if_neg fun H => hr (H 0)]
  have hs : admissibleSigns (fun _ : Fin 1 => h) = Finset.univ := by
    ext ε
    simp [admissibleSigns, hr]
  rw [hs, ← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp, Fin.sum_univ_two]
  simp [reOrImPart]
theorem isRealValued_of_mem_termFunctions {X Y : FnList} {f : R4 → ℝ} {g : R4 → ℂ}
    (hg : g ∈ termFns X Y (ofRealFn f)) : IsRealValued g := by
  rw [termFns_eq] at hg
  rcases List.mem_append.1 hg with hg | hg
  · obtain ⟨f', _, rfl⟩ := List.mem_map.1 hg
    intro x
    simp [ofRealFn]
  · rcases List.mem_cons.1 hg with rfl | hg
    · intro x
      simp [ofRealFn]
    · obtain ⟨f', _, rfl⟩ := List.mem_map.1 hg
      intro x
      simp [ofRealFn]
theorem ofFn_map_getElem {α β : Type*} (g : α → β) (L : List α) {n : ℕ} (e : L.length = n) :
    List.ofFn (fun l : Fin n => g (L[l.1]'(by omega))) = L.map g := by
  subst e
  apply List.ext_getElem <;> simp
theorem complexTuple_componentFn_ofRealFn (X Y : FnList) (f : R4 → ℝ) :
    complexTuple (entryFn X Y (ofRealFn f)) =
      toFree (X.map timeFlip.actFn ++ f :: Y) := by
  have hr : ∀ l, IsRealValued (entryFn X Y (ofRealFn f) l) := fun l =>
    isRealValued_of_mem_termFunctions (List.getElem_mem _)
  rw [complexTuple, if_pos hr]
  congr 1
  have h := ofFn_map_getElem (fun (g : R4 → ℂ) x => (g x).re) (termFns X Y (ofRealFn f))
    (termFns_length X Y _)
  refine h.trans ?_
  rw [termFns_eq]
  simp [ofRealFn, Function.comp_def]
section Term
variable {c : ℝ} {X Y : FnList}
theorem freeMul3_ofRealFn (t : PairSpec c X Y) {f : R4 → ℝ}
    (hf : f ∈ C1c ℝ) (hs : supp f ⊆ timeSlab c) :
    freeMul3 (toFree (X.map timeFlip.actFn)) (toFree [f]) (toFree Y) =
      toFree (X.map timeFlip.actFn ++ f :: Y) := by
  have h0 := singleton_mem_sepIn hf hs
  have h1 := listAppend_mem_sepIn disjoint_lowerHalf_timeSlab t.flip_mem h0
  rw [freeMul3, freeMul_toFree t.flip_mem.1 h0.1,
    freeMul_toFree (U := X.map timeFlip.actFn ++ [f]) h1.1 t.right_mem.1]
  simp
theorem centered_freeMul3_ofRealFn (t : PairSpec c X Y) (S : ConnFamily) {f : R4 → ℝ}
    (hf : f ∈ C1c ℝ) (hs : supp f ⊆ timeSlab c) :
    centeredFnFree S
        (freeMul3 (toFree (X.map timeFlip.actFn)) (toFree [f]) (toFree Y)) =
      momentAt S (entryFn X Y (ofRealFn f)) := by
  rw [freeMul3_ofRealFn t hf hs, momentAt, complexTuple_componentFn_ofRealFn]
theorem isSlabInsert_ofRealFn {f : R4 → ℝ} (hf : f ∈ C1c ℝ)
    (hs : supp f ⊆ timeSlab c) : IsSlabInsert c (ofRealFn f) :=
  ⟨ofRealFn_mem_C1c hf, by rw [supp_ofRealFn]; exact hs⟩
theorem momentAt_componentFn_linComb (hc : 0 < c) (t : PairSpec c X Y) {S : ConnFamily}
    (hlin : IsComplexMultilinear S) {h h' : R4 → ℂ} (hh : IsSlabInsert c h)
    (hh' : IsSlabInsert c h') (z z' : ℂ) :
    momentAt S (entryFn X Y (z • h + z' • h')) =
      z * momentAt S (entryFn X Y h) + z' * momentAt S (entryFn X Y h') := by
  have A1 := complexFamily_componentFn hc t hh
  have A2 : ComplexComponents (Function.update (entryFn X Y h) (insertIdx X Y) h') := by
    rw [← componentFn_eq_update]
    exact complexFamily_componentFn hc t hh'
  have key := (hlin _ (insertIdx X Y) z z' (entryFn X Y h) h' A1 A2).2
  rw [componentFn_insertIdx, ← componentFn_eq_update, ← componentFn_eq_update] at key
  exact key
theorem centered_freeMul3_singleEntry (hc : 0 < c) (t : PairSpec c X Y) {S : ConnFamily}
    (hlin : IsComplexMultilinear S) {h : R4 → ℂ} (hh : IsSlabInsert c h) :
    centeredFnFree S
        (freeMul3 (toFree (X.map timeFlip.actFn)) (singleComponent h) (toFree Y)) =
      momentAt S (entryFn X Y h) := by
  have hre := re_mem_C1c hh.1
  have him := im_mem_C1c hh.1
  have hsre := (supp_re_subset h).trans hh.2
  have hsim := (supp_im_subset h).trans hh.2
  by_cases hr : IsRealValued h
  · have he : h = ofRealFn fun x => (h x).re := by
      funext x
      apply Complex.ext
      · simp [ofRealFn]
      · simpa [ofRealFn] using hr x
    rw [he, singleComponent_ofRealFn]
    exact centered_freeMul3_ofRealFn t S hre hsre
  · have he : h = (1 : ℂ) • ofRealFn (fun x => (h x).re) +
        Complex.I • ofRealFn fun x => (h x).im := by
      funext x
      simp [ofRealFn, mul_comm Complex.I]
    have hlinear := momentAt_componentFn_linComb hc t hlin (isSlabInsert_ofRealFn hre hsre)
      (isSlabInsert_ofRealFn him hsim) 1 Complex.I
    rw [← he] at hlinear
    rw [hlinear, singleComponent_of_not_real hr, ← centered_freeMul3_ofRealFn t S hre hsre,
      ← centered_freeMul3_ofRealFn t S him hsim]
    simp only [freeMul3, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, one_mul]
end Term
section Expansion
variable {c : ℝ} {S : ConnFamily}
theorem insertion_eq_sum (htuple : TupleRules.TupleSpanActionRules)
    (hlin : IsComplexMultilinear S) (hc : 0 < c) {s t : FnListSum}
    (hs : s.ListsIn (upperOpenHalf c)) (ht : t.ListsIn (upperOpenHalf c)) {h : R4 → ℂ}
    (hh : IsSlabInsert c h) :
    insertion S s.eval h t.eval =
      ∑ ι, ∑ κ, conj (s.coeff ι) * t.coeff κ *
        termMoment S (s.list ι) (t.list κ) h := by
  rw [insertion, flipConj_eval s fun ι => (hs ι).1, FnListSum.eval]
  simp only [freeMul3, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ι _ => Finset.sum_congr rfl fun κ _ => ?_
  have key := centered_freeMul3_singleEntry hc (pairSpec_of htuple (hs ι) (ht κ)) hlin hh
  rw [termMoment_eq, ← key, freeMul3]
  ring
theorem termMoment_nil_nil {M : SharpScale} (σ : EuclidFunctionalWithRecon M S)
    (hval : MotionMulRules.SingleEntryValueZero)
    {h : R4 → ℂ} (hh : h ∈ C1c ℂ) : termMoment S [] [] h = 0 := by
  have h1 : termMoment S [] [] h = momentAt S (fun _ : Fin 1 => h) :=
    momentAt_eq_of_getElem S _ (by simp [termFns]) _ fun l => by
      fin_cases l
      simp [termFns]
  rw [h1]
  exact hval M S σ 1 (fun _ => h)
    ⟨le_rfl, fun _ => hh, fun k l hkl => absurd (Subsingleton.elim k l) hkl⟩
theorem expansionHolds {M : SharpScale} (σ : EuclidFunctionalWithRecon M S)
    (htuple : TupleRules.TupleSpanActionRules)
    (hrules : MotionMulRules.MotionMulTupleRules)
    (hlin : IsComplexMultilinear S) (hc : 0 < c) (F A : FreeSep) : ExpansionHolds S c F A := by
  rintro s t hs ht rfl rfl h hh
  refine ⟨insertion_eq_sum htuple hlin hc hs ht hh,
    fun ι κ => termFnsSpec_of hc (pairSpec_of htuple (hs ι) (ht κ)) hh, fun ι κ h1 h2 => ?_⟩
  rw [h1, h2]
  exact termMoment_nil_nil σ hrules.2.2.2.2.2.1 hh.1
theorem linearInInsert (htuple : TupleRules.TupleSpanActionRules)
    (hlin : IsComplexMultilinear S) (hc : 0 < c) {F A : FreeSep}
    (hF : F ∈ finCombIn (upperOpenHalf c)) (hA : A ∈ finCombIn (upperOpenHalf c)) :
    LinearInInsert S c F A := by
  obtain ⟨s, hs, rfl⟩ := exists_fnListSum_eval_eq hF
  obtain ⟨t, ht, rfl⟩ := exists_fnListSum_eval_eq hA
  refine ⟨isSlabInsert_zero, fun z z' h h' hh hh' => ⟨isSlabInsert_linComb hh hh' z z', ?_⟩⟩
  rw [insertion_eq_sum htuple hlin hc hs ht (isSlabInsert_linComb hh hh' z z'),
    insertion_eq_sum htuple hlin hc hs ht hh,
    insertion_eq_sum htuple hlin hc hs ht hh', Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [termMoment_eq, termMoment_eq, termMoment_eq,
    momentAt_componentFn_linComb hc (pairSpec_of htuple (hs ι) (ht κ)) hlin hh hh' z z']
  ring
end Expansion
theorem timeFlip_neg (x : R4) : timeFlip (-x) = -timeFlip x := by
  rw [timeFlip_apply, timeFlip_apply]
  funext μ
  simp
  ring
theorem shiftFn_neg_shiftFn (x : R4) (k : R4 → ℂ) :
    shiftFn (-x) (shiftFn x k) = k := by
  funext y
  simp [shiftFn, EuclidMotion.actFn_transl]
theorem complexFamily_single {g : R4 → ℂ} (hg : g ∈ C1c ℂ) :
    ComplexComponents fun _ : Fin 1 => g :=
  ⟨le_rfl, fun _ => hg, fun k l hkl => absurd (Subsingleton.elim k l) hkl⟩
theorem shiftFn_mem_C1c {h : R4 → ℂ} (hh : h ∈ C1c ℂ) (y : R4) :
    shiftFn y h ∈ C1c ℂ := by
  rw [mem_C1c_iff] at hh ⊢
  have he : shiftFn y h = h ∘ Homeomorph.subRight y := by
    funext x
    simpa using EuclidMotion.actFn_transl y h x
  rw [he]
  exact ⟨hh.1.comp (contDiff_id.sub contDiff_const), hh.2.comp_homeomorph _⟩
theorem translationCovariance (htuple : TupleRules.TupleSpanActionRules)
    (hrules : MotionMulRules.MotionMulTupleRules) {S : ConnFamily}
    (hinv : MomentSymmetry.MotionInvariant S) {c : ℝ}
    (hc : 0 < c) {F A : FreeSep} (hF : F ∈ finCombIn (upperOpenHalf c))
    (hA : A ∈ finCombIn (upperOpenHalf c)) : TranslationCovariance S c F A := by
  obtain ⟨-, hThrough, -, hTuples, -, -, hTransMirror, hSupp, hGrow, hAbove, hOne, -⟩ := hrules
  intro x c' hc' hle k hk
  have hk' := (mem_C1c_iff _).1 hk.1
  have hs : supp (shiftFn x k) ⊆ timeSlab c := by
    rw [(hSupp k hk'.1.continuous hk'.2 x).1]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    have h1 : |a 3| < c' := hk.2 ha
    have h2 : |(a + b) 3| ≤ |a 3| + |b 3| := abs_add_le _ _
    change |(a + b) 3| < c
    linarith
  have hx3 : (-timeFlip x) 3 = x 3 := by
    rw [Pi.neg_apply, (spatialProj_timeFlip x).2, neg_neg]
  have habs := abs_le.1 (le_refl |x 3|)
  have hF' : shiftFree (-timeFlip x) F ∈ finCombIn (upperOpenHalf c') := by
    refine hGrow _ _ (isOpen_upperHalf _) (isOpen_upperHalf _) (fun y hy => ?_)
      (hAbove (-timeFlip x) c F hF).1
    have hy' : c + (-timeFlip x) 3 < y 3 := hy
    rw [hx3] at hy'
    change c' < y 3
    linarith
  have hA' : shiftFree (-x) A ∈ finCombIn (upperOpenHalf c') := by
    refine hGrow _ _ (isOpen_upperHalf _) (isOpen_upperHalf _) (fun y hy => ?_)
      (hAbove (-x) c A hA).1
    have hy' : c + (-x) 3 < y 3 := hy
    rw [Pi.neg_apply] at hy'
    change c' < y 3
    linarith
  refine ⟨hs, hF', hA', ?_⟩
  have hmem := shiftFn_mem_C1c hk.1 x
  have hdef := (hOne c hc _ hmem hs).2.2 F hF A hA
  have hPQA := (htuple.2.2.2.2.2.2.1 _ _ _ hdef).1
  rw [insertion, freeMul3, ← (hinv _).1 (-x)]
  change centeredFnFree S (shiftFree (-x) _) = _
  rw [(hThrough (-x) _ _ hPQA).2, (hThrough (-x) _ _ hdef.1).2, hTransMirror, timeFlip_neg,
    singleComponent,
    (hTuples 1 _ Set.univ (complexFamily_single hmem) isOpen_univ
      fun _ => Set.subset_univ _).2.2.2.2,
    shiftFn_neg_shiftFn]
  rfl
theorem zero_le_sharpNorm (M : SharpScale) (h : R4 → ℂ) : 0 ≤ M.sharpNorm h := by
  rw [SharpScale.sharpNorm_eq_max]
  exact le_max_of_le_left (Real.iSup_nonneg fun x => norm_nonneg _)
theorem exists_pos_le_setDistR4 {P Q : Set R4} (hP : IsCompact P) (hQ : IsCompact Q)
    (hPQ : Disjoint P Q) :
    ∃ d : ℝ, 0 < d ∧ ENNReal.ofReal d ≤ TestFunctions.setDistR4 P Q := by
  obtain ⟨δ, hδ, h⟩ := Metric.exists_pos_forall_lt_edist hP hQ.isClosed hPQ
  refine ⟨δ, by exact_mod_cast hδ, le_iInf₂ fun a ha => le_iInf₂ fun b hb => ?_⟩
  have hab := h a ha b hb
  rw [edist_dist, dist_eq_norm] at hab
  rw [ENNReal.ofReal_coe_nnreal]
  exact hab.le.trans
    (ENNReal.ofReal_le_ofReal (SeparatedTuplesR4.norm_le_euclidNormVec _))
theorem exists_separatedInBalls {q : ℕ} (hq : 2 ≤ q) {A : Fin q → Set R4}
    (hc : ∀ l, IsCompact (A l)) (hd : Pairwise fun k l => Disjoint (A k) (A l)) :
    ∃ R d : ℝ, 0 < R ∧ 0 < d ∧ Moments.SeparatedInBalls A R d := by
  have hb : ∀ l, ∃ C, ∀ x ∈ A l, ‖x‖ ≤ C := fun l => (hc l).isBounded.exists_norm_le
  choose C hC using hb
  have hpair : ∀ r : Fin q × Fin q, ∃ d : ℝ, 0 < d ∧
      (r.1 ≠ r.2 → ENNReal.ofReal d ≤ TestFunctions.setDistR4 (A r.1) (A r.2)) := by
    intro r
    by_cases hr : r.1 = r.2
    · exact ⟨1, one_pos, fun h => absurd hr h⟩
    · obtain ⟨d, hd₀, hd₁⟩ := exists_pos_le_setDistR4 (hc r.1) (hc r.2) (hd hr)
      exact ⟨d, hd₀, fun _ => hd₁⟩
  choose f hf₀ hf₁ using hpair
  have : Nonempty (Fin q × Fin q) :=
    ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  obtain ⟨r₀, hr₀⟩ := Finite.exists_min f
  refine ⟨2 * (∑ l, |C l|) + 1, f r₀, by positivity, hf₀ r₀, fun l => ⟨0, fun x hx => ?_⟩,
    fun k l hkl => ?_⟩
  · have h₁ := SeparatedTuplesR4.euclidNormVec_le_two_mul_norm (x - 0)
    have h₂ : ‖x - 0‖ ≤ ∑ l, |C l| := by
      rw [sub_zero]
      exact ((hC l x hx).trans (le_abs_self _)).trans
        (Finset.single_le_sum (f := fun l => |C l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ l))
    change TorusMetric.euclidNormVec (x - 0) ≤ _
    linarith
  · exact (ENNReal.ofReal_le_ofReal (hr₀ (k, l))).trans (hf₁ (k, l) hkl)
section Pairs
variable {c : ℝ} {X Y : FnList}
theorem componentFn_cases (k : R4 → ℂ) {l : Fin (X.length + 1 + Y.length)} (hl : l ≠ insertIdx X Y) :
    (∃ f ∈ X.map timeFlip.actFn, entryFn X Y k l = ofRealFn f) ∨
      ∃ f ∈ Y, entryFn X Y k l = ofRealFn f := by
  have hne : l.1 ≠ X.length := fun e => hl (Fin.ext e)
  rcases lt_or_gt_of_ne hne with h1 | h1
  · refine Or.inl ⟨(X.map timeFlip.actFn)[l.1]'(by simpa using h1), List.getElem_mem _, ?_⟩
    simp [entryFn, termFns, List.getElem_append_left, h1]
  · refine Or.inr ⟨Y[l.1 - X.length - 1]'(by have := l.2; omega), List.getElem_mem _, ?_⟩
    have h0 : l.1 - X.length ≠ 0 := by omega
    simp [entryFn, termFns, List.getElem_append, List.getElem_cons, h0, Nat.not_lt.2 h1.le]
theorem componentFn_disjoint_timeSlab (t : PairSpec c X Y) (k : R4 → ℂ)
    {l : Fin (X.length + 1 + Y.length)} (hl : l ≠ insertIdx X Y) :
    Disjoint (supp (entryFn X Y k l)) (timeSlab c) := by
  rcases componentFn_cases k hl with ⟨f, hf, he⟩ | ⟨f, hf, he⟩
  · rw [he, supp_ofRealFn]
    exact disjoint_lowerHalf_timeSlab.mono_left (t.flip_mem.2 f hf)
  · rw [he, supp_ofRealFn]
    exact disjoint_timeSlab_upperHalf.symm.mono_left (t.right_mem.2 f hf)
theorem componentFn_mem_C1c (t : PairSpec c X Y) {k : R4 → ℂ} (hk : k ∈ C1c ℂ)
    (l : Fin (X.length + 1 + Y.length)) : entryFn X Y k l ∈ C1c ℂ :=
  termFns_mem t hk _ (List.getElem_mem _)
theorem isCompact_supp_componentFn (t : PairSpec c X Y) {k : R4 → ℂ}
    (hk : k ∈ C1c ℂ) (l : Fin (X.length + 1 + Y.length)) :
    IsCompact (supp (entryFn X Y k l)) := by
  have := ((mem_C1c_iff _).1 (componentFn_mem_C1c t hk l)).2
  rw [supp_eq_tsupport]
  exact this
def entrySupports (X Y : FnList) (Q : Set R4) : Fin (X.length + 1 + Y.length) → Set R4 :=
  Function.update (fun l => supp (entryFn X Y 0 l)) (insertIdx X Y) Q
theorem isCompact_componentSupports (t : PairSpec c X Y) {Q : Set R4} (hQ : IsCompact Q)
    (l : Fin (X.length + 1 + Y.length)) : IsCompact (entrySupports X Y Q l) := by
  by_cases hl : l = insertIdx X Y
  · subst hl
    simpa [entrySupports] using hQ
  · simp only [entrySupports, Function.update_of_ne hl]
    exact isCompact_supp_componentFn t ((mem_C1c_iff _).2 ⟨contDiff_const, HasCompactSupport.zero⟩) l
theorem pairwise_disjoint_componentSupports (hc : 0 < c) (t : PairSpec c X Y) {Q : Set R4}
    (hQ : Q ⊆ timeSlab c) :
    Pairwise fun k l => Disjoint (entrySupports X Y Q k) (entrySupports X Y Q l) := by
  intro k l hkl
  by_cases hk : k = insertIdx X Y
  · subst hk
    simp only [entrySupports, Function.update_self, Function.update_of_ne hkl.symm]
    exact (componentFn_disjoint_timeSlab t 0 hkl.symm).symm.mono_left hQ
  · by_cases hl : l = insertIdx X Y
    · subst hl
      simp only [entrySupports, Function.update_self, Function.update_of_ne hk]
      exact (componentFn_disjoint_timeSlab t 0 hk).mono_right hQ
    · simp only [entrySupports, Function.update_of_ne hk, Function.update_of_ne hl]
      exact (complexFamily_componentFn hc t isSlabInsert_zero).disjoint hkl
theorem exists_termMoment_bound (hval : MotionMulRules.SingleEntryValueZero)
    (hmoments : Moments.MomentBoundsTheorem) (M : SharpScale) (C : ℕ → ℝ → ℝ → ℝ)
    (hc : 0 < c) (t : PairSpec c X Y) {Q : Set R4} (hQ : IsCompact Q)
    (hQc : Q ⊆ timeSlab c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (S : ConnFamily) (σ : EuclidFunctionalWithRecon M S),
      σ.clusterConst = C → ∀ h ∈ C1c ℂ, supp h ⊆ Q →
        ‖termMoment S X Y h‖ ≤ K * M.sharpNorm h := by
  by_cases hn : 2 ≤ X.length + 1 + Y.length
  · obtain ⟨R, d, hR, hd, hsep⟩ := exists_separatedInBalls hn (isCompact_componentSupports t hQ)
      (pairwise_disjoint_componentSupports hc t hQc)
    set n := X.length + 1 + Y.length with hn_def
    set P : ℝ := ∏ l ∈ Finset.univ.erase (insertIdx X Y), M.sharpNorm (entryFn X Y 0 l) with hP
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun l _ => zero_le_sharpNorm M _
    refine ⟨2 ^ n * max 0 (Moments.partitionConst C n d R) * P, by positivity,
      fun S σ hσ h hh hsupp => ?_⟩
    have hent : Moments.EntriesSupportedIn (entrySupports X Y Q) (entryFn X Y h) := by
      intro l
      refine ⟨componentFn_mem_C1c t hh l, ?_⟩
      by_cases hl : l = insertIdx X Y
      · subst hl
        simpa [entrySupports, componentFn_insertIdx] using hsupp
      · simp only [entrySupports, Function.update_of_ne hl]
        rw [componentFn_of_ne X Y h 0 hl]
    have hm := (hmoments M S σ n hn R d hR hd _ hsep _ _ hent hent).1
    rw [Moments.MomentBoundHolds, hσ] at hm
    have hprod : ∏ l, M.sharpNorm (entryFn X Y h l) = M.sharpNorm h * P := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (insertIdx X Y)), componentFn_insertIdx]
      congr 1
      exact Finset.prod_congr rfl fun l hl => by
        rw [componentFn_of_ne X Y h 0 (Finset.ne_of_mem_erase hl)]
    rw [termMoment_eq]
    refine hm.trans ?_
    rw [hprod]
    have hs0 := zero_le_sharpNorm M h
    have hle : Moments.partitionConst C n d R ≤
        max 0 (Moments.partitionConst C n d R) := le_max_right _ _
    calc 2 ^ n * Moments.partitionConst C n d R * (M.sharpNorm h * P)
        ≤ 2 ^ n * max 0 (Moments.partitionConst C n d R) *
            (M.sharpNorm h * P) := by gcongr
      _ = _ := by ring
  · have hX : X = [] := List.length_eq_zero_iff.1 (by omega)
    have hY : Y = [] := List.length_eq_zero_iff.1 (by omega)
    subst hX hY
    refine ⟨0, le_rfl, fun S σ _ h hh _ => ?_⟩
    rw [termMoment_nil_nil σ hval hh]
    simp
end Pairs
section Number
variable {S : ConnFamily}
theorem exists_isUniformBoundConst (htuple : TupleRules.TupleSpanActionRules)
    (hrules : MotionMulRules.MotionMulTupleRules)
    (hmoments : Moments.MomentBoundsTheorem)
    (hlin : ∀ S : ConnFamily, IsComplexMultilinear S) (M : SharpScale) (C : ℕ → ℝ → ℝ → ℝ)
    (s t : FnListSum) (Q : Set R4) : ∃ B : ℝ, IsUniformBoundConst M C s t Q B := by
  by_cases hex : ∃ c : ℝ, 0 < c ∧ s.ListsIn (upperOpenHalf c) ∧ t.ListsIn (upperOpenHalf c) ∧
      IsCompact Q ∧ Q ⊆ timeSlab c
  · obtain ⟨c₀, hc₀, hs₀, ht₀, hQ₀, hQc₀⟩ := hex
    have hpair := fun p : Fin s.len × Fin t.len =>
      exists_termMoment_bound hrules.2.2.2.2.2.1 hmoments M C hc₀
        (pairSpec_of htuple (hs₀ p.1) (ht₀ p.2)) hQ₀ hQc₀
    choose K hK₀ hK using hpair
    refine ⟨∑ ι, ∑ κ, ‖s.coeff ι‖ * ‖t.coeff κ‖ * K (ι, κ),
      Finset.sum_nonneg fun ι _ => Finset.sum_nonneg fun κ _ =>
        mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hK₀ _), ?_⟩
    intro S σ hσ c hc hs ht _ hQc h hh hsupp
    rw [insertion_eq_sum htuple (hlin S) hc hs ht ⟨hh, hsupp.trans hQc⟩]
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ι _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ _ => ?_)
    rw [norm_mul, norm_mul, RCLike.norm_conj, mul_assoc (‖s.coeff ι‖ * ‖t.coeff κ‖)]
    exact mul_le_mul_of_nonneg_left (hK (ι, κ) S σ hσ h hh hsupp)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · exact ⟨0, le_rfl, fun S σ _ c hc hs ht hQ hQc => absurd ⟨c, hc, hs, ht, hQ, hQc⟩ hex⟩
theorem compactSetBound (htuple : TupleRules.TupleSpanActionRules)
    (hrules : MotionMulRules.MotionMulTupleRules)
    (hmoments : Moments.MomentBoundsTheorem)
    (hlin : ∀ S : ConnFamily, IsComplexMultilinear S) {M : SharpScale}
    (σ : EuclidFunctionalWithRecon M S) (c : ℝ) (F A : FreeSep) :
    CompactSetBound σ c F A := fun s t _ _ _ _ Q _ _ =>
  Classical.epsilon_spec (exists_isUniformBoundConst htuple hrules hmoments hlin M σ.clusterConst s t Q)
theorem continuousUnderC1 (htuple : TupleRules.TupleSpanActionRules)
    (hrules : MotionMulRules.MotionMulTupleRules)
    (hmoments : Moments.MomentBoundsTheorem)
    (hsharp : SharpNormC1.Main)
    (hlin : ∀ S : ConnFamily, IsComplexMultilinear S) {M : SharpScale}
    (σ : EuclidFunctionalWithRecon M S) {c : ℝ} (hc : 0 < c) {F A : FreeSep}
    (hF : F ∈ finCombIn (upperOpenHalf c)) (hA : A ∈ finCombIn (upperOpenHalf c)) :
    ContinuousUnderC1 S c F A := by
  intro Q hQ hQc hs h hhs hh hsupp hconv
  have hlinear := (linearInInsert htuple (hlin S) hc hF hA).2
  obtain ⟨s, hsI, rfl⟩ := exists_fnListSum_eval_eq hF
  obtain ⟨t, htI, rfl⟩ := exists_fnListSum_eval_eq hA
  have hb := compactSetBound htuple hrules hmoments hlin σ c s.eval t.eval
    s t hsI htI rfl rfl Q hQ hQc
  have hbound := hb.2 S σ rfl c hc hsI htI hQ hQc
  have hnorm := (hsharp.2 M).2.2.1 hs h (fun j hj => (hhs j hj).1) hh hconv
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim := hnorm.const_mul (uniformBoundConst M σ.clusterConst s t Q)
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with j hj
  have hin := hhs j hj
  have hdiff : (1 : ℂ) • hs j + (-1 : ℂ) • h = hs j - h := by
    funext x
    simp [sub_eq_add_neg]
  have hl := hlinear 1 (-1) (hs j) h ⟨hin.1, hin.2.trans hQc⟩ ⟨hh, hsupp.trans hQc⟩
  rw [hdiff] at hl
  have hsub : supp (hs j - h) ⊆ Q := by
    rw [← hdiff]
    exact (supp_linComb_subset _ _ _ _).trans (Set.union_subset hin.2 hsupp)
  have hval := hbound (hs j - h) hl.1.1 hsub
  rw [hl.2] at hval
  simpa [sub_eq_add_neg] using hval
end Number
section Convolution
variable {φ k : R4 → ℂ}
theorem conv_eq_convolution (φ k : R4 → ℂ) :
    EuclideanFunctionals.conv φ k =
      MeasureTheory.convolution φ k (ContinuousLinearMap.mul ℝ ℂ) volume := by apply _root_.YangMills.Construction.TwoPoints.ConvolveC1.convolve_eq_convolution <;> assumption
theorem tsupport_conv_subset (hφc : HasCompactSupport φ) (hk : HasCompactSupport k) :
    tsupport (EuclideanFunctionals.conv φ k) ⊆ tsupport φ + tsupport k := by
  refine closure_minimal ?_ (hφc.isCompact.add hk.isCompact).isClosed
  rw [conv_eq_convolution]
  refine (support_convolution_subset_swap _).trans ?_
  rw [add_comm]
  exact Set.add_subset_add (subset_tsupport _) (subset_tsupport _)
theorem conv_mem_C1c (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hk : k ∈ C1c ℂ) : EuclideanFunctionals.conv φ k ∈ C1c ℂ := by
  have hk' := (mem_C1c_iff _).1 hk
  rw [mem_C1c_iff]
  refine ⟨?_, IsCompact.of_isClosed_subset (hφc.isCompact.add hk'.2.isCompact)
    (isClosed_tsupport _) (tsupport_conv_subset hφc hk'.2)⟩
  rw [conv_eq_convolution]
  exact hk'.2.contDiff_convolution_right _ hφ.locallyIntegrable hk'.1
end Convolution
def topSubmoduleEquiv : R4 ≃L[ℝ] (⊤ : Submodule ℝ R4) :=
  (Submodule.topEquiv (R := ℝ) (M := R4)).symm.toContinuousLinearEquiv
def topSubmoduleMeasEquiv : R4 ≃ᵐ (⊤ : Submodule ℝ R4) :=
  topSubmoduleEquiv.toHomeomorph.toMeasurableEquiv
def topSubmoduleVolume : Measure (⊤ : Submodule ℝ R4) :=
  Measure.map topSubmoduleMeasEquiv volume
theorem exists_isometric_map (κ : ℕ) (hκ : κ = 4) :
    ∃ T : (Fin κ → ℝ) →ₗ[ℝ] (⊤ : Submodule ℝ R4), Function.Surjective T ∧
      (∀ y, EuclideanFunctions.euclideanNorm (T y : R4) =
        EuclideanFunctions.euclideanNorm y) ∧
      topSubmoduleVolume = Measure.map T volume := by
  subst hκ
  exact ⟨topSubmoduleEquiv.toLinearEquiv.toLinearMap, topSubmoduleEquiv.toLinearEquiv.surjective,
    fun _ => rfl, rfl⟩
theorem topSubmoduleVolume_isLebesgue :
    Smearing.IsLebesgueOn ⊤ topSubmoduleVolume := by
  have hfin : Module.finrank ℝ (⊤ : Submodule ℝ R4) = 4 := by
    simp
  obtain ⟨T, hs, hn, hm⟩ := exists_isometric_map _ hfin
  exact Or.inr ⟨by omega, T, ⟨hs, hn⟩, hm⟩
theorem integral_pi_topSubmodule (G : (Fin 1 → (⊤ : Submodule ℝ R4)) → ℂ) :
    ∫ z, G z ∂(Measure.pi fun _ : Fin 1 => topSubmoduleVolume) =
      ∫ x : R4, G fun _ => topSubmoduleMeasEquiv x := by
  have : SigmaFinite topSubmoduleVolume := topSubmoduleMeasEquiv.sigmaFinite_map
  have hmp := (measurePreserving_funUnique topSubmoduleVolume (Fin 1)).symm
  have h1 : ∫ w, G (fun _ => w) ∂topSubmoduleVolume =
      ∫ z, G z ∂(Measure.pi fun _ : Fin 1 => topSubmoduleVolume) := by
    convert hmp.integral_comp' G
    rfl
  rw [← h1, topSubmoduleVolume, integral_map_equiv]
theorem mem_tsupport_topSubmodule {φ : R4 → ℂ} {z : (⊤ : Submodule ℝ R4)} :
    z ∈ tsupport (fun z : (⊤ : Submodule ℝ R4) => φ z) ↔ (z : R4) ∈ tsupport φ :=
  Set.ext_iff.1 (tsupport_comp_eq_preimage φ topSubmoduleEquiv.symm.toHomeomorph) z
theorem smearConv_topSubmodule (φ k : R4 → ℂ) :
    Smearing.conv topSubmoduleVolume (fun z => φ z) k = EuclideanFunctionals.conv φ k := by
  funext x
  rw [Smearing.conv, topSubmoduleVolume, integral_map_equiv]
  rfl
section SmearingProof
open Smearing (shiftSmearingTuple convEntries valueAt integrand)
variable {c : ℝ} {X Y : FnList} {S : ConnFamily} {φ k : R4 → ℂ}
def headIdx (X Y : FnList) : Fin (X.length + 1 + Y.length) := ⟨0, by omega⟩
def swapToHead (X Y : FnList) : Equiv.Perm (Fin (X.length + 1 + Y.length)) :=
  Equiv.swap (headIdx X Y) (insertIdx X Y)
theorem swapToHead_headIdx : swapToHead X Y (headIdx X Y) = insertIdx X Y :=
  Equiv.swap_apply_left _ _
theorem swapToHead_ne {l : Fin (X.length + 1 + Y.length)} (hl : l ≠ headIdx X Y) :
    swapToHead X Y l ≠ insertIdx X Y := by
  intro h
  apply hl
  have h2 := congrArg (swapToHead X Y) h
  rw [swapToHead, Equiv.swap_apply_self, Equiv.swap_apply_right] at h2
  exact h2
theorem eq_entryFn_comp_moveToFront (k v : R4 → ℂ) (w : Fin (X.length + 1 + Y.length) → R4 → ℂ)
    (h0 : w (headIdx X Y) = v)
    (hw : ∀ l, l ≠ headIdx X Y → w l = entryFn X Y k (swapToHead X Y l)) :
    w = entryFn X Y v ∘ swapToHead X Y := by
  funext l
  by_cases hl : l = headIdx X Y
  · subst hl
    rw [Function.comp_apply, swapToHead_headIdx, componentFn_insertIdx, h0]
  · rw [hw l hl, Function.comp_apply, componentFn_of_ne X Y k v (swapToHead_ne hl)]
def bumpOnTop (φ : R4 → ℂ) : Fin 1 → (⊤ : Submodule ℝ R4) → ℂ := fun _ z => φ z
def smearSupports (X Y : FnList) (φ k : R4 → ℂ) : Fin (X.length + 1 + Y.length) → Set R4 :=
  Function.update (fun l => supp (entryFn X Y 0 (swapToHead X Y l))) (headIdx X Y)
    (supp φ + supp k)
theorem zero_mem_C1c : (0 : R4 → ℂ) ∈ C1c ℂ :=
  (mem_C1c_iff _).2 ⟨contDiff_const, HasCompactSupport.zero⟩
theorem smearData (hc : 0 < c) (t : PairSpec c X Y) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hk : k ∈ C1c ℂ)
    (hsum : supp φ + supp k ⊆ timeSlab c) :
    Smearing.Data (smearSupports X Y φ k) (entryFn X Y k ∘ swapToHead X Y)
      (bumpOnTop φ) where
  compact l := by
    by_cases hl : l = headIdx X Y
    · subst hl
      simp only [smearSupports, Function.update_self]
      rw [supp_eq_tsupport, supp_eq_tsupport]
      exact hφc.isCompact.add ((mem_C1c_iff _).1 hk).2.isCompact
    · simp only [smearSupports, Function.update_of_ne hl]
      exact isCompact_supp_componentFn t zero_mem_C1c _
  pairwise_disjoint k₁ l₁ hkl := by
    by_cases hk₁ : k₁ = headIdx X Y
    · subst hk₁
      simp only [smearSupports, Function.update_self, Function.update_of_ne hkl.symm]
      exact (componentFn_disjoint_timeSlab t 0 (swapToHead_ne hkl.symm)).symm.mono_left hsum
    · by_cases hl₁ : l₁ = headIdx X Y
      · subst hl₁
        simp only [smearSupports, Function.update_self, Function.update_of_ne hk₁]
        exact (componentFn_disjoint_timeSlab t 0 (swapToHead_ne hk₁)).mono_right hsum
      · simp only [smearSupports, Function.update_of_ne hk₁, Function.update_of_ne hl₁]
        exact (complexFamily_componentFn hc t isSlabInsert_zero).disjoint
          ((swapToHead X Y).injective.ne hkl)
  mem_C1c l := componentFn_mem_C1c t hk _
  cont _ := hφ.comp continuous_subtype_val
  compactSupport _ := hφc.comp_homeomorph topSubmoduleEquiv.symm.toHomeomorph
  conv_supp l hl := by
    obtain rfl : l = headIdx X Y := Fin.ext (Nat.lt_one_iff.1 hl)
    simp only [smearSupports, Function.update_self, Function.comp_apply, swapToHead_headIdx,
      componentFn_insertIdx]
    rintro _ ⟨a, ha, _, ⟨z, hz, rfl⟩, rfl⟩
    change a + (z : R4) ∈ _
    rw [add_comm a]
    refine Set.add_mem_add ?_ ha
    rw [supp_eq_tsupport]
    exact mem_tsupport_topSubmodule.1 hz
  rest_supp l hl := by
    have hne : l ≠ headIdx X Y := fun e => hl (by rw [e]; simp [headIdx])
    simp only [smearSupports, Function.update_of_ne hne, Function.comp_apply]
    rw [componentFn_of_ne X Y k 0 (swapToHead_ne hne)]
theorem momentAt_smearing (hsmear : Smearing.Holds)
    (hsym : MomentSymmetry.PermInvariant S) {M : SharpScale}
    (σ : EuclidFunctionalWithRecon M S) (hc : 0 < c) (t : PairSpec c X Y)
    (hn : 2 ≤ X.length + 1 + Y.length) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hk : k ∈ C1c ℂ) (hsum : supp φ + supp k ⊆ timeSlab c)
    (hin : ∀ x ∈ supp φ, IsSlabInsert c (shiftFn x k))
    (hconv : IsSlabInsert c (EuclideanFunctionals.conv φ k)) :
    ContinuousOn (fun x => momentAt S (entryFn X Y (shiftFn x k))) (supp φ) ∧
      momentAt S (entryFn X Y (EuclideanFunctionals.conv φ k)) =
        ∫ x, φ x * momentAt S (entryFn X Y (shiftFn x k)) := by
  have d := smearData hc t hφ hφc hk hsum
  obtain ⟨-, ⟨-, -, hcont⟩, hform, -, -⟩ := hsmear.2 M S σ _ 1 hn le_rfl (by omega) ⊤
    topSubmoduleVolume topSubmoduleVolume_isLebesgue _ _ _ d
  have hfirst : (entryFn X Y k ∘ swapToHead X Y) (headIdx X Y) = k := by
    rw [Function.comp_apply, swapToHead_headIdx, componentFn_insertIdx]
  have hnot : ∀ l : Fin (X.length + 1 + Y.length), l ≠ headIdx X Y → ¬ (l : ℕ) < 1 :=
    fun l hl h1 => hl (Fin.ext (Nat.lt_one_iff.1 h1))
  have htr : ∀ z : Fin 1 → (⊤ : Submodule ℝ R4),
      shiftSmearingTuple z (entryFn X Y k ∘ swapToHead X Y) =
        entryFn X Y (shiftFn (z 0 : R4) k) ∘ swapToHead X Y := by
    intro z
    refine eq_entryFn_comp_moveToFront k _ _ ?_ fun l hl => ?_
    · have h0 : ((headIdx X Y : Fin _) : ℕ) < 1 := by simp [headIdx]
      simp only [shiftSmearingTuple, dif_pos h0, hfirst]
      rfl
    · simp only [shiftSmearingTuple, dif_neg (hnot l hl)]
      rfl
  have hsm : convEntries topSubmoduleVolume (bumpOnTop φ) (entryFn X Y k ∘ swapToHead X Y) =
      entryFn X Y (EuclideanFunctionals.conv φ k) ∘ swapToHead X Y := by
    refine eq_entryFn_comp_moveToFront k _ _ ?_ fun l hl => ?_
    · have h0 : ((headIdx X Y : Fin _) : ℕ) < 1 := by simp [headIdx]
      simp only [convEntries, dif_pos h0, hfirst]
      exact smearConv_topSubmodule φ k
    · simp only [convEntries, dif_neg (hnot l hl)]
      rfl
  have hperm : ∀ {v : R4 → ℂ}, IsSlabInsert c v →
      momentAt S (entryFn X Y v ∘ swapToHead X Y) = momentAt S (entryFn X Y v) := fun hv =>
    hsym _ hn _ _ (complexFamily_componentFn hc t hv)
  have hι : Continuous fun x : R4 => fun _ : Fin 1 => topSubmoduleEquiv x :=
    continuous_pi fun _ => topSubmoduleEquiv.continuous
  have hmaps : Set.MapsTo (fun x : R4 => fun _ : Fin 1 => topSubmoduleEquiv x) (supp φ)
      (Set.pi Set.univ fun l => tsupport (bumpOnTop φ l)) := fun x hx l _ => by
    refine mem_tsupport_topSubmodule.2 ?_
    rw [supp_eq_tsupport] at hx
    exact hx
  refine ⟨(hcont.comp hι.continuousOn hmaps).congr fun x hx => ?_, ?_⟩
  · simp only [Function.comp_apply]
    change _ = momentAt S (shiftSmearingTuple _ _)
    rw [htr]
    exact (hperm (hin x hx)).symm
  · rw [integral_pi_topSubmodule] at hform
    rw [← hperm hconv]
    have h1 : momentAt S (entryFn X Y (EuclideanFunctionals.conv φ k) ∘ swapToHead X Y) =
        valueAt S (convEntries topSubmoduleVolume (bumpOnTop φ)
          (entryFn X Y k ∘ swapToHead X Y)) := by
      rw [hsm]
      rfl
    rw [h1, hform]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [integrand, Finset.univ_unique, Finset.prod_singleton, bumpOnTop]
    change φ x * momentAt S (shiftSmearingTuple _ _) = _
    rw [htr]
    by_cases hx : x ∈ supp φ
    · change φ x * momentAt S (entryFn X Y (shiftFn x k) ∘ swapToHead X Y) = _
      rw [hperm (hin x hx)]
    · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport (by rwa [supp_eq_tsupport] at hx)
      simp [h0]
theorem termMoment_smearing (hval : MotionMulRules.SingleEntryValueZero)
    (hsmear : Smearing.Holds)
    (hsym : MomentSymmetry.PermInvariant S) {M : SharpScale}
    (σ : EuclidFunctionalWithRecon M S) (hc : 0 < c) (t : PairSpec c X Y)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hk : k ∈ C1c ℂ)
    (hsum : supp φ + supp k ⊆ timeSlab c)
    (hin : ∀ x ∈ supp φ, IsSlabInsert c (shiftFn x k))
    (hconv : IsSlabInsert c (EuclideanFunctionals.conv φ k)) :
    ContinuousOn (fun x => termMoment S X Y (shiftFn x k)) (supp φ) ∧
      termMoment S X Y (EuclideanFunctionals.conv φ k) =
        ∫ x in supp φ, φ x * termMoment S X Y (shiftFn x k) := by
  have hmeas : MeasurableSet (supp φ) := by
    rw [supp_eq_tsupport]
    exact (isClosed_tsupport φ).measurableSet
  by_cases hn : 2 ≤ X.length + 1 + Y.length
  · obtain ⟨h1, h2⟩ := momentAt_smearing hsmear hsym σ hc t hn hφ hφc hk hsum hin hconv
    simp only [termMoment_eq]
    refine ⟨h1, h2.trans (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm⟩
    have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport (by rwa [supp_eq_tsupport] at hx)
    simp [h0]
  · have hX : X = [] := List.length_eq_zero_iff.1 (by omega)
    have hY : Y = [] := List.length_eq_zero_iff.1 (by omega)
    subst hX hY
    refine ⟨continuousOn_const (c := (0 : ℂ)) |>.congr fun x hx =>
      termMoment_nil_nil σ hval (hin x hx).1, ?_⟩
    rw [termMoment_nil_nil σ hval hconv.1, setIntegral_congr_fun (g := fun _ => (0 : ℂ)) hmeas
      fun x hx => by simp [termMoment_nil_nil σ hval (hin x hx).1]]
    simp
theorem smearingFormula (htuple : TupleRules.TupleSpanActionRules)
    (hrules : MotionMulRules.MotionMulTupleRules)
    (hsmear : Smearing.Holds)
    (hsym : MomentSymmetry.PermInvariant S)
    (hlin : IsComplexMultilinear S) {M : SharpScale}
    (σ : EuclidFunctionalWithRecon M S) (hc : 0 < c) {F A : FreeSep}
    (hF : F ∈ finCombIn (upperOpenHalf c)) (hA : A ∈ finCombIn (upperOpenHalf c)) :
    SmearingFormula S c F A := by
  intro φ k hφ hφc hk hsum
  have hk' := (mem_C1c_iff _).1 hk
  have hconv := conv_mem_C1c hφ hφc hk
  have hconvs : supp (EuclideanFunctionals.conv φ k) ⊆ supp φ + supp k := by
    rw [supp_eq_tsupport, supp_eq_tsupport, supp_eq_tsupport]
    exact tsupport_conv_subset hφc hk'.2
  have hcin : IsSlabInsert c (EuclideanFunctionals.conv φ k) := ⟨hconv, hconvs.trans hsum⟩
  have hin : ∀ x ∈ supp φ, IsSlabInsert c (shiftFn x k) := fun x hx => by
    refine ⟨shiftFn_mem_C1c hk x, ?_⟩
    rw [(hrules.2.2.2.2.2.2.2.1 k hk'.1.continuous hk'.2 x).1]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have hbx : b = x := hb
    subst hbx
    change a + b ∈ _
    rw [add_comm a b]
    exact hsum (Set.add_mem_add hx ha)
  obtain ⟨s, hs, rfl⟩ := exists_fnListSum_eval_eq hF
  obtain ⟨t, ht, rfl⟩ := exists_fnListSum_eval_eq hA
  have hpair := fun (ι : Fin s.len) (κ : Fin t.len) =>
    termMoment_smearing hrules.2.2.2.2.2.1 hsmear hsym σ hc (pairSpec_of htuple (hs ι) (ht κ))
      hφ hφc hk hsum hin hcin
  have hexp := fun x (hx : x ∈ supp φ) =>
    insertion_eq_sum htuple hlin hc hs ht (hin x hx)
  have hcomp : IsCompact (supp φ) := by
    rw [supp_eq_tsupport]
    exact hφc
  have hmeas : MeasurableSet (supp φ) := hcomp.measurableSet
  have hint : ∀ (ι : Fin s.len) (κ : Fin t.len), IntegrableOn
      (fun x => φ x * termMoment S (s.list ι) (t.list κ) (shiftFn x k)) (supp φ)
      volume := fun ι κ =>
    (hφ.continuousOn.mul (hpair ι κ).1).integrableOn_compact (μ := volume) hcomp
  refine ⟨hconv, hconvs, hin, ?_, ?_⟩
  · refine ContinuousOn.congr ?_ hexp
    exact continuousOn_finsetSum _ fun ι _ => continuousOn_finsetSum _ fun κ _ =>
      continuousOn_const.mul (hpair ι κ).1
  · rw [insertion_eq_sum htuple hlin hc hs ht hcin,
      setIntegral_congr_fun (g := fun x => ∑ ι, ∑ κ, conj (s.coeff ι) * t.coeff κ *
        (φ x * termMoment S (s.list ι) (t.list κ) (shiftFn x k))) hmeas
        fun x hx => by
          simp only [hexp x hx, Finset.mul_sum]
          exact Finset.sum_congr rfl fun ι _ => Finset.sum_congr rfl fun κ _ => by ring,
      integral_finsetSum _ fun ι _ => integrable_finsetSum _ fun κ _ => (hint ι κ).const_mul _]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [integral_finsetSum _ fun κ _ => (hint ι κ).const_mul _]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [integral_const_mul, ← (hpair ι κ).2]
end SmearingProof
theorem insertionFormTheorem_holds (hmoments : Moments.MomentBoundsTheorem)
    (htensor : TensorComponents.CenteredSeesTensorComps)
    (hinvariance : MomentSymmetry.ReductionHolds)
    (hrules : MotionMulRules.MotionMulTupleRules)
    (hsharp : SharpNormC1.Main)
    (hsmear : Smearing.Holds)
    (htuple : TupleRules.TupleSpanActionRules) : InsertionFormTheorem := by
  intro M S σ c hc F hF A hA
  have hlin : ∀ S : ConnFamily, IsComplexMultilinear S := fun S => (htensor S).2.2.2.1
  obtain ⟨hsym, hinv, -⟩ := hinvariance M S σ
  exact ⟨expansionHolds σ htuple hrules (hlin S) hc F A, linearInInsert htuple (hlin S) hc hF hA,
    translationCovariance htuple hrules hinv hc hF hA,
    compactSetBound htuple hrules hmoments hlin σ c F A,
    continuousUnderC1 htuple hrules hmoments hsharp hlin σ hc hF hA,
    smearingFormula htuple hrules hsmear hsym (hlin S) σ hc hF hA⟩
end YangMills.Construction.EuclideanFunctionals.InsertionForm
