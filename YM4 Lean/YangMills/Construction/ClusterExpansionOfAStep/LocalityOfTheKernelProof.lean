import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ClusterExpansionOfAStep.BlocksReadTheirBoxesProof
import YangMills.Construction.ClusterExpansionOfAStep.LocalityOfTheKernel
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace KernelLocality
open BlockAverages LumpContours TorusLumps TorusContours
open TorusFields hiding unitStep supDist
section BoxMerging
def BoxesNear (q q' : OffsetBox) : Prop := ∀ i, q.1 i ≤ q'.2 i + 2 ∧ q'.1 i ≤ q.2 i + 2
def BoxSubset (q q' : OffsetBox) : Prop := ∀ i, q'.1 i ≤ q.1 i ∧ q.2 i ≤ q'.2 i
def boxHull (q q' : OffsetBox) : OffsetBox := (fun i => min (q.1 i) (q'.1 i), fun i => max (q.2 i) (q'.2 i))
def boxWidth (q : OffsetBox) (i : Fin 4) : ℤ := q.2 i - q.1 i + 1
def BoxOrdered (q : OffsetBox) : Prop := ∀ i, q.1 i ≤ q.2 i
structure IsMergeOf (R M : Finset OffsetBox) : Prop where
  ordered : ∀ q ∈ M, BoxOrdered q
  covers : ∀ q ∈ R, ∃ q' ∈ M, BoxSubset q q'
  separated : ∀ q ∈ M, ∀ q' ∈ M, q ≠ q' → ¬ BoxesNear q q'
  sum_le : ∀ i, ∑ q ∈ M, (boxWidth q i + 2) ≤ ∑ q ∈ R, (boxWidth q i + 2)
  window : ∀ A B : Fin 4 → ℤ, (∀ q ∈ R, ∀ i, A i ≤ q.1 i ∧ q.2 i ≤ B i) → ∀ q ∈ M, ∀ i, A i ≤ q.1 i ∧ q.2 i ≤ B i
  least : ∀ {α : Type} (In : OffsetBox → α → Prop), (∀ q ∈ R, ∃ a, In q a) →
    (∀ q q' a a', BoxOrdered q → BoxOrdered q' → BoxesNear q q' → In q a → In q' a' → a = a') →
    (∀ q q' a, BoxOrdered q → BoxOrdered q' → BoxesNear q q' → In q a → In q' a → In (boxHull q q') a) →
    ∀ q ∈ M, ∃ a, In q a
theorem exists_isMergeOf : ∀ (N : ℕ) (R : Finset OffsetBox), R.card = N → (∀ q ∈ R, BoxOrdered q) →
    ∃ M, IsMergeOf R M := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro R hcard hR
    classical
    by_cases hbad : ∃ q ∈ R, ∃ q' ∈ R, q ≠ q' ∧ BoxesNear q q'
    · obtain ⟨q, hq, q', hq', hne, hnear⟩ := hbad
      set E := (R.erase q).erase q' with hE
      have hq'E : q' ∈ R.erase q := Finset.mem_erase.mpr ⟨hne.symm, hq'⟩
      have hcardE : E.card + 2 = R.card := by
        have h1 := Finset.card_erase_add_one hq
        have h2 : E.card + 1 = (R.erase q).card := Finset.card_erase_add_one hq'E
        omega
      set R' := insert (boxHull q q') E with hR'
      have hcard' : R'.card < N := by
        have : R'.card ≤ E.card + 1 := Finset.card_insert_le (boxHull q q') E
        omega
      have hord : BoxOrdered (boxHull q q') := by
        intro i
        have h1 := hR q hq i
        have h2 := hR q' hq' i
        simp only [boxHull]
        omega
      have hER : ∀ p ∈ E, p ∈ R := fun p hp =>
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp)
      have hR'ord : ∀ p ∈ R', BoxOrdered p := by
        intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact hord
        · exact hR p (hER p hp)
      obtain ⟨M, hM⟩ := ih _ hcard' R' rfl hR'ord
      have hsub1 : BoxSubset q (boxHull q q') := fun i => by simp only [boxHull]; omega
      have hsub2 : BoxSubset q' (boxHull q q') := fun i => by simp only [boxHull]; omega
      have hstep : ∀ p ∈ R, p = q ∨ p = q' ∨ p ∈ E := by
        intro p hp
        by_cases h1 : p = q
        · exact Or.inl h1
        by_cases h2 : p = q'
        · exact Or.inr (Or.inl h2)
        exact Or.inr (Or.inr (Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hp⟩⟩))
      refine ⟨M, hM.ordered, ?_, hM.separated, ?_, ?_, ?_⟩
      · intro p hp
        have hto : ∀ s, BoxSubset p s → s ∈ R' → ∃ q' ∈ M, BoxSubset p q' := by
          intro s hps hs
          obtain ⟨t, ht, hst⟩ := hM.covers s hs
          exact ⟨t, ht, fun i => ⟨(hst i).1.trans (hps i).1, (hps i).2.trans (hst i).2⟩⟩
        rcases hstep p hp with rfl | rfl | h
        · exact hto _ hsub1 (Finset.mem_insert_self _ _)
        · exact hto _ hsub2 (Finset.mem_insert_self _ _)
        · exact hto p (fun i => ⟨le_rfl, le_rfl⟩) (Finset.mem_insert_of_mem h)
      · intro i
        refine (hM.sum_le i).trans ?_
        have hnn : ∀ p ∈ R', 0 ≤ boxWidth p i + 2 := by
          intro p hp
          have := hR'ord p hp i
          simp only [boxWidth]
          omega
        have h1 : ∑ p ∈ R', (boxWidth p i + 2) ≤ (boxWidth (boxHull q q') i + 2) + ∑ p ∈ E, (boxWidth p i + 2) := by
          by_cases hin : boxHull q q' ∈ E
          · have : R' = E := Finset.insert_eq_of_mem hin
            rw [this]
            have := hnn _ (Finset.mem_insert_self (boxHull q q') E)
            omega
          · rw [hR', Finset.sum_insert hin]
        have h2 : ∑ p ∈ R, (boxWidth p i + 2) = (boxWidth q i + 2) + ((boxWidth q' i + 2) + ∑ p ∈ E, (boxWidth p i + 2)) := by
          rw [hE, Finset.add_sum_erase _ (fun p => boxWidth p i + 2) hq'E, Finset.add_sum_erase _ (fun p => boxWidth p i + 2) hq]
        have h3 : boxWidth (boxHull q q') i + 2 ≤ (boxWidth q i + 2) + (boxWidth q' i + 2) := by
          have h4 := hnear i
          have h5 := hR q hq i
          have h6 := hR q' hq' i
          simp only [boxWidth, boxHull]
          omega
        omega
      · intro A B hAB
        refine hM.window A B ?_
        intro p hp i
        rcases Finset.mem_insert.mp hp with rfl | hp
        · have h1 := hAB q hq i
          have h2 := hAB q' hq' i
          simp only [boxHull]
          omega
        · exact hAB p (hER p hp) i
      · intro α In h1 h2 h3
        refine hM.least In ?_ h2 h3
        intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · obtain ⟨a, ha⟩ := h1 q hq
          obtain ⟨a', ha'⟩ := h1 q' hq'
          have hEq := h2 q q' a a' (hR q hq) (hR q' hq') hnear ha ha'
          subst hEq
          exact ⟨a, h3 q q' a (hR q hq) (hR q' hq') hnear ha ha'⟩
        · exact h1 p (hER p hp)
    · refine ⟨R, hR, fun q hq => ⟨q, hq, fun i => ⟨le_rfl, le_rfl⟩⟩, ?_, fun i => le_rfl, fun A B h => h,
        fun In h1 _ _ => h1⟩
      intro q hq q' hq' hne hnear
      exact hbad ⟨q, hq, q', hq', hne, hnear⟩
end BoxMerging
section OffsetWindow
variable {F : BlockFrame} [∀ j i, NeZero (F.period j i)]
def InWindow (L : ℕ) (u : Fin 4 → ℤ) : Prop := ∀ i, -(7 * (L : ℤ)) ≤ u i ∧ u i ≤ 7 * (L : ℤ)
def BoxInWindow (L : ℕ) (q : OffsetBox) : Prop := BoxOrdered q ∧ InWindow L q.1 ∧ InWindow L q.2
def MemBox (u : Fin 4 → ℤ) (q : OffsetBox) : Prop := ∀ i, q.1 i ≤ u i ∧ u i ≤ q.2 i
omit [∀ j i, NeZero (F.period j i)] in
theorem siteAtOffset_apply (y : F.Cell) (u : Fin 4 → ℤ) (i : Fin 4) :
    (siteAtOffset y u : F.Site F.depth) i = (((F.blockSide : ℤ) * siteCoords y i + u i : ℤ) : ZMod (F.period F.depth i)) := by apply _root_.YangMills.Construction.BlockLocality.siteAtOffset_apply <;> assumption
omit [∀ j i, NeZero (F.period j i)] in
theorem siteAtOffset_sub_siteAtOffset (y : F.Cell) (u v : Fin 4 → ℤ) (i : Fin 4) :
    (siteAtOffset y u : F.Site F.depth) i - (siteAtOffset y v : F.Site F.depth) i = ((u i - v i : ℤ) : ZMod (F.period F.depth i)) := by apply _root_.YangMills.Construction.BlockLocality.siteAtOffset_sub_apply <;> assumption
theorem siteAtOffset_apply_eq_iff (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (y : F.Cell) {u v : Fin 4 → ℤ} {i : Fin 4}
    (h : |u i - v i| ≤ 14 * (F.blockSide : ℤ)) (hL : 2 ≤ F.blockSide) :
    (siteAtOffset y u : F.Site F.depth) i = (siteAtOffset y v : F.Site F.depth) i ↔ u i = v i := by apply _root_.YangMills.Construction.BlockLocality.siteAtOffset_apply_eq_iff <;> assumption
theorem abs_sub_le_of_inWindow {L : ℕ} {u v : Fin 4 → ℤ} (hu : InWindow L u) (hv : InWindow L v) (i : Fin 4) :
    |u i - v i| ≤ 14 * (L : ℤ) := by apply _root_.YangMills.Construction.BlockLocality.abs_sub_le_of_window <;> assumption
theorem siteAtOffset_eq_iff (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (hL : 2 ≤ F.blockSide) (y : F.Cell)
    {u v : Fin 4 → ℤ} (hu : InWindow F.blockSide u) (hv : InWindow F.blockSide v) :
    (siteAtOffset y u : F.Site F.depth) = siteAtOffset y v ↔ u = v := by apply _root_.YangMills.Construction.BlockLocality.siteAtOffset_eq_iff <;> assumption
omit [∀ j i, NeZero (F.period j i)] in
theorem mem_boxAtOffset {y : F.Cell} {q : OffsetBox} {x : F.Site F.depth} :
    x ∈ boxAtOffset y q ↔ ∃ v, MemBox v q ∧ x = siteAtOffset y v := by apply _root_.YangMills.Construction.BlockLocality.mem_boxAtOffset <;> assumption
theorem inWindow_of_memBox {L : ℕ} {q : OffsetBox} (hq : BoxInWindow L q) {v : Fin 4 → ℤ} (hv : MemBox v q) : InWindow L v := by apply _root_.YangMills.Construction.BlockLocality.window_of_mem_box <;> assumption
theorem siteAtOffset_mem_boxAtOffset_iff (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (hL : 2 ≤ F.blockSide) (y : F.Cell)
    {u : Fin 4 → ℤ} {q : OffsetBox} (hu : InWindow F.blockSide u) (hq : BoxInWindow F.blockSide q) :
    siteAtOffset y u ∈ boxAtOffset y q ↔ MemBox u q := by apply _root_.YangMills.Construction.BlockLocality.siteAtOffset_mem_boxAtOffset_iff <;> assumption
theorem memBox_lower {q : OffsetBox} (hq : BoxOrdered q) : MemBox q.1 q := fun i => ⟨le_rfl, hq i⟩
theorem memBox_upper {q : OffsetBox} (hq : BoxOrdered q) : MemBox q.2 q := fun i => ⟨hq i, le_rfl⟩
theorem boxAtOffset_injective (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (hL : 2 ≤ F.blockSide) (y : F.Cell)
    {q q' : OffsetBox} (hq : BoxInWindow F.blockSide q) (hq' : BoxInWindow F.blockSide q') (h : boxAtOffset y q = boxAtOffset y q') : q = q' := by apply _root_.YangMills.Construction.BlockLocality.boxAtOffset_injective (F := F) <;> assumption
theorem valMinAbs_intCast_of_small {p : ℕ} [NeZero p] {z : ℤ} (h : 2 * |z| < (p : ℤ)) : ((z : ZMod p)).valMinAbs = z := by apply _root_.YangMills.SharedProofs.p9640 <;> assumption
theorem valMinAbs_siteAtOffset_sub (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (hL : 2 ≤ F.blockSide) (y : F.Cell) {u v : Fin 4 → ℤ}
    (hu : InWindow F.blockSide u) (hv : InWindow F.blockSide v) (i : Fin 4) (hs : |u i - v i| ≤ 7 * (F.blockSide : ℤ)) :
    (((siteAtOffset y u : F.Site F.depth) i - (siteAtOffset y v : F.Site F.depth) i).valMinAbs) = u i - v i := by apply _root_.YangMills.Construction.BlockLocality.valMinAbs_siteAtOffset_sub <;> assumption
theorem areWithin_of_boxesNear (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (hL : 2 ≤ F.blockSide) (y : F.Cell) {q q' : OffsetBox}
    (hq : BoxInWindow F.blockSide q) (hq' : BoxInWindow F.blockSide q') (hn : BoxesNear q q') : AreWithin 2 (boxAtOffset y q) (boxAtOffset y q') := by apply _root_.YangMills.Construction.BlockLocality.areWithin_of_boxesNear <;> assumption
theorem boxesNear_of_areWithin (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (hL : 2 ≤ F.blockSide) (y : F.Cell) {q q' : OffsetBox}
    (hq : BoxInWindow F.blockSide q) (hq' : BoxInWindow F.blockSide q') (hw : AreWithin 2 (boxAtOffset y q) (boxAtOffset y q')) : BoxesNear q q' := by apply _root_.YangMills.Construction.BlockLocality.boxesNear_of_areWithin (F := F) <;> assumption
omit [∀ j i, NeZero (F.period j i)] in
theorem mem_boxSites_iff {j : ℕ} {lo hi : Fin 4 → ℤ} {x : F.Site j} :
    x ∈ boxSites j lo hi ↔ ∃ c : Fin 4 → ℤ, (∀ i, lo i ≤ c i ∧ c i ≤ hi i) ∧ siteOfCoords j c = x := by
  simp [boxSites, Fintype.mem_piFinset]
theorem boxAtOffset_boxHull_subset (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (hL : 2 ≤ F.blockSide) (y : F.Cell) {q q' : OffsetBox}
    (hq : BoxInWindow F.blockSide q) (hq' : BoxInWindow F.blockSide q') {lo hi : Fin 4 → ℤ}
    (hlo : ∀ i, lo i ≤ hi i ∧ hi i - lo i + 1 < F.blockSide)
    (h1 : boxAtOffset y q ⊆ boxSites F.depth lo hi) (h2 : boxAtOffset y q' ⊆ boxSites F.depth lo hi) :
    boxAtOffset y (boxHull q q') ⊆ boxSites F.depth lo hi := by exact _root_.YangMills.Construction.BlockLocality.boxAtOffset_boxHull_subset (F := F) (q := q) (q' := q') (lo := lo) (hi := hi) hbig hL y hq hq' hlo h1 h2
omit [∀ j i, NeZero (F.period j i)] in
theorem boxAtOffset_eq_boxSites (y : F.Cell) (q : OffsetBox) :
    (boxAtOffset y q : Finset (F.Site F.depth)) = boxSites F.depth (fun i => (F.blockSide : ℤ) * siteCoords y i + q.1 i)
      (fun i => (F.blockSide : ℤ) * siteCoords y i + q.2 i) := by apply _root_.YangMills.Construction.BlockLocality.boxAtOffset_eq_boxSites <;> assumption
omit [∀ j i, NeZero (F.period j i)] in
theorem mergedBoxes_eq_of_isLeast {j : ℕ} {seeds Z : Finset (Finset (F.Site j))} (h : IsLeastSeparatedCover seeds Z) :
    mergedBoxes seeds = Z := by apply _root_.YangMills.Construction.BlockLocality.mergedBoxes_eq_of_isLeast <;> assumption
theorem mergedBoxes_image_boxAtOffset (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (hL : 2 ≤ F.blockSide) (y : F.Cell)
    {R M : Finset OffsetBox} (hM : IsMergeOf R M) (hR : ∀ q ∈ R, BoxInWindow F.blockSide q) (hMw : ∀ q ∈ M, BoxInWindow F.blockSide q)
    (hs : ∀ q ∈ M, ∀ i, boxWidth q i < F.blockSide) :
    mergedBoxes (R.image (boxAtOffset y)) = M.image (boxAtOffset y) := by
  classical
  refine mergedBoxes_eq_of_isLeast ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro B hB
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
    refine ⟨_, _, fun i => ?_, boxAtOffset_eq_boxSites y q⟩
    have h1 := (hMw q hq).1 i
    have h2 := hs q hq i
    simp only [boxWidth] at h2
    constructor <;> omega
  · intro B hB
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨q', hq', hsub⟩ := hM.covers q hq
    refine ⟨_, Finset.mem_image_of_mem _ hq', fun x hx => ?_⟩
    obtain ⟨v, hv, rfl⟩ := mem_boxAtOffset.mp hx
    exact mem_boxAtOffset.mpr ⟨v, fun i => ⟨(hsub i).1.trans (hv i).1, (hv i).2.trans (hsub i).2⟩, rfl⟩
  · intro B hB B' hB' hne hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hB'
    exact hM.separated q hq q' hq' (fun h => hne (by rw [h]))
      (boxesNear_of_areWithin hbig hL y (hMw q hq) (hMw q' hq') hw)
  · intro Z' hZ' B hB
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
    have hA : ∀ p ∈ R, ∃ a, BoxInWindow F.blockSide p ∧ a ∈ Z' ∧ boxAtOffset y p ⊆ a := by
      intro p hp
      obtain ⟨B', hB', hs'⟩ := hZ'.2.1 _ (Finset.mem_image_of_mem _ hp)
      exact ⟨B', hR p hp, hB', hs'⟩
    have hB₂ : ∀ (p p' : OffsetBox) (a a' : Finset (F.Site F.depth)), BoxOrdered p → BoxOrdered p' → BoxesNear p p' →
        (BoxInWindow F.blockSide p ∧ a ∈ Z' ∧ boxAtOffset y p ⊆ a) → (BoxInWindow F.blockSide p' ∧ a' ∈ Z' ∧ boxAtOffset y p' ⊆ a') → a = a' := by
      rintro p p' a a' - - hn ⟨hw, ha, hs₁⟩ ⟨hw', ha', hs₂⟩
      by_contra hne
      obtain ⟨x, hx, x', hx', hd⟩ := areWithin_of_boxesNear hbig hL y hw hw' hn
      exact hZ'.2.2 a ha a' ha' hne ⟨x, hs₁ hx, x', hs₂ hx', hd⟩
    have hC : ∀ (p p' : OffsetBox) (a : Finset (F.Site F.depth)), BoxOrdered p → BoxOrdered p' → BoxesNear p p' →
        (BoxInWindow F.blockSide p ∧ a ∈ Z' ∧ boxAtOffset y p ⊆ a) → (BoxInWindow F.blockSide p' ∧ a ∈ Z' ∧ boxAtOffset y p' ⊆ a) →
        BoxInWindow F.blockSide (boxHull p p') ∧ a ∈ Z' ∧ boxAtOffset y (boxHull p p') ⊆ a := by
      rintro p p' a - - hn ⟨hw, ha, hs₁⟩ ⟨hw', -, hs₂⟩
      obtain ⟨lo, hi, hb, rfl⟩ := hZ'.1 a ha
      refine ⟨⟨?_, ?_, ?_⟩, ha, boxAtOffset_boxHull_subset hbig hL y hw hw' hb hs₁ hs₂⟩
      · intro i
        have h1 := hw.1 i
        have h2 := hw'.1 i
        simp only [boxHull]
        omega
      · intro i
        have h1 := hw.2.1 i
        have h2 := hw'.2.1 i
        simp only [boxHull]
        omega
      · intro i
        have h1 := hw.2.2 i
        have h2 := hw'.2.2 i
        simp only [boxHull]
        omega
    obtain ⟨a, ha⟩ := hM.least (fun (p : OffsetBox) (a : Finset (F.Site F.depth)) =>
      BoxInWindow F.blockSide p ∧ a ∈ Z' ∧ boxAtOffset y p ⊆ a) hA hB₂ hC q hq
    exact ⟨a, ha.2.1, ha.2.2⟩
def collarBox (q : OffsetBox) : OffsetBox := (fun i => q.1 i - 4098, fun i => q.2 i + 4098)
omit [∀ j i, NeZero (F.period j i)] in
theorem mem_centredCube_odd_iff {m : ℕ} {z : Fin 4 → ℤ} : z ∈ centredCube (2 * m + 1) ↔ ∀ i, -(m : ℤ) ≤ z i ∧ z i ≤ m := by apply _root_.YangMills.Construction.BlockLocality.mem_centredCube_odd_iff <;> assumption
omit [∀ j i, NeZero (F.period j i)] in
theorem thicken_boxAtOffset (m : ℕ) (y : F.Cell) {q : OffsetBox} (hq : BoxOrdered q) :
    thicken m (boxAtOffset y q) = boxAtOffset y (fun i => q.1 i - m, fun i => q.2 i + m) := by apply _root_.YangMills.Construction.BlockLocality.thicken_boxAtOffset <;> assumption
omit [∀ j i, NeZero (F.period j i)] in
theorem lumpCollar_boxAtOffset (y : F.Cell) {q : OffsetBox} (hq : BoxOrdered q) :
    lumpCollar (boxAtOffset y q) = boxAtOffset y (collarBox q) := by apply _root_.YangMills.Construction.BlockLocality.lumpCollar_boxAtOffset <;> assumption
def LumpBoxFamily (L : ℕ) (Q : Finset OffsetBox) : Prop :=
  ∀ q ∈ Q, ∀ i, -(3 * (L : ℤ)) ≤ q.1 i ∧ q.1 i ≤ q.2 i ∧ q.2 i ≤ 3 * (L : ℤ) ∧ q.2 i - q.1 i + 1 < 2 ^ 15
theorem boxInWindow_of_lumpBox {L : ℕ} {Q : Finset OffsetBox} (hQ : LumpBoxFamily L Q) {q : OffsetBox} (hq : q ∈ Q) : BoxInWindow L q := by
  refine ⟨fun i => (hQ q hq i).2.1, fun i => ?_, fun i => ?_⟩ <;> have := hQ q hq i <;> omega
theorem boxInWindow_collarBox {L : ℕ} (hL : 2 ^ 16 ≤ L) {Q : Finset OffsetBox} (hQ : LumpBoxFamily L Q) {r : OffsetBox}
    (hr : r ∈ Q.image collarBox) : BoxInWindow L r := by
  classical
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;> have := hQ q hq i <;> simp only [collarBox] <;> omega
theorem boxInWindow_of_merge {L : ℕ} (hL : 2 ^ 16 ≤ L) {Q M : Finset OffsetBox} (hQ : LumpBoxFamily L Q)
    (hM : IsMergeOf (Q.image collarBox) M) {q : OffsetBox} (hq : q ∈ M) : BoxInWindow L q := by
  have hw := hM.window (fun _ => -(7 * (L : ℤ))) (fun _ => 7 * (L : ℤ)) (fun r hr i => by
    have h := boxInWindow_collarBox hL hQ hr
    exact ⟨(h.2.1 i).1, (h.2.2 i).2⟩) q hq
  have ho := hM.ordered q hq
  refine ⟨ho, fun i => ?_, fun i => ?_⟩ <;> have := hw i <;> have := ho i <;> omega
theorem boxWidth_lt_of_merge {L J₀ : ℕ} (hLam : 11 * 2 ^ 12 * J₀ < L) {Q M : Finset OffsetBox} (hQ : LumpBoxFamily L Q)
    (hM : IsMergeOf (Q.image collarBox) M) (hc : Q.card < J₀) {q : OffsetBox} (hq : q ∈ M) (i : Fin 4) : boxWidth q i < L := by
  classical
  have h1 : ∑ p ∈ Q.image collarBox, (boxWidth p i + 2) ≤ ((Q.image collarBox).card : ℤ) * (11 * 2 ^ 12) := by
    have := Finset.sum_le_card_nsmul (Q.image collarBox) (fun p => boxWidth p i + 2) (11 * 2 ^ 12) (fun p hp => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
      have := hQ r hr i
      simp only [boxWidth, collarBox]
      omega)
    simpa using this
  have h2 : ((Q.image collarBox).card : ℤ) ≤ Q.card := by exact_mod_cast Finset.card_image_le
  have h4 : boxWidth q i + 2 ≤ ∑ p ∈ M, (boxWidth p i + 2) :=
    Finset.single_le_sum (f := fun p => boxWidth p i + 2) (fun p hp => by
      have := hM.ordered p hp i
      simp only [boxWidth]
      omega) hq
  have h5 := hM.sum_le i
  have h6 : ((11 * 2 ^ 12 * J₀ : ℕ) : ℤ) < L := by exact_mod_cast hLam
  push_cast at h6
  nlinarith
theorem excludedBoxes_of_family (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (hL : 2 ^ 16 ≤ F.blockSide) {J₀ : ℕ}
    (hLam : 11 * 2 ^ 12 * J₀ < F.blockSide) {Q M : Finset OffsetBox} (hQ : LumpBoxFamily F.blockSide Q)
    (hM : IsMergeOf (Q.image collarBox) M) {h : Finset (Finset (F.Site F.depth))} {y : F.Cell}
    (hb : nearbyLumps h y = Q.image (boxAtOffset y)) :
    (IsCrowded J₀ h y ↔ J₀ ≤ Q.card) ∧ (nearbyLumps h y = ∅ ↔ Q = ∅) ∧
      excludedBoxes J₀ h y = (open Classical in if J₀ ≤ Q.card then ∅ else M).image (boxAtOffset y) := by
  classical
  have hL2 : 2 ≤ F.blockSide := by omega
  have hcard : (nearbyLumps h y).card = Q.card := by
    rw [hb]
    exact Finset.card_image_of_injOn fun q hq q' hq' he =>
      boxAtOffset_injective hbig hL2 y (boxInWindow_of_lumpBox hQ hq) (boxInWindow_of_lumpBox hQ hq') he
  have hcr : IsCrowded J₀ h y ↔ J₀ ≤ Q.card := by
    unfold IsCrowded
    rw [hcard]
  refine ⟨hcr, ?_, ?_⟩
  · rw [hb, Finset.image_eq_empty]
  · unfold excludedBoxes
    by_cases hc : J₀ ≤ Q.card
    · rw [if_pos (hcr.mpr hc), if_pos hc, Finset.image_empty]
    · rw [if_neg (fun h' => hc (hcr.mp h')), if_neg hc]
      have hseeds : (nearbyLumps h y).image lumpCollar = (Q.image collarBox).image (boxAtOffset y) := by
        rw [hb, Finset.image_image, Finset.image_image]
        refine Finset.image_congr fun q hq => ?_
        exact lumpCollar_boxAtOffset y (fun i => (hQ q hq i).2.1)
      rw [hseeds]
      exact mergedBoxes_image_boxAtOffset hbig hL2 y hM (fun r hr => boxInWindow_collarBox hL hQ hr) (fun q hq => boxInWindow_of_merge hL hQ hM hq)
        (fun q hq i => boxWidth_lt_of_merge hLam hQ hM (not_le.mp hc) hq i)
end OffsetWindow
section OffsetPaths
def stepOffset (st : PathStep) : Fin 4 → ℤ := if st.2 then Pi.single st.1 1 else -Pi.single st.1 1
def offsetPath : (Fin 4 → ℤ) → List PathStep → List (Fin 4 → ℤ)
  | u, [] => [u]
  | u, st :: r => u :: offsetPath (u + stepOffset st) r
def offsetPathEnd : (Fin 4 → ℤ) → List PathStep → (Fin 4 → ℤ)
  | u, [] => u
  | u, st :: r => offsetPathEnd (u + stepOffset st) r
theorem offsetPathEnd_append (u : Fin 4 → ℤ) (l l' : List PathStep) : offsetPathEnd u (l ++ l') = offsetPathEnd (offsetPathEnd u l) l' := by
  induction l generalizing u with
  | nil => rfl
  | cons st r ih => exact ih _
theorem mem_offsetPath_self (u : Fin 4 → ℤ) (l : List PathStep) : u ∈ offsetPath u l := by
  cases l <;> simp [offsetPath]
theorem mem_offsetPath_append {u p : Fin 4 → ℤ} {l l' : List PathStep} (h : p ∈ offsetPath u (l ++ l')) :
    p ∈ offsetPath u l ∨ p ∈ offsetPath (offsetPathEnd u l) l' := by
  induction l generalizing u with
  | nil => exact Or.inr h
  | cons st r ih =>
    simp only [List.cons_append, offsetPath, List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inl (by simp [offsetPath])
    · rcases ih h with h | h
      · exact Or.inl (by simp [offsetPath, h])
      · exact Or.inr h
theorem stepOffset_flip (st : PathStep) : stepOffset (st.1, !st.2) = - stepOffset st := by apply _root_.YangMills.Construction.LatticePaths.stepDisplacement_flip <;> assumption
theorem offsetPathEnd_reversePath (u : Fin 4 → ℤ) (l : List PathStep) : offsetPathEnd (offsetPathEnd u l) (reversePath l) = u := by
  induction l generalizing u with
  | nil => rfl
  | cons st r ih =>
    have : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    rw [this, offsetPathEnd_append]
    simp only [offsetPathEnd]
    rw [ih, stepOffset_flip]
    simp
theorem mem_offsetPath_of_reversePath {v p : Fin 4 → ℤ} {l : List PathStep} (h : p ∈ offsetPath (offsetPathEnd v l) (reversePath l)) :
    p ∈ offsetPath v l := by
  induction l generalizing v with
  | nil => exact h
  | cons st r ih =>
    have hr : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    rw [hr] at h
    simp only [offsetPathEnd] at h
    rcases mem_offsetPath_append h with h | h
    · exact List.mem_cons_of_mem _ (ih h)
    · rw [offsetPathEnd_reversePath] at h
      simp only [offsetPath, stepOffset_flip, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · simp [offsetPath, mem_offsetPath_self]
      · simp [offsetPath]
def InBounds (lo hi u : Fin 4 → ℤ) : Prop := ∀ k, lo k ≤ u k ∧ u k ≤ hi k
def partialShift (u h : Fin 4 → ℤ) (S : Finset (Fin 4)) : Fin 4 → ℤ := fun k => u k + if k ∈ S then h k else 0
theorem replicate_inBounds {lo hi : Fin 4 → ℤ} (a : Fin 4) (b : Bool) :
    ∀ (m : ℕ) (u : Fin 4 → ℤ), InBounds lo hi u →
      InBounds lo hi (u + (m : ℤ) • stepOffset (a, b)) →
      (∀ p ∈ offsetPath u (List.replicate m (a, b)), InBounds lo hi p) ∧
        offsetPathEnd u (List.replicate m (a, b)) = u + (m : ℤ) • stepOffset (a, b) := by
  intro m
  induction m with
  | zero =>
    intro u hu _
    simp [offsetPath, offsetPathEnd, hu]
  | succ m ih =>
    intro u hu hv
    have hs : InBounds lo hi (u + stepOffset (a, b)) := by
      intro k
      have h1 := hu k
      have h2 := hv k
      by_cases hk : k = a
      · subst hk
        cases b <;> simp [stepOffset] at h2 ⊢ <;> omega
      · cases b <;> simp [stepOffset, hk] at h2 ⊢ <;> omega
    have he : u + stepOffset (a, b) + (m : ℤ) • stepOffset (a, b) = u + ((m + 1 : ℕ) : ℤ) • stepOffset (a, b) := by
      push_cast
      rw [add_smul, one_smul]
      abel
    obtain ⟨h1, h2⟩ := ih (u + stepOffset (a, b)) hs (he ▸ hv)
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [List.replicate_succ, offsetPath, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hu
      · exact h1 p hp
    · simp only [List.replicate_succ, offsetPathEnd]
      rw [h2, he]
theorem natAbs_smul_stepOffset (a : Fin 4) (c : ℤ) :
    ((c.natAbs : ℤ)) • stepOffset (a, decide (0 ≤ c)) = Pi.single a c := by apply _root_.YangMills.Construction.BlockLocality.natAbs_smul_stepOffset <;> assumption
theorem flatMap_inBounds {lo hi u h : Fin 4 → ℤ} (hu : InBounds lo hi u) (hv : InBounds lo hi (u + h)) (π : Equiv.Perm (Fin 4)) :
    ∀ (ks : List (Fin 4)) (S : Finset (Fin 4)), ks.Nodup → (∀ k ∈ ks, π k ∉ S) →
      (∀ p ∈ offsetPath (partialShift u h S)
          (ks.flatMap fun k => List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))), InBounds lo hi p) ∧
        offsetPathEnd (partialShift u h S) (ks.flatMap fun k => List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))) =
          partialShift u h (S ∪ (ks.map π).toFinset) := by
  have hpart : ∀ S, InBounds lo hi (partialShift u h S) := by
    intro S k
    have h1 := hu k
    have h2 := hv k
    simp only [Pi.add_apply] at h2
    simp only [partialShift]
    split_ifs <;> omega
  intro ks
  induction ks with
  | nil =>
    intro S _ _
    simp only [List.flatMap_nil, offsetPathEnd, offsetPath, List.mem_singleton, List.map_nil, List.toFinset_nil,
      Finset.union_empty]
    exact ⟨fun p hp => hp ▸ hpart S, trivial⟩
  | cons a r ih =>
    intro S hnd hS
    obtain ⟨hna, hnr⟩ := List.nodup_cons.mp hnd
    have haS : π a ∉ S := hS a (List.mem_cons_self)
    have hend : partialShift u h S + ((h (π a)).natAbs : ℤ) • stepOffset (π a, decide (0 ≤ h (π a))) =
        partialShift u h (insert (π a) S) := by
      rw [natAbs_smul_stepOffset]
      funext k
      by_cases hk : k = π a
      · subst hk
        simp [partialShift, haS]
      · simp [partialShift, hk]
    obtain ⟨h1, h2⟩ := replicate_inBounds (lo := lo) (hi := hi) (π a) (decide (0 ≤ h (π a))) (h (π a)).natAbs
      (partialShift u h S) (hpart S) (hend ▸ hpart _)
    have hS' : ∀ k ∈ r, π k ∉ insert (π a) S := by
      intro k hk hmem
      rcases Finset.mem_insert.mp hmem with he | he
      · exact hna (π.injective he ▸ hk)
      · exact hS k (List.mem_cons_of_mem _ hk) he
    obtain ⟨h3, h4⟩ := ih (insert (π a) S) hnr hS'
    simp only [List.flatMap_cons]
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases mem_offsetPath_append hp with hp | hp
      · exact h1 p hp
      · rw [h2, hend] at hp
        exact h3 p hp
    · rw [offsetPathEnd_append, h2, hend, h4]
      congr 1
      ext k
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_map, List.map_cons,
        List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
theorem axisPath_inBounds {lo hi u h : Fin 4 → ℤ} (hu : InBounds lo hi u) (hv : InBounds lo hi (u + h)) (π : Equiv.Perm (Fin 4)) :
    (∀ p ∈ offsetPath u (axisPath h π), InBounds lo hi p) ∧ offsetPathEnd u (axisPath h π) = u + h := by
  have h0 : partialShift u h ∅ = u := by
    funext k
    simp [partialShift]
  have := flatMap_inBounds hu hv π (List.finRange 4) ∅ (List.nodup_finRange 4) (by simp)
  rw [h0] at this
  refine ⟨this.1, this.2.trans ?_⟩
  funext k
  have : k ∈ ((List.finRange 4).map π).toFinset := by
    simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, true_and]
    exact ⟨π.symm k, by simp⟩
  simp [partialShift, this]
def contourOffsetPath (L : ℕ) (z₀ z₁ ξ : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (i : Fin 4) : List PathStep :=
  axisPath (ξ - z₀) π ++ List.replicate L (i, true) ++ reversePath (axisPath (ξ - z₁) π)
theorem contourOffsetPath_inBox {L : ℕ} {z₀ z₁ ξ : Fin 4 → ℤ} (h₀ : z₀ ∈ centredCube L) (h₁ : z₁ ∈ centredCube L) (hξ : ξ ∈ centredCube L)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    ∀ p ∈ offsetPath z₀ (contourOffsetPath L z₀ z₁ ξ π i), OffsetInBox (2 * L) p := by
  have hc : ∀ {z : Fin 4 → ℤ}, z ∈ centredCube L → ∀ k, -(((L : ℤ) - 1) / 2) ≤ z k ∧ z k ≤ ((L : ℤ) - 1) / 2 :=
    fun h => mem_centredCube_iff.mp h
  set lo : Fin 4 → ℤ := fun _ => -(2 * (L : ℤ)) with hlo
  set hi : Fin 4 → ℤ := fun _ => 2 * (L : ℤ) with hhi
  have hbox : ∀ {z : Fin 4 → ℤ}, z ∈ centredCube L → InBounds lo hi z := by
    intro z hz k
    have := hc hz k
    simp only [hlo, hhi]
    omega
  have hshift : ∀ {z : Fin 4 → ℤ}, z ∈ centredCube L → InBounds lo hi (z + Pi.single i (L : ℤ)) := by
    intro z hz k
    have := hc hz k
    by_cases hk : k = i
    · subst hk
      simp only [hlo, hhi, Pi.add_apply, Pi.single_eq_same]
      omega
    · simp only [hlo, hhi, Pi.add_apply, Pi.single_eq_of_ne hk]
      omega
  obtain ⟨a₁, a₂⟩ := axisPath_inBounds (hbox h₀) (by simpa using hbox hξ) π (h := ξ - z₀)
  have hend₀ : z₀ + (ξ - z₀) = ξ := by abel
  rw [hend₀] at a₂
  have hrep : (L : ℤ) • stepOffset (i, true) = Pi.single i (L : ℤ) := by
    have := natAbs_smul_stepOffset i (L : ℤ)
    simpa using this
  obtain ⟨b₁, b₂⟩ := replicate_inBounds (lo := lo) (hi := hi) i true L ξ (hbox hξ) (by rw [hrep]; exact hshift hξ)
  rw [hrep] at b₂
  obtain ⟨c₁, c₂⟩ := axisPath_inBounds (u := z₁ + Pi.single i (L : ℤ)) (h := ξ - z₁) (hshift h₁)
    (by
      have : z₁ + Pi.single i (L : ℤ) + (ξ - z₁) = ξ + Pi.single i (L : ℤ) := by abel
      rw [this]
      exact hshift hξ) π
  have hend₁ : z₁ + Pi.single i (L : ℤ) + (ξ - z₁) = ξ + Pi.single i (L : ℤ) := by abel
  rw [hend₁] at c₂
  intro p hp
  have hin : InBounds lo hi p := by
    unfold contourOffsetPath at hp
    rcases mem_offsetPath_append hp with hp | hp
    · rcases mem_offsetPath_append hp with hp | hp
      · exact a₁ p hp
      · rw [a₂] at hp
        exact b₁ p hp
    · rw [offsetPathEnd_append, a₂, b₂, ← c₂] at hp
      exact c₁ p (mem_offsetPath_of_reversePath hp)
  intro k
  have := hin k
  simp only [hlo, hhi] at this
  rw [abs_le]
  exact_mod_cast this
theorem inWindow_of_offsetInBox {L m : ℕ} (hm : m ≤ 7 * L) {u : Fin 4 → ℤ} (h : OffsetInBox m u) : InWindow L u := by apply _root_.YangMills.Construction.BlockLocality.window_of_offsetInBox <;> assumption
theorem offsetInBox_of_mem_centredCube {L : ℕ} {z : Fin 4 → ℤ} (h : z ∈ centredCube L) : OffsetInBox L z := by apply _root_.YangMills.Construction.BlockLocality.offsetInBox_of_mem_centredCube <;> assumption
end OffsetPaths
section OffsetContours
variable {F F' : BlockFrame} [∀ j i, NeZero (F.period j i)] [∀ j i, NeZero (F'.period j i)]
theorem siteAtOffset_add_stepDisplacement (y : F.Cell) (u : Fin 4 → ℤ) (st : PathStep) :
    (siteAtOffset y u : F.Site F.depth) + stepDisplacement F.depth st = siteAtOffset y (u + stepOffset st) := by apply _root_.YangMills.Construction.BlockLocality.siteAtOffset_add_stepDisplacement <;> assumption
theorem pathSites_siteAtOffset (y : F.Cell) (u : Fin 4 → ℤ) (l : List PathStep) :
    pathSites (siteAtOffset y u) l = (offsetPath u l).map (siteAtOffset y) := by
  induction l generalizing u with
  | nil => rfl
  | cons st r ih =>
    simp only [pathSites, offsetPath, List.map_cons, siteAtOffset_add_stepDisplacement, ih]
theorem pathHolonomy_eq_of_agree {R : ℕ} (X : F.GaugeField F.depth) (X' : F'.GaugeField F'.depth) (y : F.Cell) (y' : F'.Cell)
    (hag : ∀ (u : Fin 4 → ℤ) (i : Fin 4), OffsetInBox R u → OffsetInBox R (u + Pi.single i 1) →
      X (siteAtOffset y u) i = X' (siteAtOffset y' u) i) (l : List PathStep) (u : Fin 4 → ℤ)
    (hp : ∀ p ∈ offsetPath u l, OffsetInBox R p) :
    pathHolonomy X (siteAtOffset y u) l = pathHolonomy X' (siteAtOffset y' u) l := by
  induction l generalizing u with
  | nil => rfl
  | cons st r ih =>
    simp only [pathHolonomy]
    rw [siteAtOffset_add_stepDisplacement, siteAtOffset_add_stepDisplacement]
    have h1 : OffsetInBox R u := hp u (by simp [offsetPath])
    have h2 : OffsetInBox R (u + stepOffset st) := hp _ (by simp [offsetPath, mem_offsetPath_self])
    rw [ih _ fun p hq => hp p (by simp [offsetPath, hq])]
    congr 1
    rcases st with ⟨i, b⟩
    cases b
    · have h3 : OffsetInBox R (u - Pi.single i 1) := by simpa [stepOffset, sub_eq_add_neg] using h2
      have h4 := hag (u - Pi.single i 1) i h3 (by simpa using h1)
      have e1 : (siteAtOffset y u : F.Site F.depth) - unitStep F.depth i = siteAtOffset y (u - Pi.single i 1) := by
        simp [siteAtOffset, unitStep, sub_eq_add_neg, _root_.YangMills.Construction.TorusContours.siteOfCoords_add, _root_.YangMills.Construction.TorusContours.siteOfCoords_neg, add_assoc]
      have e2 : (siteAtOffset y' u : F'.Site F'.depth) - unitStep F'.depth i = siteAtOffset y' (u - Pi.single i 1) := by
        simp [siteAtOffset, unitStep, sub_eq_add_neg, _root_.YangMills.Construction.TorusContours.siteOfCoords_add, _root_.YangMills.Construction.TorusContours.siteOfCoords_neg, add_assoc]
      simp only [linkValue, Bool.false_eq_true, if_false, e1, e2, h4]
    · have h4 := hag u i h1 (by simpa [stepOffset] using h2)
      simp only [linkValue, if_true, h4]
theorem siteAtOffset_add_unitStep (y : F.Cell) (i : Fin 4) (v : Fin 4 → ℤ) :
    (siteAtOffset (y + unitStep F.top i) v : F.Site F.depth) = siteAtOffset y (v + Pi.single i (F.blockSide : ℤ)) := by apply _root_.YangMills.Construction.BlockLocality.siteAtOffset_add_unitStep <;> assumption
theorem inWindow_of_mem_centredCube {L : ℕ} {z : Fin 4 → ℤ} (h : z ∈ centredCube L) : InWindow L z := by apply _root_.YangMills.Construction.BlockLocality.window_of_mem_centredCube <;> assumption
theorem contourPath_eq (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (hL : 2 ≤ F.blockSide) {b : F.Cell → F.Site F.depth}
    {y : F.Cell} {i : Fin 4} {z₀ z₁ ξ : Fin 4 → ℤ} (h₀ : z₀ ∈ centredCube F.blockSide) (h₁ : z₁ ∈ centredCube F.blockSide) (hξ : ξ ∈ centredCube F.blockSide)
    (hb₀ : b y = siteAtOffset y z₀) (hb₁ : b (y + unitStep F.top i) = siteAtOffset (y + unitStep F.top i) z₁)
    (π : Equiv.Perm (Fin 4)) : contourPath b (y, i) ξ π = contourOffsetPath F.blockSide z₀ z₁ ξ π i := by
  have hoff : ∀ (y₁ : F.Cell) {z : Fin 4 → ℤ}, z ∈ centredCube F.blockSide →
      minimalOffset (siteAtOffset y₁ z : F.Site F.depth) (cellCentre F.depth y₁ + siteOfCoords F.depth ξ) = ξ - z := by
    intro y₁ z hz
    funext k
    have h1 := mem_centredCube_iff.mp hz k
    have h2 := mem_centredCube_iff.mp hξ k
    exact valMinAbs_siteAtOffset_sub hbig hL y₁ (inWindow_of_mem_centredCube hξ) (inWindow_of_mem_centredCube hz) k (by rw [abs_le]; omega)
  simp only [contourPath, contourOffsetPath, hb₀, hb₁, hoff _ h₀, hoff _ h₁]
def IsGoodOffsetContour (L : ℕ) (M₀ M₁ : Finset OffsetBox) (z₀ z₁ : Fin 4 → ℤ) (i : Fin 4)
    (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) : Prop :=
  ∀ p ∈ offsetPath z₀ (contourOffsetPath L z₀ z₁ e.1 e.2 i),
    (∀ q ∈ M₀, ¬ MemBox p q) ∧ ∀ q ∈ M₁, ¬ MemBox (p - Pi.single i (L : ℤ)) q
open Classical in
def usedOffsetContours (c₀ c₁ : Prop) (L : ℕ) (M₀ M₁ : Finset OffsetBox) (z₀ z₁ : Fin 4 → ℤ) (i : Fin 4) :
    Finset ((Fin 4 → ℤ) × Equiv.Perm (Fin 4)) :=
  if c₀ ∨ c₁ ∨ ((centredCube L ×ˢ Finset.univ).filter (IsGoodOffsetContour L M₀ M₁ z₀ z₁ i)) = ∅ then centredCube L ×ˢ Finset.univ
  else (centredCube L ×ˢ Finset.univ).filter (IsGoodOffsetContour L M₀ M₁ z₀ z₁ i)
theorem mem_centredCube_of_mem_usedOffsetContours (c₀ c₁ : Prop) (L : ℕ) (M₀ M₁ : Finset OffsetBox) (z₀ z₁ : Fin 4 → ℤ) (i : Fin 4)
    {e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)} (he : e ∈ usedOffsetContours c₀ c₁ L M₀ M₁ z₀ z₁ i) : e.1 ∈ centredCube L := by
  classical
  unfold usedOffsetContours at he
  split_ifs at he
  · exact (Finset.mem_product.mp he).1
  · exact (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1
theorem isGoodContour_iff (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (hL : 2 ≤ F.blockSide) {J₀ : ℕ}
    {h : Finset (Finset (F.Site F.depth))} {b : F.Cell → F.Site F.depth} {y : F.Cell} {i : Fin 4}
    {z₀ z₁ : Fin 4 → ℤ} (h₀ : z₀ ∈ centredCube F.blockSide) (h₁ : z₁ ∈ centredCube F.blockSide)
    (hb₀ : b y = siteAtOffset y z₀) (hb₁ : b (y + unitStep F.top i) = siteAtOffset (y + unitStep F.top i) z₁)
    {M₀ M₁ : Finset OffsetBox} (hM₀ : ∀ q ∈ M₀, BoxInWindow F.blockSide q) (hM₁ : ∀ q ∈ M₁, BoxInWindow F.blockSide q)
    (hB₀ : excludedBoxes J₀ h y = M₀.image (boxAtOffset y))
    (hB₁ : excludedBoxes J₀ h (y + unitStep F.top i) = M₁.image (boxAtOffset (y + unitStep F.top i)))
    (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) (he : e.1 ∈ centredCube F.blockSide) :
    IsGoodContour J₀ h b (y, i) e.1 e.2 ↔ IsGoodOffsetContour F.blockSide M₀ M₁ z₀ z₁ i e := by
  classical
  have hwin : ∀ p ∈ offsetPath z₀ (contourOffsetPath F.blockSide z₀ z₁ e.1 e.2 i), InWindow F.blockSide p ∧
      InWindow F.blockSide (p - Pi.single i (F.blockSide : ℤ)) := by
    intro p hp
    have hb := contourOffsetPath_inBox h₀ h₁ he e.2 i p hp
    refine ⟨inWindow_of_offsetInBox (by omega) hb, fun k => ?_⟩
    have h2 := abs_le.mp (hb k)
    push_cast at h2
    by_cases hk : k = i
    · subst hk
      simp only [Pi.sub_apply, Pi.single_eq_same]
      omega
    · simp only [Pi.sub_apply, Pi.single_eq_of_ne hk, sub_zero]
      omega
  have hsh : ∀ p : Fin 4 → ℤ, (siteAtOffset y p : F.Site F.depth) =
      siteAtOffset (y + unitStep F.top i) (p - Pi.single i (F.blockSide : ℤ)) := by
    intro p
    rw [siteAtOffset_add_unitStep, sub_add_cancel]
  unfold IsGoodContour IsGoodOffsetContour
  simp only []
  rw [contourPath_eq hbig hL h₀ h₁ he hb₀ hb₁ e.2, hb₀, pathSites_siteAtOffset, hB₀, hB₁]
  constructor
  · intro H p hp
    have hx : (siteAtOffset y p : F.Site F.depth) ∈
        (offsetPath z₀ (contourOffsetPath F.blockSide z₀ z₁ e.1 e.2 i)).map (siteAtOffset y) := List.mem_map_of_mem hp
    refine ⟨fun q hq hin => H _ hx _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hq))
      ((siteAtOffset_mem_boxAtOffset_iff hbig hL y (hwin p hp).1 (hM₀ q hq)).mpr hin),
      fun q hq hin => H _ hx _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq)) ?_⟩
    rw [hsh p]
    exact (siteAtOffset_mem_boxAtOffset_iff hbig hL _ (hwin p hp).2 (hM₁ q hq)).mpr hin
  · intro H x hx B hB hmem
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    rcases Finset.mem_union.mp hB with hB | hB
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
      exact (H p hp).1 q hq ((siteAtOffset_mem_boxAtOffset_iff hbig hL y (hwin p hp).1 (hM₀ q hq)).mp hmem)
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
      rw [hsh p] at hmem
      exact (H p hp).2 q hq ((siteAtOffset_mem_boxAtOffset_iff hbig hL _ (hwin p hp).2 (hM₁ q hq)).mp hmem)
theorem usedContours_eq (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (hL : 2 ≤ F.blockSide) {J₀ : ℕ}
    {h : Finset (Finset (F.Site F.depth))} {b : F.Cell → F.Site F.depth} {y : F.Cell} {i : Fin 4}
    {z₀ z₁ : Fin 4 → ℤ} (h₀ : z₀ ∈ centredCube F.blockSide) (h₁ : z₁ ∈ centredCube F.blockSide)
    (hb₀ : b y = siteAtOffset y z₀) (hb₁ : b (y + unitStep F.top i) = siteAtOffset (y + unitStep F.top i) z₁)
    {M₀ M₁ : Finset OffsetBox} (hM₀ : ∀ q ∈ M₀, BoxInWindow F.blockSide q) (hM₁ : ∀ q ∈ M₁, BoxInWindow F.blockSide q)
    (hB₀ : excludedBoxes J₀ h y = M₀.image (boxAtOffset y))
    (hB₁ : excludedBoxes J₀ h (y + unitStep F.top i) = M₁.image (boxAtOffset (y + unitStep F.top i)))
    {c₀ c₁ : Prop} (hc₀ : IsCrowded J₀ h y ↔ c₀) (hc₁ : IsCrowded J₀ h (y + unitStep F.top i) ↔ c₁) :
    usedContours J₀ h b (y, i) = usedOffsetContours c₀ c₁ F.blockSide M₀ M₁ z₀ z₁ i := by
  classical
  have hf : (allContours F).filter (fun e => IsGoodContour J₀ h b (y, i) e.1 e.2) =
      (centredCube F.blockSide ×ˢ Finset.univ).filter (IsGoodOffsetContour F.blockSide M₀ M₁ z₀ z₁ i) :=
    Finset.filter_congr fun e he => isGoodContour_iff hbig hL h₀ h₁ hb₀ hb₁ hM₀ hM₁ hB₀ hB₁ e
      (Finset.mem_product.mp he).1
  unfold usedContours usedOffsetContours
  simp only []
  rw [hf]
  by_cases hC : c₀ ∨ c₁ ∨ ((centredCube F.blockSide ×ˢ Finset.univ).filter (IsGoodOffsetContour F.blockSide M₀ M₁ z₀ z₁ i)) = ∅
  · rw [if_pos hC, if_pos (by rwa [hc₀, hc₁])]
    rfl
  · rw [if_neg hC, if_neg (by rwa [hc₀, hc₁])]
theorem contourMean_eq (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (hL : 2 ≤ F.blockSide) {J₀ : ℕ}
    {h : Finset (Finset (F.Site F.depth))} {b : F.Cell → F.Site F.depth} {y : F.Cell} {i : Fin 4}
    {z₀ z₁ : Fin 4 → ℤ} (h₀ : z₀ ∈ centredCube F.blockSide) (h₁ : z₁ ∈ centredCube F.blockSide)
    (hb₀ : b y = siteAtOffset y z₀) (hb₁ : b (y + unitStep F.top i) = siteAtOffset (y + unitStep F.top i) z₁)
    {M₀ M₁ : Finset OffsetBox} (hM₀ : ∀ q ∈ M₀, BoxInWindow F.blockSide q) (hM₁ : ∀ q ∈ M₁, BoxInWindow F.blockSide q)
    (hB₀ : excludedBoxes J₀ h y = M₀.image (boxAtOffset y))
    (hB₁ : excludedBoxes J₀ h (y + unitStep F.top i) = M₁.image (boxAtOffset (y + unitStep F.top i)))
    {c₀ c₁ : Prop} (hc₀ : IsCrowded J₀ h y ↔ c₀) (hc₁ : IsCrowded J₀ h (y + unitStep F.top i) ↔ c₁)
    (X : F.GaugeField F.depth) :
    contourMean J₀ h b X (y, i) = (1 / ((usedOffsetContours c₀ c₁ F.blockSide M₀ M₁ z₀ z₁ i).card : ℝ)) •
      ∑ e ∈ usedOffsetContours c₀ c₁ F.blockSide M₀ M₁ z₀ z₁ i,
        ((pathHolonomy X (siteAtOffset y z₀) (contourOffsetPath F.blockSide z₀ z₁ e.1 e.2 i) : UnitQuaternion) : ℍ[ℝ]) := by
  unfold contourMean
  rw [usedContours_eq hbig hL h₀ h₁ hb₀ hb₁ hM₀ hM₁ hB₀ hB₁ hc₀ hc₁]
  refine congrArg _ (Finset.sum_congr rfl fun e he => ?_)
  have := mem_centredCube_of_mem_usedOffsetContours _ _ _ _ _ _ _ _ he
  simp only []
  rw [contourPath_eq hbig hL h₀ h₁ this hb₀ hb₁ e.2, hb₀]
def IsBaseOffset (J₀ : ℕ) (Q M : Finset OffsetBox) (z : Fin 4 → ℤ) : Prop :=
  ((Q = ∅ ∨ J₀ ≤ Q.card) → z = 0) ∧
    (¬ (Q = ∅ ∨ J₀ ≤ Q.card) → ∀ q ∈ M, ∀ v, MemBox v q → ∀ i, v i ≠ z i)
theorem mem_baseSitesAt_of_not_trivial {J₀ : ℕ} {h : Finset (Finset (F.Site F.depth))} {y : F.Cell} {x : F.Site F.depth}
    (hc : ¬ (nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y)) :
    x ∈ baseSitesAt J₀ h y ↔ x ∈ sitesBelow F.depth y ∧ ∀ B ∈ excludedBoxes J₀ h y, ∀ x' ∈ B, ∀ i, x' i ≠ x i := by apply _root_.YangMills.Construction.BlockLocality.mem_baseSitesAt_of_open <;> assumption
theorem siteAtOffset_mem_baseSitesAt_iff (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (hL : 2 ^ 16 ≤ F.blockSide) {J₀ : ℕ}
    (hLam : 11 * 2 ^ 12 * J₀ < F.blockSide) {Q M : Finset OffsetBox} (hQ : LumpBoxFamily F.blockSide Q)
    (hM : IsMergeOf (Q.image collarBox) M) {h : Finset (Finset (F.Site F.depth))} {y : F.Cell}
    (hb : nearbyLumps h y = Q.image (boxAtOffset y)) {z : Fin 4 → ℤ} (hz : z ∈ centredCube F.blockSide) :
    siteAtOffset y z ∈ baseSitesAt J₀ h y ↔ IsBaseOffset J₀ Q M z := by
  classical
  have hL2 : 2 ≤ F.blockSide := by omega
  obtain ⟨hcr, hem, hbx⟩ := excludedBoxes_of_family hbig hL hLam hQ hM hb
  have hC : (nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y) ↔ (Q = ∅ ∨ J₀ ≤ Q.card) := by rw [hem, hcr]
  by_cases hc : Q = ∅ ∨ J₀ ≤ Q.card
  · unfold baseSitesAt
    rw [if_pos (hC.mpr hc), Finset.mem_singleton]
    have h0 : (cellCentre F.depth y : F.Site F.depth) = siteAtOffset y 0 := by
      rw [siteAtOffset, _root_.YangMills.Construction.TorusContours.siteOfCoords_zero, add_zero]
    rw [h0, siteAtOffset_eq_iff hbig hL2 y (inWindow_of_mem_centredCube hz) (inWindow_of_mem_centredCube (zero_mem_centredCube (by omega)))]
    exact ⟨fun h1 => ⟨fun _ => h1, fun h2 => absurd hc h2⟩, fun h1 => h1.1 hc⟩
  · rw [mem_baseSitesAt_of_not_trivial (fun h1 => hc (hC.mp h1))]
    have hnc : ¬ J₀ ≤ Q.card := fun h1 => hc (Or.inr h1)
    rw [if_neg hnc] at hbx
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨fun h3 => absurd h3 hc, fun _ q hq v hv i he => ?_⟩
      refine h2 (boxAtOffset y q) (hbx ▸ Finset.mem_image_of_mem _ hq) (siteAtOffset y v)
        (mem_boxAtOffset.mpr ⟨v, hv, rfl⟩) i ?_
      exact (siteAtOffset_apply_eq_iff hbig y (abs_sub_le_of_inWindow (inWindow_of_memBox (boxInWindow_of_merge hL hQ hM hq) hv) (inWindow_of_mem_centredCube hz) i) hL2).mpr he
    · rintro ⟨-, h2⟩
      refine ⟨(mem_sitesBelow_iff y _).mpr ⟨z, hz, rfl⟩, fun B hB x hx i he => ?_⟩
      rw [hbx] at hB
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨v, hv, rfl⟩ := mem_boxAtOffset.mp hx
      exact h2 hc q hq v hv i
        ((siteAtOffset_apply_eq_iff hbig y (abs_sub_le_of_inWindow (inWindow_of_memBox (boxInWindow_of_merge hL hQ hM hq) hv) (inWindow_of_mem_centredCube hz) i) hL2).mp he)
theorem card_baseSitesAt_eq (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (hL : 2 ^ 16 ≤ F.blockSide) {J₀ : ℕ}
    (hLam : 11 * 2 ^ 12 * J₀ < F.blockSide) {Q M : Finset OffsetBox} (hQ : LumpBoxFamily F.blockSide Q)
    (hM : IsMergeOf (Q.image collarBox) M) {h : Finset (Finset (F.Site F.depth))} {y : F.Cell}
    (hb : nearbyLumps h y = Q.image (boxAtOffset y)) :
    (baseSitesAt J₀ h y).card =
      (open Classical in ((centredCube F.blockSide).filter (IsBaseOffset J₀ Q M)).card) := by
  classical
  have hsub : ∀ x ∈ baseSitesAt J₀ h y, ∃ z ∈ centredCube F.blockSide, x = siteAtOffset y z := by
    intro x hx
    by_cases hc : nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y
    · unfold baseSitesAt at hx
      rw [if_pos hc] at hx
      rw [Finset.mem_singleton.mp hx]
      exact ⟨0, zero_mem_centredCube (by omega), by rw [siteAtOffset, _root_.YangMills.Construction.TorusContours.siteOfCoords_zero, add_zero]⟩
    · exact (mem_sitesBelow_iff y x).mp ((mem_baseSitesAt_of_not_trivial hc).mp hx).1
  have himg : baseSitesAt J₀ h y = ((centredCube F.blockSide).filter (IsBaseOffset J₀ Q M)).image (siteAtOffset y) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := hsub x hx
      exact ⟨z, ⟨hz, (siteAtOffset_mem_baseSitesAt_iff hbig hL hLam hQ hM hb hz).mp hx⟩, rfl⟩
    · rintro ⟨z, ⟨hz, h1⟩, rfl⟩
      exact (siteAtOffset_mem_baseSitesAt_iff hbig hL hLam hQ hM hb hz).mpr h1
  rw [himg]
  refine Finset.card_image_of_injOn fun z hz z' hz' he => ?_
  exact (siteAtOffset_eq_iff hbig (by omega) y (inWindow_of_mem_centredCube (Finset.mem_filter.mp hz).1)
    (inWindow_of_mem_centredCube (Finset.mem_filter.mp hz').1)).mp he
theorem isBaseChoice_iff (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth) :
    IsBaseChoice J₀ h b ↔ ∀ y, b y ∈ baseSitesAt J₀ h y := by
  classical
  constructor
  · intro hb y
    by_cases hc : nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y
    · unfold baseSitesAt
      rw [if_pos hc, Finset.mem_singleton]
      exact (hb y).1 hc
    · exact (mem_baseSitesAt_of_not_trivial hc).mpr ((hb y).2 hc)
  · intro hb y
    have h1 := hb y
    refine ⟨fun hc => ?_, fun hc => (mem_baseSitesAt_of_not_trivial hc).mp h1⟩
    unfold baseSitesAt at h1
    rw [if_pos hc, Finset.mem_singleton] at h1
    exact h1
end OffsetContours
section HotLumps
variable {F F' : BlockFrame} [∀ j i, NeZero (F.period j i)] [∀ j i, NeZero (F'.period j i)]
def lumpBoxOf {L : ℕ} (g : LumpGrid L) (z : Fin 4 → ℤ) : OffsetBox :=
  (fun i => z i - offsetFromCentre L (z i) + g.lower (offsetFromCentre L (z i)),
    fun i => z i - offsetFromCentre L (z i) + g.upper (offsetFromCentre L (z i)))
theorem offsetFromCentre_spec {L : ℕ} (hL : 0 < L) (hodd : Odd L) (c : ℤ) :
    |offsetFromCentre L c| ≤ ((L : ℤ) - 1) / 2 ∧ c - offsetFromCentre L c = (L : ℤ) * ((c + ((L : ℤ) - 1) / 2) / (L : ℤ)) := by apply _root_.YangMills.Construction.BlockLocality.offsetFromCentre_spec <;> assumption
theorem offsetFromCentre_add_mul {L : ℕ} (c m : ℤ) : offsetFromCentre L (c + (L : ℤ) * m) = offsetFromCentre L c := by apply _root_.YangMills.Construction.BlockLocality.offsetFromCentre_add_mul <;> assumption
omit [∀ j i, NeZero (F.period j i)] [∀ j i, NeZero (F'.period j i)] in
theorem boxSites_add_period {j : ℕ} (a b s : Fin 4 → ℤ) (hs : ∀ i, (F.period j i : ℤ) ∣ s i) :
    (boxSites j (fun i => a i + s i) (fun i => b i + s i) : Finset (F.Site j)) = boxSites j a b := by apply _root_.YangMills.Construction.BlockLocality.boxSites_add_period <;> assumption
theorem lumpOf_siteAtOffset {g : LumpGrid F.blockSide} (y : F.Cell) (z : Fin 4 → ℤ) :
    lumpOf g (siteAtOffset y z : F.Site F.depth) = boxAtOffset y (lumpBoxOf g z) := by apply _root_.YangMills.Construction.BlockLocality.lumpOf_siteAtOffset <;> assumption
def InTwoBlocks (L : ℕ) (z : Fin 4 → ℤ) : Prop := ∀ i, |z i| ≤ 2 * (L : ℤ) + ((L : ℤ) - 1) / 2
theorem lumpBoxOf_bounds {L : ℕ} (hL : 0 < L) (hodd : Odd L) (g : LumpGrid L) (z : Fin 4 → ℤ) (i : Fin 4) :
    (lumpBoxOf g z).1 i ≤ z i ∧ z i ≤ (lumpBoxOf g z).2 i ∧ (lumpBoxOf g z).2 i - (lumpBoxOf g z).1 i + 1 < 2 ^ 15 := by apply _root_.YangMills.Construction.BlockLocality.lumpBox_spec <;> assumption
omit [∀ j i, NeZero (F.period j i)] [∀ j i, NeZero (F'.period j i)] in
theorem mem_cutBelow_cellBall {y : F.Cell} {x : F.Site F.depth} :
    x ∈ cutBelow F.depth (cellBall y 2) ↔ ∃ m : Fin 4 → ℤ, (∀ i, -2 ≤ m i ∧ m i ≤ 2) ∧
      ∃ w ∈ centredCube F.blockSide, x = siteAtOffset (y + siteOfCoords F.top m) w := by apply _root_.YangMills.Construction.BlockLocality.mem_cutBelow_cellBall <;> assumption
theorem siteAtOffset_add_siteOfCoords (y : F.Cell) (m w : Fin 4 → ℤ) :
    (siteAtOffset (y + siteOfCoords F.top m) w : F.Site F.depth) = siteAtOffset y (fun i => w i + (F.blockSide : ℤ) * m i) := by apply _root_.YangMills.Construction.BlockLocality.siteAtOffset_add_cell <;> assumption
theorem mem_cutBelow_cellBall_iff (hL : 2 ≤ F.blockSide) (hodd : Odd F.blockSide) (y : F.Cell) {x : F.Site F.depth} :
    x ∈ cutBelow F.depth (cellBall y 2) ↔ ∃ z, InTwoBlocks F.blockSide z ∧ x = siteAtOffset y z := by apply _root_.YangMills.Construction.BlockLocality.mem_cutBelow_cellBall_iff <;> assumption
theorem mem_lumpOf_self (hL : 2 ≤ F.blockSide) (hodd : Odd F.blockSide) (g : LumpGrid F.blockSide) (y : F.Cell) (z : Fin 4 → ℤ) :
    (siteAtOffset y z : F.Site F.depth) ∈ lumpOf g (siteAtOffset y z : F.Site F.depth) := by apply _root_.YangMills.Construction.BlockLocality.mem_lumpOf_self <;> assumption
omit [∀ j i, NeZero (F.period j i)] [∀ j i, NeZero (F'.period j i)] in
theorem mem_levelSites [∀ i, NeZero (F.period F.depth i)] (x : F.Site F.depth) : x ∈ levelSites F F.depth := by
  refine mem_boxSites_iff.mpr ⟨siteCoords x, fun i => ?_, _root_.YangMills.Construction.TorusContours.siteOfCoords_siteCoords x⟩
  have h1 : (0 : ℤ) ≤ siteCoords x i := by
    simp only [siteCoords]
    rw [ZMod.cast_eq_val]
    positivity
  have h2 : siteCoords x i < (F.period F.depth i : ℤ) := by
    simp only [siteCoords]
    rw [ZMod.cast_eq_val]
    exact_mod_cast ZMod.val_lt _
  simp only [Pi.zero_apply]
  omega
def cornerOffsets (μ ν : Fin 4) : List (Fin 4 → ℤ) :=
  [0, Pi.single μ 1, Pi.single ν 1, Pi.single μ 1 + Pi.single ν 1]
omit [∀ j i, NeZero (F.period j i)] [∀ j i, NeZero (F'.period j i)] in
theorem mem_plaquetteCorners_iff {p : F.Site F.depth × Fin 4 × Fin 4} {x : F.Site F.depth} :
    x ∈ plaquetteCorners p ↔ ∃ δ ∈ cornerOffsets p.2.1 p.2.2, x = p.1 + siteOfCoords F.depth δ := by apply _root_.YangMills.Construction.BlockLocality.mem_plaquetteCorners_iff <;> assumption
theorem cornerOffsets_bounds {μ ν : Fin 4} {δ : Fin 4 → ℤ} (h : δ ∈ cornerOffsets μ ν) (k : Fin 4) :
    -2 ≤ δ k ∧ δ k ≤ 2 := by apply _root_.YangMills.Construction.BlockLocality.cornerOffset_bound <;> assumption
theorem plaquetteDefect_eq_of_agree {R : ℕ} (X : F.GaugeField F.depth) (X' : F'.GaugeField F'.depth) (y : F.Cell) (y' : F'.Cell)
    (hag : ∀ (u : Fin 4 → ℤ) (i : Fin 4), OffsetInBox R u → OffsetInBox R (u + Pi.single i 1) →
      X (siteAtOffset y u) i = X' (siteAtOffset y' u) i) (μ ν : Fin 4) (u : Fin 4 → ℤ)
    (hu : ∀ k, |u k| + 2 ≤ (R : ℤ)) :
    plaquetteDefect X (siteAtOffset y u, μ, ν) = plaquetteDefect X' (siteAtOffset y' u, μ, ν) := by apply _root_.YangMills.Construction.BlockLocality.plaquetteDefect_congr <;> assumption
omit [∀ j i, NeZero (F'.period j i)] in
theorem exists_siteAtOffset (y : F.Cell) (x : F.Site F.depth) : ∃ w, x = siteAtOffset y w := by apply _root_.YangMills.Construction.BlockLocality.exists_siteAtOffset <;> assumption
theorem lumpBoxOf_inWindow {L : ℕ} (hL : 2 ^ 16 ≤ L) (hodd : Odd L) (g : LumpGrid L) {z : Fin 4 → ℤ} (hz : InTwoBlocks L z) :
    BoxInWindow L (lumpBoxOf g z) ∧ (∀ v, MemBox v (lumpBoxOf g z) → InTwoBlocks L v) := by apply _root_.YangMills.Construction.BlockLocality.lumpBox_inWindow <;> assumption
theorem lumpOf_mem_hotLumps_of_agree (hL : 2 ^ 16 ≤ F.blockSide) (hodd : Odd F.blockSide) (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ))
    (g : LumpGrid F.blockSide) (g' : LumpGrid F'.blockSide)
    (hg : ∀ z, (lumpBoxOf g z) = (lumpBoxOf g' z)) (s : ℝ) (X : F.GaugeField F.depth) (X' : F'.GaugeField F'.depth) (y : F.Cell)
    (y' : F'.Cell)
    (hag : ∀ (u : Fin 4 → ℤ) (i : Fin 4), OffsetInBox (3 * F.blockSide) u → OffsetInBox (3 * F.blockSide) (u + Pi.single i 1) →
      X (siteAtOffset y u) i = X' (siteAtOffset y' u) i) {z : Fin 4 → ℤ} (hz : InTwoBlocks F.blockSide z)
    (hin : lumpOf g (siteAtOffset y z : F.Site F.depth) ∈ hotLumps g s (levelSites F F.depth) X) :
    lumpOf g' (siteAtOffset y' z : F'.Site F'.depth) ∈ hotLumps g' s (levelSites F' F'.depth) X' := by
  classical
  have hL2 : 2 ≤ F.blockSide := by omega
  obtain ⟨⟨p₀, μ, ν⟩, hp, hl⟩ := Finset.mem_biUnion.mp hin
  obtain ⟨x, hx, hxl⟩ := Finset.mem_image.mp hl
  obtain ⟨hpc, hps⟩ := Finset.mem_filter.mp hp
  have hself : x ∈ lumpOf g (siteAtOffset y z : F.Site F.depth) := by
    rw [← hxl]
    obtain ⟨w, rfl⟩ := exists_siteAtOffset y x
    exact mem_lumpOf_self hL2 hodd g y w
  rw [lumpOf_siteAtOffset] at hself
  obtain ⟨v, hv, rfl⟩ := mem_boxAtOffset.mp hself
  obtain ⟨hzw, hzK⟩ := lumpBoxOf_inWindow hL hodd g hz
  have hvK := hzK v hv
  obtain ⟨hvw, -⟩ := lumpBoxOf_inWindow hL hodd g hvK
  have hrep : lumpBoxOf g v = lumpBoxOf g z := by
    refine boxAtOffset_injective hbig hL2 y hvw hzw ?_
    rw [← lumpOf_siteAtOffset, ← lumpOf_siteAtOffset]
    exact hxl
  obtain ⟨δ, hδ, hxδ⟩ := mem_plaquetteCorners_iff.mp hx
  simp only [] at hδ hxδ
  have hp₀ : p₀ = siteAtOffset y (v - δ) := by
    have : (siteAtOffset y (v - δ) : F.Site F.depth) = siteAtOffset y v - siteOfCoords F.depth δ := by
      simp only [siteAtOffset, sub_eq_add_neg, _root_.YangMills.Construction.TorusContours.siteOfCoords_add, _root_.YangMills.Construction.TorusContours.siteOfCoords_neg]
      abel
    rw [this, hxδ]
    abel
  subst hp₀
  have hbound : ∀ k, |(v - δ) k| + 2 ≤ ((3 * F.blockSide : ℕ) : ℤ) := by
    intro k
    have h1 := abs_le.mp (hvK k)
    have h2 := cornerOffsets_bounds hδ k
    have h3 : |(v - δ) k| ≤ 2 * (F.blockSide : ℤ) + ((F.blockSide : ℤ) - 1) / 2 + 2 := by
      simp only [Pi.sub_apply]
      rw [abs_le]
      omega
    push_cast
    omega
  have hcur := plaquetteDefect_eq_of_agree X X' y y' hag μ ν (v - δ) hbound
  have hmemP := Finset.mem_filter.mp hpc
  have hlt : μ < ν := hmemP.2.1
  have hx' : (siteAtOffset y' v : F'.Site F'.depth) ∈ plaquetteCorners (siteAtOffset y' (v - δ), μ, ν) := by
    refine mem_plaquetteCorners_iff.mpr ⟨δ, hδ, ?_⟩
    simp only [siteAtOffset, sub_eq_add_neg, _root_.YangMills.Construction.TorusContours.siteOfCoords_add, _root_.YangMills.Construction.TorusContours.siteOfCoords_neg]
    abel
  refine Finset.mem_biUnion.mpr ⟨(siteAtOffset y' (v - δ), μ, ν), Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
  · refine Finset.mem_filter.mpr ⟨?_, hlt, fun x _ => mem_levelSites x⟩
    exact Finset.mem_product.mpr ⟨mem_levelSites _, Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩
  · rw [← hcur]
    exact hps
  · refine Finset.mem_image.mpr ⟨_, hx', ?_⟩
    rw [lumpOf_siteAtOffset, lumpOf_siteAtOffset, ← hg v, ← hg z, hrep]
omit [∀ j i, NeZero (F.period j i)] [∀ j i, NeZero (F'.period j i)] in
theorem mem_nearbyLumps {h : Finset (Finset (F.Site F.depth))} {y : F.Cell} {l : Finset (F.Site F.depth)} :
    l ∈ nearbyLumps h y ↔ l ∈ h ∧ l ⊆ cutBelow F.depth (cellBall y 2) := by
  simp only [nearbyLumps, Finset.mem_filter]
theorem mem_nearbyLumps_iff (hL : 2 ≤ F.blockSide) (hodd : Odd F.blockSide) {h : Finset (Finset (F.Site F.depth))} {y : F.Cell}
    {l : Finset (F.Site F.depth)} :
    l ∈ nearbyLumps h y ↔ l ∈ h ∧ ∀ x ∈ l, ∃ z, InTwoBlocks F.blockSide z ∧ x = siteAtOffset y z := by apply _root_.YangMills.Construction.BlockLocality.mem_nearbyLumps_iff <;> assumption
theorem lumpOf_inTwoBlocks (hL : 2 ^ 16 ≤ F.blockSide) (hodd : Odd F.blockSide) (g : LumpGrid F.blockSide) (y : F.Cell) {z : Fin 4 → ℤ}
    (hz : InTwoBlocks F.blockSide z) : ∀ x ∈ lumpOf g (siteAtOffset y z : F.Site F.depth), ∃ v, InTwoBlocks F.blockSide v ∧ x = siteAtOffset y v := by apply _root_.YangMills.Construction.BlockLocality.lumpOf_in_nearBlocks <;> assumption
def twoBlockOffsets (L : ℕ) : Finset (Fin 4 → ℤ) := centredCube (2 * (2 * L + (L - 1) / 2) + 1)
theorem mem_twoBlockOffsets {L : ℕ} (hL : 1 ≤ L) {z : Fin 4 → ℤ} : z ∈ twoBlockOffsets L ↔ InTwoBlocks L z := by apply _root_.YangMills.Construction.BlockLocality.mem_nearBlockOffsets <;> assumption
theorem exists_lumpOf_of_mem_hotLumps {L : ℕ} {g : LumpGrid L} {s : ℝ} {j : ℕ} {X : Finset (F.Site j)} {W : F.GaugeField j}
    {l : Finset (F.Site j)} (hl : l ∈ hotLumps g s X W) : ∃ x : F.Site j, l = lumpOf g x := by apply _root_.YangMills.Construction.BlockLocality.exists_lumpOf_of_mem_hotLumps <;> assumption
theorem sameNearbyLumps_of_agree (hL : 2 ^ 16 ≤ F.blockSide) (hodd : Odd F.blockSide) (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ))
    (hbig' : ∀ i, 16 * (F'.blockSide : ℤ) ≤ (F'.period F'.depth i : ℤ)) (hLL : F'.blockSide = F.blockSide)
    (g : LumpGrid F.blockSide) (g' : LumpGrid F'.blockSide) (hg : ∀ z, (lumpBoxOf g z) = (lumpBoxOf g' z)) (s : ℝ)
    (X : F.GaugeField F.depth) (X' : F'.GaugeField F'.depth) (y : F.Cell) (y' : F'.Cell)
    (hag : ∀ (u : Fin 4 → ℤ) (i : Fin 4), OffsetInBox (3 * F.blockSide) u → OffsetInBox (3 * F.blockSide) (u + Pi.single i 1) →
      X (siteAtOffset y u) i = X' (siteAtOffset y' u) i) :
    SameNearbyLumps (hotLumps g s (levelSites F F.depth) X) (hotLumps g' s (levelSites F' F'.depth) X') y y' := by
  classical
  have hL2 : 2 ≤ F.blockSide := by omega
  have hL' : 2 ^ 16 ≤ F'.blockSide := by omega
  have hL2' : 2 ≤ F'.blockSide := by omega
  have hodd' : Odd F'.blockSide := hLL ▸ hodd
  have hag' : ∀ (u : Fin 4 → ℤ) (i : Fin 4), OffsetInBox (3 * F'.blockSide) u → OffsetInBox (3 * F'.blockSide) (u + Pi.single i 1) →
      X' (siteAtOffset y' u) i = X (siteAtOffset y u) i := by
    intro u i h1 h2
    rw [hLL] at h1 h2
    exact (hag u i h1 h2).symm
  have hKK : ∀ {z : Fin 4 → ℤ}, InTwoBlocks F.blockSide z → InTwoBlocks F'.blockSide z := fun h => by rwa [hLL]
  have hKK' : ∀ {z : Fin 4 → ℤ}, InTwoBlocks F'.blockSide z → InTwoBlocks F.blockSide z := fun h => by rwa [hLL] at h
  set h := hotLumps g s (levelSites F F.depth) X with hh
  set h' := hotLumps g' s (levelSites F' F'.depth) X' with hh'
  refine ⟨((twoBlockOffsets F.blockSide).filter fun z => lumpOf g (siteAtOffset y z : F.Site F.depth) ∈ h).image (lumpBoxOf g), ?_, ?_, ?_⟩
  · intro q hq i
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
    have hzK := (mem_twoBlockOffsets (by omega)).mp (Finset.mem_filter.mp hz).1
    obtain ⟨⟨hord, -, -⟩, hK⟩ := lumpBoxOf_inWindow hL hodd g hzK
    have h1 := abs_le.mp (hK _ (memBox_lower hord) i)
    have h2 := abs_le.mp (hK _ (memBox_upper hord) i)
    have h3 := lumpBoxOf_bounds (L := F.blockSide) (by omega) hodd g z i
    omega
  · ext l
    rw [mem_nearbyLumps_iff hL2 hodd, Finset.image_image, Finset.mem_image]
    constructor
    · rintro ⟨hlh, hsub⟩
      obtain ⟨x₀, rfl⟩ := exists_lumpOf_of_mem_hotLumps hlh
      obtain ⟨w, rfl⟩ := exists_siteAtOffset y x₀
      obtain ⟨z, hz, he⟩ := hsub _ (mem_lumpOf_self hL2 hodd g y w)
      have hlz : lumpOf g (siteAtOffset y w : F.Site F.depth) = lumpOf g (siteAtOffset y z : F.Site F.depth) := by rw [he]
      refine ⟨z, Finset.mem_filter.mpr ⟨(mem_twoBlockOffsets (by omega)).mpr hz, hlz ▸ hlh⟩, ?_⟩
      rw [Function.comp_apply, ← lumpOf_siteAtOffset, hlz]
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hzK, hin⟩ := Finset.mem_filter.mp hz
      rw [Function.comp_apply, ← lumpOf_siteAtOffset]
      exact ⟨hin, lumpOf_inTwoBlocks hL hodd g y ((mem_twoBlockOffsets (by omega)).mp hzK)⟩
  · ext l
    rw [mem_nearbyLumps_iff hL2' hodd', Finset.image_image, Finset.mem_image]
    constructor
    · rintro ⟨hlh, hsub⟩
      obtain ⟨x₀, rfl⟩ := exists_lumpOf_of_mem_hotLumps hlh
      obtain ⟨w, rfl⟩ := exists_siteAtOffset y' x₀
      obtain ⟨z, hz, he⟩ := hsub _ (mem_lumpOf_self hL2' hodd' g' y' w)
      have hlz : lumpOf g' (siteAtOffset y' w : F'.Site F'.depth) = lumpOf g' (siteAtOffset y' z : F'.Site F'.depth) := by rw [he]
      have hback := lumpOf_mem_hotLumps_of_agree hL' hodd' hbig' g' g (fun z => (hg z).symm) s X' X y' y hag' hz (hlz ▸ hlh)
      refine ⟨z, Finset.mem_filter.mpr ⟨(mem_twoBlockOffsets (by omega)).mpr (hKK' hz), hback⟩, ?_⟩
      rw [Function.comp_apply, hg z, ← lumpOf_siteAtOffset, hlz]
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hzK, hin⟩ := Finset.mem_filter.mp hz
      have hzI := (mem_twoBlockOffsets (by omega)).mp hzK
      rw [Function.comp_apply, hg z, ← lumpOf_siteAtOffset]
      exact ⟨lumpOf_mem_hotLumps_of_agree hL hodd hbig g g' hg s X X' y y' hag hzI hin, lumpOf_inTwoBlocks hL' hodd' g' y' (hKK hzI)⟩
end HotLumps
section FineLevel
variable {ℓ : StepParameters} {n n' : ℕ} [NeZero n] [NeZero n']
theorem fineLevelField_eq_of_agree {W : TorusField (n * ℓ.side)} {W' : TorusField (n' * ℓ.side)} {y : (stepBlockFrame ℓ.side n).Cell}
    {y' : (stepBlockFrame ℓ.side n').Cell} {m : ℕ}
    (h : FieldsAgreeNear W W' (cellCentreOnTorus ℓ.side y) (cellCentreOnTorus ℓ.side y') m) (u : Fin 4 → ℤ) (i : Fin 4)
    (h1 : OffsetInBox m u) (h2 : OffsetInBox m (u + Pi.single i 1)) :
    fineLevelField ℓ n W (siteAtOffset y u) i = fineLevelField ℓ n' W' (siteAtOffset y' u) i := by
  have e : ∀ {k : ℕ} [NeZero k] (y₁ : (stepBlockFrame ℓ.side k).Cell),
      toTorusSite (k * ℓ.side) (siteAtOffset y₁ u : (stepBlockFrame ℓ.side k).Site 0) = cellCentreOnTorus ℓ.side y₁ + siteOfInt u := by
    intro k _ y₁
    unfold siteAtOffset cellCentreOnTorus
    exact (toTorusSite_add (F := stepBlockFrame ℓ.side k) (j := 0) (m := k * ℓ.side) (fun i => stepBlockFrame_period_zero i) _ _).trans
      (congrArg _ (toTorusSite_siteOfCoords (F := stepBlockFrame ℓ.side k) (j := 0) (m := k * ℓ.side) (fun i => stepBlockFrame_period_zero i) u))
  have := h (u, i) ⟨h1, h2⟩
  show W (toTorusSite _ (siteAtOffset y u : (stepBlockFrame ℓ.side n).Site 0)) i =
    W' (toTorusSite _ (siteAtOffset y' u : (stepBlockFrame ℓ.side n').Site 0)) i
  rw [e, e]
  exact this
theorem period_stepBlockFrame_ge (L k : ℕ) [NeZero L] [NeZero k] (h : 16 ≤ k) (i : Fin 4) :
    16 * ((stepBlockFrame L k).blockSide : ℤ) ≤ ((stepBlockFrame L k).period (stepBlockFrame L k).depth i : ℤ) := by apply _root_.YangMills.Construction.BlockLocality.period_ge_stepBlockFrame <;> assumption
end FineLevel
end KernelLocality
namespace TorusLumps
open BlockAverages LumpContours TorusFields TorusContours KernelLocality
theorem bondKernelLocality : BondKernelLocality := by
  intro ℓ hfit hLam n n' _ _ h16 h16' W W' y y'
  have hL : 2 ^ 16 ≤ ℓ.side := hfit.L_ge
  have hodd : Odd ℓ.side := hfit.L_odd
  have hL2 : 2 ≤ ℓ.side := by omega
  have hbig := period_stepBlockFrame_ge ℓ.side n h16
  have hbig' := period_stepBlockFrame_ge ℓ.side n' h16'
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext b
    simp only [baseChoices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (isBaseChoice_iff (F := stepBlockFrame ℓ.side n) _ _ _).trans Fintype.mem_piFinset.symm
  · intro hag
    exact sameNearbyLumps_of_agree (F := stepBlockFrame ℓ.side n) (F' := stepBlockFrame ℓ.side n') hL hodd hbig hbig' rfl ℓ.grid ℓ.grid
      (fun _ => rfl) ℓ.threshold _ _ y y' (fun u i h1 h2 => fineLevelField_eq_of_agree hag u i h1 h2)
  · rintro ⟨Q, hQ, e, e'⟩
    obtain ⟨M, hM⟩ := exists_isMergeOf _ (Q.image collarBox) rfl (by
      classical
      intro r hr
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
      intro i
      have := hQ q hq i
      simp only [collarBox]
      omega)
    refine ⟨(card_baseSitesAt_eq (F := stepBlockFrame ℓ.side n) hbig hL hLam hQ hM e).trans
      (card_baseSitesAt_eq (F := stepBlockFrame ℓ.side n') hbig' hL hLam hQ hM e').symm, fun z hz => ?_⟩
    exact (siteAtOffset_mem_baseSitesAt_iff (F := stepBlockFrame ℓ.side n) hbig hL hLam hQ hM e hz).trans
      (siteAtOffset_mem_baseSitesAt_iff (F := stepBlockFrame ℓ.side n') hbig' hL hLam hQ hM e' hz).symm
  · intro i x V V' b b' z₀ z₁ h₀ h₁ hb₀ hb₀' hb₁ hb₁' hag hs₀ hs₁
    classical
    obtain ⟨Q₀, hQ₀, e₀, e₀'⟩ := hs₀
    obtain ⟨Q₁, hQ₁, e₁, e₁'⟩ := hs₁
    have hord : ∀ {Q : Finset OffsetBox}, LumpBoxFamily ℓ.side Q → ∀ r ∈ Q.image collarBox, BoxOrdered r := by
      intro Q hQ r hr
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
      intro i
      have := hQ q hq i
      simp only [collarBox]
      omega
    obtain ⟨M₀, hM₀⟩ := exists_isMergeOf _ (Q₀.image collarBox) rfl (hord hQ₀)
    obtain ⟨M₁, hM₁⟩ := exists_isMergeOf _ (Q₁.image collarBox) rfl (hord hQ₁)
    obtain ⟨c₀, -, r₀⟩ := excludedBoxes_of_family (F := stepBlockFrame ℓ.side n) hbig hL hLam hQ₀ hM₀ e₀
    obtain ⟨c₀', -, r₀'⟩ := excludedBoxes_of_family (F := stepBlockFrame ℓ.side n') hbig' hL hLam hQ₀ hM₀ e₀'
    obtain ⟨c₁, -, r₁⟩ := excludedBoxes_of_family (F := stepBlockFrame ℓ.side n) hbig hL hLam hQ₁ hM₁ e₁
    obtain ⟨c₁', -, r₁'⟩ := excludedBoxes_of_family (F := stepBlockFrame ℓ.side n') hbig' hL hLam hQ₁ hM₁ e₁'
    have hw : ∀ {Q M : Finset OffsetBox}, LumpBoxFamily ℓ.side Q → IsMergeOf (Q.image collarBox) M →
        ∀ q ∈ (if ℓ.baseDepth ≤ Q.card then ∅ else M), BoxInWindow ℓ.side q := by
      intro Q M hQ hM q hq
      split_ifs at hq
      · simp at hq
      · exact boxInWindow_of_merge hL hQ hM hq
    have hmean : contourMean ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ n W)) b (fineLevelField ℓ n W) (y, i) =
        contourMean ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ n' W')) b' (fineLevelField ℓ n' W') (y', i) := by
      refine (contourMean_eq (F := stepBlockFrame ℓ.side n) hbig hL2 h₀ h₁ hb₀ hb₁ (hw hQ₀ hM₀) (hw hQ₁ hM₁) r₀ r₁ c₀ c₁ _).trans
        (Eq.trans ?_ (contourMean_eq (F := stepBlockFrame ℓ.side n') hbig' hL2 h₀ h₁ hb₀' hb₁' (hw hQ₀ hM₀) (hw hQ₁ hM₁)
          r₀' r₁' c₀' c₁' _).symm)
      refine congrArg _ (Finset.sum_congr rfl fun e he => ?_)
      exact congrArg Subtype.val (pathHolonomy_eq_of_agree (F := stepBlockFrame ℓ.side n) (F' := stepBlockFrame ℓ.side n') _ _ y y'
        (fun u k h1 h2 => fineLevelField_eq_of_agree hag u k h1 h2) _ z₀
        (contourOffsetPath_inBox h₀ h₁ (mem_centredCube_of_mem_usedOffsetContours _ _ _ _ _ _ _ _ he) e.2 i))
    refine ⟨hmean, fun hV => ?_⟩
    rw [bondKernel_eq_meanKernel, bondKernel_eq_meanKernel]
    exact congrArg₂ (meanKernel (ℓ.coupling * x)) hmean hV
end TorusLumps
end YangMills.Construction
end
