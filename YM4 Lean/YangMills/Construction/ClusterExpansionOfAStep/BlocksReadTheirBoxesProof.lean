import YangMills.Construction.ColdChainAtEveryLevel.MeansOfAPotential
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ClusterExpansionOfAStep.BlocksReadTheirBoxes
import YangMills.Construction.ClusterExpansionOfAStep.ContoursFromBases
import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockLocality
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.TorusLumps
open YangMills.Construction.TorusFields hiding unitStep supDist gaugeTransform
section Merge
def BoxesNear (q q' : OffsetBox) : Prop := ∀ i, q.1 i ≤ q'.2 i + 2 ∧ q'.1 i ≤ q.2 i + 2
def BoxSubset (q q' : OffsetBox) : Prop := ∀ i, q'.1 i ≤ q.1 i ∧ q.2 i ≤ q'.2 i
def boxHull (q q' : OffsetBox) : OffsetBox := (fun i => min (q.1 i) (q'.1 i), fun i => max (q.2 i) (q'.2 i))
def boxWidth (q : OffsetBox) (i : Fin 4) : ℤ := q.2 i - q.1 i + 1
def BoxOrdered (q : OffsetBox) : Prop := ∀ i, q.1 i ≤ q.2 i
structure MergedFamily (R M : Finset OffsetBox) : Prop where
  ordered : ∀ q ∈ M, BoxOrdered q
  covers : ∀ q ∈ R, ∃ q' ∈ M, BoxSubset q q'
  separated : ∀ q ∈ M, ∀ q' ∈ M, q ≠ q' → ¬ BoxesNear q q'
  width_sum_le : ∀ i, ∑ q ∈ M, (boxWidth q i + 2) ≤ ∑ q ∈ R, (boxWidth q i + 2)
  bounded : ∀ A B : Fin 4 → ℤ, (∀ q ∈ R, ∀ i, A i ≤ q.1 i ∧ q.2 i ≤ B i) → ∀ q ∈ M, ∀ i, A i ≤ q.1 i ∧ q.2 i ≤ B i
  exists_of_closed : ∀ {α : Type} (In : OffsetBox → α → Prop), (∀ q ∈ R, ∃ a, In q a) →
    (∀ q q' a a', BoxOrdered q → BoxOrdered q' → BoxesNear q q' → In q a → In q' a' → a = a') →
    (∀ q q' a, BoxOrdered q → BoxOrdered q' → BoxesNear q q' → In q a → In q' a → In (boxHull q q') a) →
    ∀ q ∈ M, ∃ a, In q a
theorem exists_mergedFamily : ∀ (N : ℕ) (R : Finset OffsetBox), R.card = N → (∀ q ∈ R, BoxOrdered q) →
    ∃ M, MergedFamily R M := by
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
        refine (hM.width_sum_le i).trans ?_
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
        refine hM.bounded A B ?_
        intro p hp i
        rcases Finset.mem_insert.mp hp with rfl | hp
        · have h1 := hAB q hq i
          have h2 := hAB q' hq' i
          simp only [boxHull]
          omega
        · exact hAB p (hER p hp) i
      · intro α In h1 h2 h3
        refine hM.exists_of_closed In ?_ h2 h3
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
end Merge
section Window
variable {F : BlockFrame} [∀ j i, NeZero (F.period j i)]
def OffsetWindow (L : ℕ) (u : Fin 4 → ℤ) : Prop := ∀ i, -(7 * (L : ℤ)) ≤ u i ∧ u i ≤ 7 * (L : ℤ)
def BoxInWindow (L : ℕ) (q : OffsetBox) : Prop := BoxOrdered q ∧ OffsetWindow L q.1 ∧ OffsetWindow L q.2
def InOffsetBox (u : Fin 4 → ℤ) (q : OffsetBox) : Prop := ∀ i, q.1 i ≤ u i ∧ u i ≤ q.2 i
omit [∀ j i, NeZero (F.period j i)] in
theorem siteAtOffset_apply (y : F.Cell) (u : Fin 4 → ℤ) (i : Fin 4) :
    (siteAtOffset y u : F.Site F.depth) i =
      (((F.blockSide : ℤ) * siteCoords y i + u i : ℤ) : ZMod (F.period F.depth i)) := by
  rw [TorusContours.siteAtOffset_eq]
  rfl
omit [∀ j i, NeZero (F.period j i)] in
theorem siteAtOffset_sub_apply (y : F.Cell) (u v : Fin 4 → ℤ) (i : Fin 4) :
    (siteAtOffset y u : F.Site F.depth) i - (siteAtOffset y v : F.Site F.depth) i =
      ((u i - v i : ℤ) : ZMod (F.period F.depth i)) := by
  rw [siteAtOffset_apply, siteAtOffset_apply]
  push_cast
  ring
theorem siteAtOffset_apply_eq_iff (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (y : F.Cell)
    {u v : Fin 4 → ℤ} {i : Fin 4} (h : |u i - v i| ≤ 14 * (F.blockSide : ℤ)) (hL : 2 ≤ F.blockSide) :
    (siteAtOffset y u : F.Site F.depth) i = (siteAtOffset y v : F.Site F.depth) i ↔ u i = v i := by
  constructor
  · intro he
    have h1 : ((u i - v i : ℤ) : ZMod (F.period F.depth i)) = 0 := by
      rw [← siteAtOffset_sub_apply, he, sub_self]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    have h2 : |u i - v i| < (F.period F.depth i : ℤ) := by
      have := hbig i
      have : (2 : ℤ) ≤ F.blockSide := by exact_mod_cast hL
      omega
    have := Int.eq_zero_of_abs_lt_dvd h1 h2
    omega
  · intro he
    rw [siteAtOffset_apply, siteAtOffset_apply, he]
theorem abs_sub_le_of_window {L : ℕ} {u v : Fin 4 → ℤ} (hu : OffsetWindow L u) (hv : OffsetWindow L v) (i : Fin 4) :
    |u i - v i| ≤ 14 * (L : ℤ) := by
  have h1 := hu i
  have h2 := hv i
  rw [abs_le]
  omega
theorem siteAtOffset_eq_iff (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (hL : 2 ≤ F.blockSide)
    (y : F.Cell) {u v : Fin 4 → ℤ} (hu : OffsetWindow F.blockSide u) (hv : OffsetWindow F.blockSide v) :
    (siteAtOffset y u : F.Site F.depth) = siteAtOffset y v ↔ u = v := by
  constructor
  · intro he
    funext i
    exact (siteAtOffset_apply_eq_iff hbig y (abs_sub_le_of_window hu hv i) hL).mp (congrFun he i)
  · rintro rfl
    rfl
omit [∀ j i, NeZero (F.period j i)] in
theorem mem_boxAtOffset {y : F.Cell} {q : OffsetBox} {x : F.Site F.depth} :
    x ∈ boxAtOffset y q ↔ ∃ v, InOffsetBox v q ∧ x = siteAtOffset y v := by
  simp only [boxAtOffset, boxSites, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
theorem window_of_mem_box {L : ℕ} {q : OffsetBox} (hq : BoxInWindow L q) {v : Fin 4 → ℤ}
    (hv : InOffsetBox v q) : OffsetWindow L v := by
  intro i
  have h1 := hq.2.1 i
  have h2 := hq.2.2 i
  have h3 := hv i
  omega
theorem siteAtOffset_mem_boxAtOffset_iff (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ))
    (hL : 2 ≤ F.blockSide) (y : F.Cell) {u : Fin 4 → ℤ} {q : OffsetBox} (hu : OffsetWindow F.blockSide u)
    (hq : BoxInWindow F.blockSide q) :
    siteAtOffset y u ∈ boxAtOffset y q ↔ InOffsetBox u q := by
  rw [mem_boxAtOffset]
  constructor
  · rintro ⟨v, hv, he⟩
    rwa [(siteAtOffset_eq_iff hbig hL y hu (window_of_mem_box hq hv)).mp he]
  · intro h
    exact ⟨u, h, rfl⟩
theorem lower_mem_box {q : OffsetBox} (hq : BoxOrdered q) : InOffsetBox q.1 q := fun i => ⟨le_rfl, hq i⟩
theorem upper_mem_box {q : OffsetBox} (hq : BoxOrdered q) : InOffsetBox q.2 q := fun i => ⟨hq i, le_rfl⟩
theorem boxAtOffset_injective (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ)) (hL : 2 ≤ F.blockSide)
    (y : F.Cell) {q q' : OffsetBox} (hq : BoxInWindow F.blockSide q) (hq' : BoxInWindow F.blockSide q')
    (h : boxAtOffset y q = boxAtOffset y q') : q = q' := by
  have h1 : InOffsetBox q.1 q' := (siteAtOffset_mem_boxAtOffset_iff hbig hL y hq.2.1 hq').mp
    (h ▸ (siteAtOffset_mem_boxAtOffset_iff hbig hL y hq.2.1 hq).mpr (lower_mem_box hq.1))
  have h2 : InOffsetBox q.2 q' := (siteAtOffset_mem_boxAtOffset_iff hbig hL y hq.2.2 hq').mp
    (h ▸ (siteAtOffset_mem_boxAtOffset_iff hbig hL y hq.2.2 hq).mpr (upper_mem_box hq.1))
  have h3 : InOffsetBox q'.1 q := (siteAtOffset_mem_boxAtOffset_iff hbig hL y hq'.2.1 hq).mp
    (h.symm ▸ (siteAtOffset_mem_boxAtOffset_iff hbig hL y hq'.2.1 hq').mpr (lower_mem_box hq'.1))
  have h4 : InOffsetBox q'.2 q := (siteAtOffset_mem_boxAtOffset_iff hbig hL y hq'.2.2 hq).mp
    (h.symm ▸ (siteAtOffset_mem_boxAtOffset_iff hbig hL y hq'.2.2 hq').mpr (upper_mem_box hq'.1))
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact le_antisymm (h3 i).1 (h1 i).1
  · exact le_antisymm (h2 i).2 (h4 i).2
theorem valMinAbs_intCast_of_small {p : ℕ} [NeZero p] {z : ℤ} (h : 2 * |z| < (p : ℤ)) :
    ((z : ZMod p)).valMinAbs = z := by apply _root_.YangMills.SharedProofs.p9640 <;> assumption
theorem valMinAbs_siteAtOffset_sub (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ))
    (hL : 2 ≤ F.blockSide) (y : F.Cell) {u v : Fin 4 → ℤ} (hu : OffsetWindow F.blockSide u)
    (hv : OffsetWindow F.blockSide v) (i : Fin 4) (hs : |u i - v i| ≤ 7 * (F.blockSide : ℤ)) :
    (((siteAtOffset y u : F.Site F.depth) i - (siteAtOffset y v : F.Site F.depth) i).valMinAbs) = u i - v i := by
  rw [siteAtOffset_sub_apply]
  refine valMinAbs_intCast_of_small ?_
  have := hbig i
  have : (2 : ℤ) ≤ F.blockSide := by exact_mod_cast hL
  omega
theorem areWithin_of_boxesNear (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ))
    (hL : 2 ≤ F.blockSide) (y : F.Cell) {q q' : OffsetBox} (hq : BoxInWindow F.blockSide q)
    (hq' : BoxInWindow F.blockSide q') (hn : BoxesNear q q') :
    AreWithin 2 (boxAtOffset y q) (boxAtOffset y q') := by
  have hp : ∀ i, ∃ a b : ℤ, (q.1 i ≤ a ∧ a ≤ q.2 i) ∧ (q'.1 i ≤ b ∧ b ≤ q'.2 i) ∧ |a - b| ≤ 2 := by
    intro i
    have h1 := hq.1 i
    have h2 := hq'.1 i
    have h3 := hn i
    by_cases c1 : q.2 i < q'.1 i
    · refine ⟨q.2 i, q'.1 i, ⟨h1, le_rfl⟩, ⟨le_rfl, h2⟩, ?_⟩
      rw [abs_le]
      omega
    by_cases c2 : q'.2 i < q.1 i
    · refine ⟨q.1 i, q'.2 i, ⟨le_rfl, h1⟩, ⟨h2, le_rfl⟩, ?_⟩
      rw [abs_le]
      omega
    refine ⟨max (q.1 i) (q'.1 i), max (q.1 i) (q'.1 i), ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by simp⟩
  choose a b ha hb hab using hp
  have hua : InOffsetBox a q := ha
  have hub : InOffsetBox b q' := hb
  refine ⟨siteAtOffset y a, mem_boxAtOffset.mpr ⟨a, hua, rfl⟩, siteAtOffset y b, mem_boxAtOffset.mpr ⟨b, hub, rfl⟩, ?_⟩
  refine Finset.sup_le fun i _ => ?_
  rw [valMinAbs_siteAtOffset_sub hbig hL y (window_of_mem_box hq hua) (window_of_mem_box hq' hub) i
    ((hab i).trans (by omega))]
  have := abs_le.mp (hab i)
  omega
theorem boxesNear_of_areWithin (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ))
    (hL : 2 ≤ F.blockSide) (y : F.Cell) {q q' : OffsetBox} (hq : BoxInWindow F.blockSide q)
    (hq' : BoxInWindow F.blockSide q') (hw : AreWithin 2 (boxAtOffset y q) (boxAtOffset y q')) :
    BoxesNear q q' := by
  obtain ⟨x, hx, x', hx', hd⟩ := hw
  obtain ⟨u, hu, rfl⟩ := mem_boxAtOffset.mp hx
  obtain ⟨v, hv, rfl⟩ := mem_boxAtOffset.mp hx'
  have hc : ∀ i, |u i - v i| ≤ 2 := by
    intro i
    have h1 : (((siteAtOffset y u : F.Site F.depth) i - (siteAtOffset y v : F.Site F.depth) i).valMinAbs).natAbs ≤ 2 :=
      (Finset.le_sup (f := fun i => (((siteAtOffset y u : F.Site F.depth) i -
        (siteAtOffset y v : F.Site F.depth) i).valMinAbs).natAbs) (Finset.mem_univ i)).trans hd
    set e := ((siteAtOffset y u : F.Site F.depth) i - (siteAtOffset y v : F.Site F.depth) i).valMinAbs with he
    have h2 : ((e : ℤ) : ZMod (F.period F.depth i)) = ((u i - v i : ℤ) : ZMod (F.period F.depth i)) := by
      rw [he, ZMod.coe_valMinAbs, siteAtOffset_sub_apply]
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h2
    have h3 : |u i - v i - e| < (F.period F.depth i : ℤ) := by
      have h4 := abs_sub_le_of_window (window_of_mem_box hq hu) (window_of_mem_box hq' hv) i
      have h5 := hbig i
      rw [abs_le] at h4
      rw [abs_lt]
      omega
    have h6 := Int.eq_zero_of_abs_lt_dvd h2 h3
    rw [abs_le]
    omega
  intro i
  have h1 := hu i
  have h2 := hv i
  have h3 := abs_le.mp (hc i)
  constructor <;> omega
omit [∀ j i, NeZero (F.period j i)] in
theorem mem_boxSites_iff {j : ℕ} {lo hi : Fin 4 → ℤ} {x : F.Site j} :
    x ∈ boxSites j lo hi ↔ ∃ c : Fin 4 → ℤ, (∀ i, lo i ≤ c i ∧ c i ≤ hi i) ∧ siteOfCoords j c = x := by
  simp [boxSites, Fintype.mem_piFinset]
theorem boxAtOffset_boxHull_subset (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ))
    (hL : 2 ≤ F.blockSide) (y : F.Cell) {q q' : OffsetBox} (hq : BoxInWindow F.blockSide q)
    (hq' : BoxInWindow F.blockSide q') {lo hi : Fin 4 → ℤ}
    (hlo : ∀ i, lo i ≤ hi i ∧ hi i - lo i + 1 < F.blockSide)
    (h1 : boxAtOffset y q ⊆ boxSites F.depth lo hi) (h2 : boxAtOffset y q' ⊆ boxSites F.depth lo hi) :
    boxAtOffset y (boxHull q q') ⊆ boxSites F.depth lo hi := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := mem_boxAtOffset.mp hx
  have hin : ∀ P : Fin 4 → ℤ, (InOffsetBox P q ∨ InOffsetBox P q') → ∃ c : Fin 4 → ℤ,
      (∀ i, lo i ≤ c i ∧ c i ≤ hi i) ∧ siteOfCoords F.depth c = (siteAtOffset y P : F.Site F.depth) := by
    intro P hP
    rcases hP with hP | hP
    · exact mem_boxSites_iff.mp (h1 (mem_boxAtOffset.mpr ⟨P, hP, rfl⟩))
    · exact mem_boxSites_iff.mp (h2 (mem_boxAtOffset.mpr ⟨P, hP, rfl⟩))
  have hco : ∀ i, ∃ ci : ℤ, (lo i ≤ ci ∧ ci ≤ hi i) ∧
      ((ci : ℤ) : ZMod (F.period F.depth i)) = (siteAtOffset y v : F.Site F.depth) i := by
    intro i
    have hA : ∃ P : Fin 4 → ℤ, (InOffsetBox P q ∨ InOffsetBox P q') ∧ P i = min (q.1 i) (q'.1 i) ∧
        OffsetWindow F.blockSide P := by
      by_cases c : q.1 i ≤ q'.1 i
      · exact ⟨q.1, Or.inl (lower_mem_box hq.1), by simp [c], hq.2.1⟩
      · exact ⟨q'.1, Or.inr (lower_mem_box hq'.1), by simp [le_of_not_ge c], hq'.2.1⟩
    have hB : ∃ P : Fin 4 → ℤ, (InOffsetBox P q ∨ InOffsetBox P q') ∧ P i = max (q.2 i) (q'.2 i) ∧
        OffsetWindow F.blockSide P := by
      by_cases c : q.2 i ≤ q'.2 i
      · exact ⟨q'.2, Or.inr (upper_mem_box hq'.1), by simp [c], hq'.2.2⟩
      · exact ⟨q.2, Or.inl (upper_mem_box hq.1), by simp [le_of_not_ge c], hq.2.2⟩
    obtain ⟨P₁, hP₁, e₁, w₁⟩ := hA
    obtain ⟨P₂, hP₂, e₂, w₂⟩ := hB
    obtain ⟨c₁, hc₁, t₁⟩ := hin P₁ hP₁
    obtain ⟨c₂, hc₂, t₂⟩ := hin P₂ hP₂
    have t₁' : ((c₁ i : ℤ) : ZMod (F.period F.depth i)) = (siteAtOffset y P₁ : F.Site F.depth) i := congrFun t₁ i
    have t₂' : ((c₂ i : ℤ) : ZMod (F.period F.depth i)) = (siteAtOffset y P₂ : F.Site F.depth) i := congrFun t₂ i
    have hv1 := (hv i).1
    have hv2 := (hv i).2
    simp only [boxHull] at hv1 hv2
    have hdiff : c₂ i - c₁ i = P₂ i - P₁ i := by
      have h3 : (((c₂ i - c₁ i : ℤ)) : ZMod (F.period F.depth i)) = ((P₂ i - P₁ i : ℤ) : ZMod (F.period F.depth i)) := by
        rw [← siteAtOffset_sub_apply y P₂ P₁ i, ← t₁', ← t₂']
        push_cast
        ring
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h3
      have h4 : |P₂ i - P₁ i - (c₂ i - c₁ i)| < (F.period F.depth i : ℤ) := by
        have h5 := abs_le.mp (abs_sub_le_of_window w₂ w₁ i)
        have h6 := hbig i
        have h7 := hc₁ i
        have h8 := hc₂ i
        have h9 := hlo i
        rw [abs_lt]
        omega
      have := Int.eq_zero_of_abs_lt_dvd h3 h4
      omega
    refine ⟨c₁ i + (v i - P₁ i), ?_, ?_⟩
    · have h7 := hc₁ i
      have h8 := hc₂ i
      omega
    · have h10 : (siteAtOffset y v : F.Site F.depth) i - (siteAtOffset y P₁ : F.Site F.depth) i =
          ((v i - P₁ i : ℤ) : ZMod (F.period F.depth i)) := siteAtOffset_sub_apply y v P₁ i
      push_cast at h10 ⊢
      rw [t₁', ← h10]
      ring
  choose c hc₁ hc₂ using hco
  refine mem_boxSites_iff.mpr ⟨c, hc₁, ?_⟩
  funext i
  exact hc₂ i
omit [∀ j i, NeZero (F.period j i)] in
theorem boxAtOffset_eq_boxSites (y : F.Cell) (q : OffsetBox) :
    (boxAtOffset y q : Finset (F.Site F.depth)) =
      boxSites F.depth (fun i => (F.blockSide : ℤ) * siteCoords y i + q.1 i)
        (fun i => (F.blockSide : ℤ) * siteCoords y i + q.2 i) := by
  ext x
  rw [mem_boxAtOffset, mem_boxSites_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨fun i => (F.blockSide : ℤ) * siteCoords y i + v i, fun i => ?_, (TorusContours.siteAtOffset_eq y v).symm⟩
    have := hv i
    constructor <;> dsimp only <;> omega
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun i => c i - (F.blockSide : ℤ) * siteCoords y i, fun i => ?_, ?_⟩
    · have := hc i
      constructor <;> simp only <;> omega
    · rw [TorusContours.siteAtOffset_eq]
      congr 1
      funext i
      ring
omit [∀ j i, NeZero (F.period j i)] in
theorem leastCover_subset {j : ℕ} {seeds Z₁ Z₂ : Finset (Finset (F.Site j))}
    (h₁ : IsLeastSeparatedCover seeds Z₁) (h₂ : IsLeastSeparatedCover seeds Z₂) : Z₁ ⊆ Z₂ := by
  intro B hB
  obtain ⟨B', hB', hs⟩ := h₁.2 Z₂ h₂.1 B hB
  obtain ⟨B'', hB'', hs'⟩ := h₂.2 Z₁ h₁.1 B' hB'
  have hne : B = B'' := by
    by_contra hne
    obtain ⟨lo, hi, hb, rfl⟩ := h₁.1.1 B hB
    have hx : (siteOfCoords j lo : F.Site j) ∈ boxSites j lo hi :=
      mem_boxSites_iff.mpr ⟨lo, fun i => ⟨le_rfl, (hb i).1⟩, rfl⟩
    refine h₁.1.2.2 _ hB _ hB'' hne ⟨_, hx, _, hs' (hs hx), ?_⟩
    simp [supDist]
  subst hne
  have : B = B' := Finset.Subset.antisymm hs hs'
  rwa [this]
omit [∀ j i, NeZero (F.period j i)] in
theorem mergedBoxes_eq_of_isLeast {j : ℕ} {seeds Z : Finset (Finset (F.Site j))}
    (h : IsLeastSeparatedCover seeds Z) : mergedBoxes seeds = Z := by
  classical
  have hex : ∃ Z, IsLeastSeparatedCover seeds Z := ⟨Z, h⟩
  unfold mergedBoxes
  rw [dif_pos hex]
  exact Finset.Subset.antisymm (leastCover_subset hex.choose_spec h) (leastCover_subset h hex.choose_spec)
theorem mergedBoxes_image_eq (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ))
    (hL : 2 ≤ F.blockSide) (y : F.Cell) {R M : Finset OffsetBox} (hM : MergedFamily R M)
    (hR : ∀ q ∈ R, BoxInWindow F.blockSide q) (hMw : ∀ q ∈ M, BoxInWindow F.blockSide q)
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
    have hB₂ : ∀ (p p' : OffsetBox) (a a' : Finset (F.Site F.depth)), BoxOrdered p → BoxOrdered p' →
        BoxesNear p p' → (BoxInWindow F.blockSide p ∧ a ∈ Z' ∧ boxAtOffset y p ⊆ a) →
        (BoxInWindow F.blockSide p' ∧ a' ∈ Z' ∧ boxAtOffset y p' ⊆ a') → a = a' := by
      rintro p p' a a' - - hn ⟨hw, ha, hs₁⟩ ⟨hw', ha', hs₂⟩
      by_contra hne
      obtain ⟨x, hx, x', hx', hd⟩ := areWithin_of_boxesNear hbig hL y hw hw' hn
      exact hZ'.2.2 a ha a' ha' hne ⟨x, hs₁ hx, x', hs₂ hx', hd⟩
    have hC : ∀ (p p' : OffsetBox) (a : Finset (F.Site F.depth)), BoxOrdered p → BoxOrdered p' →
        BoxesNear p p' → (BoxInWindow F.blockSide p ∧ a ∈ Z' ∧ boxAtOffset y p ⊆ a) →
        (BoxInWindow F.blockSide p' ∧ a ∈ Z' ∧ boxAtOffset y p' ⊆ a) →
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
    obtain ⟨a, ha⟩ := hM.exists_of_closed (fun (p : OffsetBox) (a : Finset (F.Site F.depth)) =>
      BoxInWindow F.blockSide p ∧ a ∈ Z' ∧ boxAtOffset y p ⊆ a) hA hB₂ hC q hq
    exact ⟨a, ha.2.1, ha.2.2⟩
def collarBox (q : OffsetBox) : OffsetBox := (fun i => q.1 i - 4098, fun i => q.2 i + 4098)
omit [∀ j i, NeZero (F.period j i)] in
theorem mem_centredCube_odd_iff {m : ℕ} {z : Fin 4 → ℤ} :
    z ∈ centredCube (2 * m + 1) ↔ ∀ i, -(m : ℤ) ≤ z i ∧ z i ≤ m := by apply _root_.YangMills.Construction.PotentialMeans.mem_centredCube_odd_iff <;> assumption
omit [∀ j i, NeZero (F.period j i)] in
theorem thicken_boxAtOffset (m : ℕ) (y : F.Cell) {q : OffsetBox} (hq : BoxOrdered q) :
    thicken m (boxAtOffset y q) = boxAtOffset y (fun i => q.1 i - m, fun i => q.2 i + m) := by
  ext x
  simp only [thicken, Finset.mem_biUnion, Finset.mem_image]
  rw [mem_boxAtOffset]
  constructor
  · rintro ⟨x₀, hx₀, h, hh, rfl⟩
    obtain ⟨v, hv, rfl⟩ := mem_boxAtOffset.mp hx₀
    refine ⟨v + h, fun i => ?_, ?_⟩
    · have h1 := mem_centredCube_odd_iff.mp hh i
      have h2 := hv i
      simp only [Pi.add_apply]
      omega
    · simp only [siteAtOffset, TorusContours.siteOfCoords_add, add_assoc]
  · rintro ⟨u, hu, rfl⟩
    let v : Fin 4 → ℤ := fun i => max (q.1 i) (min (u i) (q.2 i))
    have hv : InOffsetBox v q := fun i => by
      have := hq i
      simp only [v]
      omega
    refine ⟨siteAtOffset y v, mem_boxAtOffset.mpr ⟨v, hv, rfl⟩, u - v, ?_, ?_⟩
    · rw [mem_centredCube_odd_iff]
      intro i
      have h1 := hu i
      have h2 := hq i
      simp only at h1
      simp only [v, Pi.sub_apply]
      omega
    · simp only [siteAtOffset, add_assoc, ← TorusContours.siteOfCoords_add]
      congr 2
      abel
omit [∀ j i, NeZero (F.period j i)] in
theorem lumpCollar_boxAtOffset (y : F.Cell) {q : OffsetBox} (hq : BoxOrdered q) :
    lumpCollar (boxAtOffset y q) = boxAtOffset y (collarBox q) := by
  have hw : ((lumpRange + 2 : ℕ) : ℤ) = 4098 := by norm_num [lumpRange]
  unfold lumpCollar
  rw [thicken_boxAtOffset _ y hq, hw]
  rfl
def NearbyLumpBoxes (L : ℕ) (Q : Finset OffsetBox) : Prop :=
  ∀ q ∈ Q, ∀ i, -(3 * (L : ℤ)) ≤ q.1 i ∧ q.1 i ≤ q.2 i ∧ q.2 i ≤ 3 * (L : ℤ) ∧ q.2 i - q.1 i + 1 < 2 ^ 15
theorem lumpBoxes_inWindow {L : ℕ} {Q : Finset OffsetBox} (hQ : NearbyLumpBoxes L Q) {q : OffsetBox}
    (hq : q ∈ Q) : BoxInWindow L q := by
  refine ⟨fun i => (hQ q hq i).2.1, fun i => ?_, fun i => ?_⟩ <;> have := hQ q hq i <;> omega
theorem collarBox_inWindow {L : ℕ} (hL : 2 ^ 16 ≤ L) {Q : Finset OffsetBox} (hQ : NearbyLumpBoxes L Q)
    {r : OffsetBox} (hr : r ∈ Q.image collarBox) : BoxInWindow L r := by
  classical
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;> have := hQ q hq i <;> simp only [collarBox] <;> omega
theorem merged_inWindow {L : ℕ} (hL : 2 ^ 16 ≤ L) {Q M : Finset OffsetBox} (hQ : NearbyLumpBoxes L Q)
    (hM : MergedFamily (Q.image collarBox) M) {q : OffsetBox} (hq : q ∈ M) : BoxInWindow L q := by
  have hw := hM.bounded (fun _ => -(7 * (L : ℤ))) (fun _ => 7 * (L : ℤ)) (fun r hr i => by
    have h := collarBox_inWindow hL hQ hr
    exact ⟨(h.2.1 i).1, (h.2.2 i).2⟩) q hq
  have ho := hM.ordered q hq
  refine ⟨ho, fun i => ?_, fun i => ?_⟩ <;> have := hw i <;> have := ho i <;> omega
theorem merged_width_lt {L J₀ : ℕ} (hLam : 11 * 2 ^ 12 * J₀ < L) {Q M : Finset OffsetBox}
    (hQ : NearbyLumpBoxes L Q) (hM : MergedFamily (Q.image collarBox) M) (hc : Q.card < J₀) {q : OffsetBox}
    (hq : q ∈ M) (i : Fin 4) : boxWidth q i < L := by
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
  have h5 := hM.width_sum_le i
  have h6 : ((11 * 2 ^ 12 * J₀ : ℕ) : ℤ) < L := by exact_mod_cast hLam
  push_cast at h6
  nlinarith
theorem excludedBoxes_of_lumpBoxes (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ))
    (hL : 2 ^ 16 ≤ F.blockSide) {J₀ : ℕ} (hLam : 11 * 2 ^ 12 * J₀ < F.blockSide) {Q M : Finset OffsetBox}
    (hQ : NearbyLumpBoxes F.blockSide Q) (hM : MergedFamily (Q.image collarBox) M)
    {h : Finset (Finset (F.Site F.depth))} {y : F.Cell}
    (hb : nearbyLumps h y = Q.image (boxAtOffset y)) :
    (IsCrowded J₀ h y ↔ J₀ ≤ Q.card) ∧ (nearbyLumps h y = ∅ ↔ Q = ∅) ∧
      excludedBoxes J₀ h y = (open Classical in if J₀ ≤ Q.card then ∅ else M).image (boxAtOffset y) := by
  classical
  have hL2 : 2 ≤ F.blockSide := by omega
  have hcard : (nearbyLumps h y).card = Q.card := by
    rw [hb]
    exact Finset.card_image_of_injOn fun q hq q' hq' he =>
      boxAtOffset_injective hbig hL2 y (lumpBoxes_inWindow hQ hq) (lumpBoxes_inWindow hQ hq') he
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
      exact mergedBoxes_image_eq hbig hL2 y hM (fun r hr => collarBox_inWindow hL hQ hr)
        (fun q hq => merged_inWindow hL hQ hM hq)
        (fun q hq i => merged_width_lt hLam hQ hM (not_le.mp hc) hq i)
end Window
section Paths
def stepOffset (st : PathStep) : Fin 4 → ℤ := if st.2 then Pi.single st.1 1 else -Pi.single st.1 1
def offsetPath : (Fin 4 → ℤ) → List PathStep → List (Fin 4 → ℤ)
  | u, [] => [u]
  | u, st :: r => u :: offsetPath (u + stepOffset st) r
def offsetEnd : (Fin 4 → ℤ) → List PathStep → (Fin 4 → ℤ)
  | u, [] => u
  | u, st :: r => offsetEnd (u + stepOffset st) r
theorem offsetEnd_append (u : Fin 4 → ℤ) (l l' : List PathStep) :
    offsetEnd u (l ++ l') = offsetEnd (offsetEnd u l) l' := by
  induction l generalizing u with
  | nil => rfl
  | cons st r ih => exact ih _
theorem mem_offsetPath_self (u : Fin 4 → ℤ) (l : List PathStep) : u ∈ offsetPath u l := by
  cases l <;> simp [offsetPath]
theorem mem_offsetPath_append {u p : Fin 4 → ℤ} {l l' : List PathStep} (h : p ∈ offsetPath u (l ++ l')) :
    p ∈ offsetPath u l ∨ p ∈ offsetPath (offsetEnd u l) l' := by
  induction l generalizing u with
  | nil => exact Or.inr h
  | cons st r ih =>
    simp only [List.cons_append, offsetPath, List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inl (by simp [offsetPath])
    · rcases ih h with h | h
      · exact Or.inl (by simp [offsetPath, h])
      · exact Or.inr h
def InOffsetRange (lo hi u : Fin 4 → ℤ) : Prop := ∀ k, lo k ≤ u k ∧ u k ≤ hi k
def partialShift (u h : Fin 4 → ℤ) (S : Finset (Fin 4)) : Fin 4 → ℤ := fun k => u k + if k ∈ S then h k else 0
theorem replicate_offsetPath {lo hi : Fin 4 → ℤ} (a : Fin 4) (b : Bool) :
    ∀ (m : ℕ) (u : Fin 4 → ℤ), InOffsetRange lo hi u →
      InOffsetRange lo hi (u + (m : ℤ) • stepOffset (a, b)) →
      (∀ p ∈ offsetPath u (List.replicate m (a, b)), InOffsetRange lo hi p) ∧
        offsetEnd u (List.replicate m (a, b)) = u + (m : ℤ) • stepOffset (a, b) := by
  intro m
  induction m with
  | zero =>
    intro u hu _
    simp [offsetPath, offsetEnd, hu]
  | succ m ih =>
    intro u hu hv
    have hs : InOffsetRange lo hi (u + stepOffset (a, b)) := by
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
    · simp only [List.replicate_succ, offsetEnd]
      rw [h2, he]
theorem natAbs_smul_stepOffset (a : Fin 4) (c : ℤ) :
    ((c.natAbs : ℤ)) • stepOffset (a, decide (0 ≤ c)) = Pi.single a c := by
  funext k
  by_cases hk : k = a
  · subst hk
    by_cases hc : 0 ≤ c
    · simp [stepOffset, hc, abs_of_nonneg hc]
    · have : c < 0 := not_le.mp hc
      simp [stepOffset, hc, abs_of_neg this]
  · by_cases hc : 0 ≤ c <;> simp [stepOffset, hc, hk]
theorem axisLegs_offsetPath {lo hi u h : Fin 4 → ℤ} (hu : InOffsetRange lo hi u) (hv : InOffsetRange lo hi (u + h))
    (π : Equiv.Perm (Fin 4)) :
    ∀ (ks : List (Fin 4)) (S : Finset (Fin 4)), ks.Nodup → (∀ k ∈ ks, π k ∉ S) →
      (∀ p ∈ offsetPath (partialShift u h S)
          (ks.flatMap fun k => List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))), InOffsetRange lo hi p) ∧
        offsetEnd (partialShift u h S)
            (ks.flatMap fun k => List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))) =
          partialShift u h (S ∪ (ks.map π).toFinset) := by
  have hpart : ∀ S, InOffsetRange lo hi (partialShift u h S) := by
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
    simp only [List.flatMap_nil, offsetEnd, offsetPath, List.mem_singleton, List.map_nil, List.toFinset_nil,
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
    obtain ⟨h1, h2⟩ := replicate_offsetPath (lo := lo) (hi := hi) (π a) (decide (0 ≤ h (π a))) (h (π a)).natAbs
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
    · rw [offsetEnd_append, h2, hend, h4]
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
theorem axisPath_offsetPath {lo hi u h : Fin 4 → ℤ} (hu : InOffsetRange lo hi u) (hv : InOffsetRange lo hi (u + h))
    (π : Equiv.Perm (Fin 4)) :
    (∀ p ∈ offsetPath u (axisPath h π), InOffsetRange lo hi p) ∧ offsetEnd u (axisPath h π) = u + h := by
  have h0 : partialShift u h ∅ = u := by
    funext k
    simp [partialShift]
  have := axisLegs_offsetPath hu hv π (List.finRange 4) ∅ (List.nodup_finRange 4) (by simp)
  rw [h0] at this
  refine ⟨this.1, this.2.trans ?_⟩
  funext k
  have : k ∈ ((List.finRange 4).map π).toFinset := by
    simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, true_and]
    exact ⟨π.symm k, by simp⟩
  simp [partialShift, this]
theorem window_of_offsetInBox {L m : ℕ} (hm : m ≤ 7 * L) {u : Fin 4 → ℤ} (h : OffsetInBox m u) :
    OffsetWindow L u := by
  intro k
  have h1 := abs_le.mp (h k)
  omega
theorem offsetInBox_of_mem_centredCube {L : ℕ} {z : Fin 4 → ℤ} (h : z ∈ centredCube L) : OffsetInBox L z := by
  intro k
  have := TorusContours.mem_centredCube_iff.mp h k
  rw [abs_le]
  omega
end Paths
section Contours
variable {F F' : BlockFrame} [∀ j i, NeZero (F.period j i)] [∀ j i, NeZero (F'.period j i)]
theorem siteAtOffset_add_stepDisplacement (y : F.Cell) (u : Fin 4 → ℤ) (st : PathStep) :
    (siteAtOffset y u : F.Site F.depth) + stepDisplacement F.depth st = siteAtOffset y (u + stepOffset st) := by
  rcases st with ⟨i, b⟩
  cases b <;> simp [siteAtOffset, stepDisplacement, stepOffset, unitStep, TorusContours.siteOfCoords_add,
    TorusContours.siteOfCoords_neg, add_assoc]
theorem pathHolonomy_congr {R : ℕ} (X : F.GaugeField F.depth) (X' : F'.GaugeField F'.depth) (y : F.Cell)
    (y' : F'.Cell)
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
        simp [siteAtOffset, unitStep, sub_eq_add_neg, TorusContours.siteOfCoords_add,
          TorusContours.siteOfCoords_neg, add_assoc]
      have e2 : (siteAtOffset y' u : F'.Site F'.depth) - unitStep F'.depth i =
          siteAtOffset y' (u - Pi.single i 1) := by
        simp [siteAtOffset, unitStep, sub_eq_add_neg, TorusContours.siteOfCoords_add,
          TorusContours.siteOfCoords_neg, add_assoc]
      simp only [linkValue, Bool.false_eq_true, if_false, e1, e2, h4]
    · have h4 := hag u i h1 (by simpa [stepOffset] using h2)
      simp only [linkValue, if_true, h4]
theorem siteAtOffset_add_unitStep (y : F.Cell) (i : Fin 4) (v : Fin 4 → ℤ) :
    (siteAtOffset (y + unitStep F.top i) v : F.Site F.depth) = siteAtOffset y (v + Pi.single i (F.blockSide : ℤ)) := by
  simp only [siteAtOffset, TorusContours.cellCentre_add_unitStep, TorusContours.siteOfCoords_add]
  abel
theorem window_of_mem_centredCube {L : ℕ} {z : Fin 4 → ℤ} (h : z ∈ centredCube L) : OffsetWindow L z :=
  window_of_offsetInBox (by omega) (offsetInBox_of_mem_centredCube h)
def IsBaseOffset (J₀ : ℕ) (Q M : Finset OffsetBox) (z : Fin 4 → ℤ) : Prop :=
  ((Q = ∅ ∨ J₀ ≤ Q.card) → z = 0) ∧
    (¬ (Q = ∅ ∨ J₀ ≤ Q.card) → ∀ q ∈ M, ∀ v, InOffsetBox v q → ∀ i, v i ≠ z i)
theorem mem_baseSitesAt_of_open {J₀ : ℕ} {h : Finset (Finset (F.Site F.depth))} {y : F.Cell} {x : F.Site F.depth}
    (hc : ¬ (nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y)) :
    x ∈ baseSitesAt J₀ h y ↔ x ∈ sitesBelow F.depth y ∧ ∀ B ∈ excludedBoxes J₀ h y, ∀ x' ∈ B, ∀ i, x' i ≠ x i := by
  classical
  unfold baseSitesAt
  rw [if_neg hc]
  simp only [Finset.mem_filter]
theorem siteAtOffset_mem_baseSitesAt_iff (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ))
    (hL : 2 ^ 16 ≤ F.blockSide) {J₀ : ℕ} (hLam : 11 * 2 ^ 12 * J₀ < F.blockSide) {Q M : Finset OffsetBox}
    (hQ : NearbyLumpBoxes F.blockSide Q) (hM : MergedFamily (Q.image collarBox) M)
    {h : Finset (Finset (F.Site F.depth))} {y : F.Cell} (hb : nearbyLumps h y = Q.image (boxAtOffset y))
    {z : Fin 4 → ℤ} (hz : z ∈ centredCube F.blockSide) :
    siteAtOffset y z ∈ baseSitesAt J₀ h y ↔ IsBaseOffset J₀ Q M z := by
  classical
  have hL2 : 2 ≤ F.blockSide := by omega
  obtain ⟨hcr, hem, hbx⟩ := excludedBoxes_of_lumpBoxes hbig hL hLam hQ hM hb
  have hC : (nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y) ↔ (Q = ∅ ∨ J₀ ≤ Q.card) := by rw [hem, hcr]
  by_cases hc : Q = ∅ ∨ J₀ ≤ Q.card
  · unfold baseSitesAt
    rw [if_pos (hC.mpr hc), Finset.mem_singleton]
    have h0 : (cellCentre F.depth y : F.Site F.depth) = siteAtOffset y 0 := by
      rw [siteAtOffset, TorusContours.siteOfCoords_zero, add_zero]
    rw [h0, siteAtOffset_eq_iff hbig hL2 y (window_of_mem_centredCube hz)
      (window_of_mem_centredCube (TorusContours.zero_mem_centredCube (by omega)))]
    exact ⟨fun h1 => ⟨fun _ => h1, fun h2 => absurd hc h2⟩, fun h1 => h1.1 hc⟩
  · rw [mem_baseSitesAt_of_open (fun h1 => hc (hC.mp h1))]
    have hnc : ¬ J₀ ≤ Q.card := fun h1 => hc (Or.inr h1)
    rw [if_neg hnc] at hbx
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨fun h3 => absurd h3 hc, fun _ q hq v hv i he => ?_⟩
      refine h2 (boxAtOffset y q) (hbx ▸ Finset.mem_image_of_mem _ hq) (siteAtOffset y v)
        (mem_boxAtOffset.mpr ⟨v, hv, rfl⟩) i ?_
      exact (siteAtOffset_apply_eq_iff hbig y (abs_sub_le_of_window
        (window_of_mem_box (merged_inWindow hL hQ hM hq) hv) (window_of_mem_centredCube hz) i) hL2).mpr he
    · rintro ⟨-, h2⟩
      refine ⟨(TorusContours.mem_sitesBelow_iff y _).mpr ⟨z, hz, rfl⟩, fun B hB x hx i he => ?_⟩
      rw [hbx] at hB
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨v, hv, rfl⟩ := mem_boxAtOffset.mp hx
      exact h2 hc q hq v hv i
        ((siteAtOffset_apply_eq_iff hbig y (abs_sub_le_of_window
          (window_of_mem_box (merged_inWindow hL hQ hM hq) hv) (window_of_mem_centredCube hz) i) hL2).mp he)
theorem card_baseSitesAt (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ))
    (hL : 2 ^ 16 ≤ F.blockSide) {J₀ : ℕ} (hLam : 11 * 2 ^ 12 * J₀ < F.blockSide) {Q M : Finset OffsetBox}
    (hQ : NearbyLumpBoxes F.blockSide Q) (hM : MergedFamily (Q.image collarBox) M)
    {h : Finset (Finset (F.Site F.depth))} {y : F.Cell} (hb : nearbyLumps h y = Q.image (boxAtOffset y)) :
    (baseSitesAt J₀ h y).card =
      (open Classical in ((centredCube F.blockSide).filter (IsBaseOffset J₀ Q M)).card) := by
  classical
  have hsub : ∀ x ∈ baseSitesAt J₀ h y, ∃ z ∈ centredCube F.blockSide, x = siteAtOffset y z := by
    intro x hx
    by_cases hc : nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y
    · unfold baseSitesAt at hx
      rw [if_pos hc] at hx
      rw [Finset.mem_singleton.mp hx]
      exact ⟨0, TorusContours.zero_mem_centredCube (by omega),
        by rw [siteAtOffset, TorusContours.siteOfCoords_zero, add_zero]⟩
    · exact (TorusContours.mem_sitesBelow_iff y x).mp ((mem_baseSitesAt_of_open hc).mp hx).1
  have himg : baseSitesAt J₀ h y =
      ((centredCube F.blockSide).filter (IsBaseOffset J₀ Q M)).image (siteAtOffset y) := by
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
  exact (siteAtOffset_eq_iff hbig (by omega) y (window_of_mem_centredCube (Finset.mem_filter.mp hz).1)
    (window_of_mem_centredCube (Finset.mem_filter.mp hz').1)).mp he
end Contours
section Lumps
variable {F F' : BlockFrame} [∀ j i, NeZero (F.period j i)] [∀ j i, NeZero (F'.period j i)]
def lumpBox {L : ℕ} (g : LumpGrid L) (z : Fin 4 → ℤ) : OffsetBox :=
  (fun i => z i - offsetFromCentre L (z i) + g.lower (offsetFromCentre L (z i)),
    fun i => z i - offsetFromCentre L (z i) + g.upper (offsetFromCentre L (z i)))
theorem offsetFromCentre_spec {L : ℕ} (hL : 0 < L) (hodd : Odd L) (c : ℤ) :
    |offsetFromCentre L c| ≤ ((L : ℤ) - 1) / 2 ∧
      c - offsetFromCentre L c = (L : ℤ) * ((c + ((L : ℤ) - 1) / 2) / (L : ℤ)) := by
  obtain ⟨s, hs⟩ := hodd
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  have ht : ((L : ℤ) - 1) / 2 = s := by omega
  have h1 := Int.emod_nonneg (c + ((L : ℤ) - 1) / 2) (ne_of_gt hLz)
  have h2 := Int.emod_lt_of_pos (c + ((L : ℤ) - 1) / 2) hLz
  have h3 := Int.emod_add_mul_ediv (c + ((L : ℤ) - 1) / 2) (L : ℤ)
  unfold offsetFromCentre
  constructor
  · rw [abs_le]
    omega
  · linarith
theorem offsetFromCentre_add_mul {L : ℕ} (c m : ℤ) :
    offsetFromCentre L (c + (L : ℤ) * m) = offsetFromCentre L c := by
  unfold offsetFromCentre
  have : c + (L : ℤ) * m + ((L : ℤ) - 1) / 2 = c + ((L : ℤ) - 1) / 2 + (L : ℤ) * m := by ring
  rw [this, Int.add_mul_emod_self_left]
omit [∀ j i, NeZero (F.period j i)] [∀ j i, NeZero (F'.period j i)] in
theorem boxSites_add_period {j : ℕ} (a b s : Fin 4 → ℤ) (hs : ∀ i, (F.period j i : ℤ) ∣ s i) :
    (boxSites j (fun i => a i + s i) (fun i => b i + s i) : Finset (F.Site j)) = boxSites j a b := by
  have hz : (siteOfCoords j s : F.Site j) = 0 := by
    funext i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hs i)
  ext x
  rw [mem_boxSites_iff, mem_boxSites_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c - s, fun i => ?_, ?_⟩
    · have := hc i
      simp only [Pi.sub_apply]
      omega
    · rw [sub_eq_add_neg, TorusContours.siteOfCoords_add, TorusContours.siteOfCoords_neg, hz]
      simp
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c + s, fun i => ?_, ?_⟩
    · have := hc i
      simp only [Pi.add_apply]
      omega
    · rw [TorusContours.siteOfCoords_add, hz, add_zero]
theorem lumpOf_siteAtOffset {g : LumpGrid F.blockSide} (y : F.Cell) (z : Fin 4 → ℤ) :
    lumpOf g (siteAtOffset y z : F.Site F.depth) = boxAtOffset y (lumpBox g z) := by
  have hcast : ∀ i, ∃ k : ℤ, siteCoords (siteAtOffset y z : F.Site F.depth) i =
      (F.blockSide : ℤ) * siteCoords y i + z i + (F.period F.depth i : ℤ) * k := by
    intro i
    have h1 : (((siteCoords (siteAtOffset y z : F.Site F.depth) i : ℤ)) : ZMod (F.period F.depth i)) =
        (((F.blockSide : ℤ) * siteCoords y i + z i : ℤ) : ZMod (F.period F.depth i)) := by
      rw [TorusContours.intCast_siteCoords, siteAtOffset_apply]
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
    obtain ⟨k, hk⟩ := h1
    exact ⟨-k, by linarith⟩
  choose k hk using hcast
  have hoff : ∀ i, offsetFromCentre F.blockSide (siteCoords (siteAtOffset y z : F.Site F.depth) i) =
      offsetFromCentre F.blockSide (z i) := by
    intro i
    rw [hk i, TorusContours.period_depth]
    have : (F.blockSide : ℤ) * siteCoords y i + z i + ((F.period F.top i * F.blockSide : ℕ) : ℤ) * k i =
        z i + (F.blockSide : ℤ) * (siteCoords y i + (F.period F.top i : ℤ) * k i) := by
      push_cast
      ring
    rw [this, offsetFromCentre_add_mul]
  rw [boxAtOffset_eq_boxSites]
  unfold lumpOf
  simp only [hoff]
  have hs := boxSites_add_period (F := F) (j := F.depth)
    (fun i => (F.blockSide : ℤ) * siteCoords y i + (lumpBox g z).1 i)
    (fun i => (F.blockSide : ℤ) * siteCoords y i + (lumpBox g z).2 i)
    (fun i => (F.period F.depth i : ℤ) * k i) (fun i => ⟨k i, rfl⟩)
  rw [← hs]
  congr 1
  · funext i
    simp only [lumpBox, hk i]
    ring
  · funext i
    simp only [lumpBox, hk i]
    ring
def InNearBlocks (L : ℕ) (z : Fin 4 → ℤ) : Prop := ∀ i, |z i| ≤ 2 * (L : ℤ) + ((L : ℤ) - 1) / 2
theorem lumpBox_spec {L : ℕ} (hL : 0 < L) (hodd : Odd L) (g : LumpGrid L) (z : Fin 4 → ℤ) (i : Fin 4) :
    (lumpBox g z).1 i ≤ z i ∧ z i ≤ (lumpBox g z).2 i ∧ (lumpBox g z).2 i - (lumpBox g z).1 i + 1 < 2 ^ 15 := by
  have hsp := offsetFromCentre_spec hL hodd (z i)
  have h1 := g.mem_interval _ hsp.1
  have h2 := g.interval_length _ hsp.1
  simp only [lumpBox]
  omega
theorem lumpBox_in_block {L : ℕ} (hL : 0 < L) (hodd : Odd L) (g : LumpGrid L) {z : Fin 4 → ℤ}
    (hz : InNearBlocks L z) :
    ∃ m : Fin 4 → ℤ, (∀ i, -2 ≤ m i ∧ m i ≤ 2) ∧
      ∀ v, InOffsetBox v (lumpBox g z) → ∀ i, |v i - (L : ℤ) * m i| ≤ ((L : ℤ) - 1) / 2 := by
  obtain ⟨s, hs⟩ := hodd
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  have ht : ((L : ℤ) - 1) / 2 = s := by omega
  have hsp := fun i => offsetFromCentre_spec hL ⟨s, hs⟩ (z i)
  refine ⟨fun i => (z i + ((L : ℤ) - 1) / 2) / (L : ℤ), fun i => ?_, fun v hv i => ?_⟩
  · have h1 := abs_le.mp (hz i)
    dsimp only
    constructor
    · rw [Int.le_ediv_iff_mul_le hLz]
      omega
    · have : (z i + ((L : ℤ) - 1) / 2) / (L : ℤ) < 3 := by
        rw [Int.ediv_lt_iff_lt_mul hLz]
        omega
      omega
  · have h1 := g.mem_interval _ (hsp i).1
    have h2 := hv i
    have h3 := (hsp i).2
    simp only [lumpBox] at h2
    rw [abs_le]
    simp only []
    rw [← h3]
    omega
omit [∀ j i, NeZero (F.period j i)] [∀ j i, NeZero (F'.period j i)] in
theorem mem_cutBelow_cellBall {y : F.Cell} {x : F.Site F.depth} :
    x ∈ cutBelow F.depth (cellBall y 2) ↔ ∃ m : Fin 4 → ℤ, (∀ i, -2 ≤ m i ∧ m i ≤ 2) ∧
      ∃ w ∈ centredCube F.blockSide, x = siteAtOffset (y + siteOfCoords F.top m) w := by
  rw [cutBelow, Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hc, hx⟩
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨w, hw, rfl⟩ := (TorusContours.mem_sitesBelow_iff _ _).mp hx
    refine ⟨m, fun i => ?_, w, hw, rfl⟩
    exact_mod_cast (mem_centredCube_odd_iff (m := 2)).mp hm i
  · rintro ⟨m, hm, w, hw, rfl⟩
    refine ⟨_, Finset.mem_image.mpr ⟨m, (mem_centredCube_odd_iff (m := 2)).mpr fun i => ?_, rfl⟩,
      (TorusContours.mem_sitesBelow_iff _ _).mpr ⟨w, hw, rfl⟩⟩
    exact_mod_cast hm i
theorem cellCentre_add_siteOfCoords (y : F.Cell) (m : Fin 4 → ℤ) :
    (cellCentre F.depth (y + siteOfCoords F.top m) : F.Site F.depth) =
      cellCentre F.depth y + siteOfCoords F.depth fun i => (F.blockSide : ℤ) * m i := by
  have h : (y + siteOfCoords F.top m : F.Cell) = siteOfCoords F.top (siteCoords y + m) := by
    rw [TorusContours.siteOfCoords_add, TorusContours.siteOfCoords_siteCoords]
  rw [h, TorusContours.cellCentre_siteOfCoords, TorusContours.cellCentre_eq, ← TorusContours.siteOfCoords_add]
  congr 1
  funext k
  simp [mul_add]
theorem siteAtOffset_add_cell (y : F.Cell) (m w : Fin 4 → ℤ) :
    (siteAtOffset (y + siteOfCoords F.top m) w : F.Site F.depth) =
      siteAtOffset y (fun i => w i + (F.blockSide : ℤ) * m i) := by
  simp only [siteAtOffset, cellCentre_add_siteOfCoords]
  rw [add_assoc, ← TorusContours.siteOfCoords_add]
  congr 2
  funext i
  simp [add_comm]
theorem mem_cutBelow_cellBall_iff (hL : 2 ≤ F.blockSide) (hodd : Odd F.blockSide) (y : F.Cell)
    {x : F.Site F.depth} :
    x ∈ cutBelow F.depth (cellBall y 2) ↔ ∃ z, InNearBlocks F.blockSide z ∧ x = siteAtOffset y z := by
  rw [mem_cutBelow_cellBall]
  constructor
  · rintro ⟨m, hm, w, hw, rfl⟩
    refine ⟨fun i => w i + (F.blockSide : ℤ) * m i, fun i => ?_, siteAtOffset_add_cell y m w⟩
    have h1 := TorusContours.mem_centredCube_iff.mp hw i
    have h2 := hm i
    rw [abs_le]
    simp only []
    constructor <;> nlinarith
  · rintro ⟨z, hz, rfl⟩
    have hsp := fun i => offsetFromCentre_spec (L := F.blockSide) (by omega) hodd (z i)
    refine ⟨fun i => (z i + ((F.blockSide : ℤ) - 1) / 2) / (F.blockSide : ℤ), fun i => ?_,
      fun i => offsetFromCentre F.blockSide (z i), ?_, ?_⟩
    · have h1 := abs_le.mp (hz i)
      have hLz' : (0 : ℤ) < F.blockSide := by omega
      obtain ⟨s, hs⟩ := hodd
      dsimp only
      constructor
      · rw [Int.le_ediv_iff_mul_le hLz']
        omega
      · have : (z i + ((F.blockSide : ℤ) - 1) / 2) / (F.blockSide : ℤ) < 3 := by
          rw [Int.ediv_lt_iff_lt_mul hLz']
          omega
        omega
    · rw [TorusContours.mem_centredCube_iff]
      intro i
      have := abs_le.mp (hsp i).1
      omega
    · rw [siteAtOffset_add_cell]
      congr 1
      funext i
      have := (hsp i).2
      omega
theorem mem_lumpOf_self (hL : 2 ≤ F.blockSide) (hodd : Odd F.blockSide) (g : LumpGrid F.blockSide) (y : F.Cell)
    (z : Fin 4 → ℤ) : (siteAtOffset y z : F.Site F.depth) ∈ lumpOf g (siteAtOffset y z : F.Site F.depth) := by
  rw [lumpOf_siteAtOffset]
  refine mem_boxAtOffset.mpr ⟨z, fun i => ?_, rfl⟩
  have := lumpBox_spec (L := F.blockSide) (by omega) hodd g z i
  exact ⟨this.1, this.2.1⟩
def cornerOffsetList (μ ν : Fin 4) : List (Fin 4 → ℤ) :=
  [0, Pi.single μ 1, Pi.single ν 1, Pi.single μ 1 + Pi.single ν 1]
omit [∀ j i, NeZero (F.period j i)] [∀ j i, NeZero (F'.period j i)] in
theorem mem_plaquetteCorners_iff {p : F.Site F.depth × Fin 4 × Fin 4} {x : F.Site F.depth} :
    x ∈ plaquetteCorners p ↔ ∃ δ ∈ cornerOffsetList p.2.1 p.2.2, x = p.1 + siteOfCoords F.depth δ := by
  simp only [plaquetteCorners, cornerOffsetList, Finset.mem_insert, Finset.mem_singleton, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, TorusContours.siteOfCoords_add,
    TorusContours.siteOfCoords_zero, add_zero, unitStep]
  simp only [add_assoc]
theorem cornerOffset_bound {μ ν : Fin 4} {δ : Fin 4 → ℤ} (h : δ ∈ cornerOffsetList μ ν) (k : Fin 4) :
    -2 ≤ δ k ∧ δ k ≤ 2 := by
  simp only [cornerOffsetList, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · simp
  · by_cases hk : k = μ
    · subst hk; simp
    · simp [hk]
  · by_cases hk : k = ν
    · subst hk; simp
    · simp [hk]
  · simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> omega
theorem plaquetteDefect_congr {R : ℕ} (X : F.GaugeField F.depth) (X' : F'.GaugeField F'.depth) (y : F.Cell)
    (y' : F'.Cell)
    (hag : ∀ (u : Fin 4 → ℤ) (i : Fin 4), OffsetInBox R u → OffsetInBox R (u + Pi.single i 1) →
      X (siteAtOffset y u) i = X' (siteAtOffset y' u) i) (μ ν : Fin 4) (u : Fin 4 → ℤ)
    (hu : ∀ k, |u k| + 2 ≤ (R : ℤ)) :
    plaquetteDefect X (siteAtOffset y u, μ, ν) = plaquetteDefect X' (siteAtOffset y' u, μ, ν) := by
  unfold plaquetteDefect plaquetteHolonomy
  simp only []
  rw [pathHolonomy_congr X X' y y' hag]
  intro p hp
  simp only [offsetPath, stepOffset, Bool.false_eq_true, if_true, if_false, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  intro k
  have h1 := hu k
  have h2 := abs_le.mp (le_refl |u k|)
  rw [abs_le]
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> (try simp only [Pi.add_apply, Pi.neg_apply, Pi.single_apply]) <;>
    (try split_ifs) <;> omega
omit [∀ j i, NeZero (F'.period j i)] in
theorem exists_siteAtOffset (y : F.Cell) (x : F.Site F.depth) : ∃ w, x = siteAtOffset y w := by
  refine ⟨fun i => siteCoords x i - (F.blockSide : ℤ) * siteCoords y i, ?_⟩
  rw [TorusContours.siteAtOffset_eq]
  have : (fun i => (F.blockSide : ℤ) * siteCoords y i + (siteCoords x i - (F.blockSide : ℤ) * siteCoords y i)) =
      siteCoords x := by
    funext i
    ring
  rw [this, TorusContours.siteOfCoords_siteCoords]
theorem lumpBox_inWindow {L : ℕ} (hL : 2 ^ 16 ≤ L) (hodd : Odd L) (g : LumpGrid L) {z : Fin 4 → ℤ}
    (hz : InNearBlocks L z) :
    BoxInWindow L (lumpBox g z) ∧ (∀ v, InOffsetBox v (lumpBox g z) → InNearBlocks L v) := by
  obtain ⟨m, hm, hb⟩ := lumpBox_in_block (by omega) hodd g hz
  have hK : ∀ v, InOffsetBox v (lumpBox g z) → InNearBlocks L v := by
    intro v hv i
    have h1 := abs_le.mp (hb v hv i)
    have h2 := hm i
    rw [abs_le]
    constructor <;> nlinarith
  have hord : BoxOrdered (lumpBox g z) := fun i => by
    have := lumpBox_spec (by omega) hodd g z i
    omega
  have hw : ∀ v, InNearBlocks L v → OffsetWindow L v := by
    intro v hv i
    have := abs_le.mp (hv i)
    omega
  exact ⟨⟨hord, hw _ (hK _ (lower_mem_box hord)), hw _ (hK _ (upper_mem_box hord))⟩, hK⟩
theorem mem_hotLumps_transfer (hL : 2 ^ 16 ≤ F.blockSide) (hodd : Odd F.blockSide)
    (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ))
    (g : LumpGrid F.blockSide) (g' : LumpGrid F'.blockSide)
    (hg : ∀ z, (lumpBox g z) = (lumpBox g' z)) (s : ℝ) (X : F.GaugeField F.depth) (X' : F'.GaugeField F'.depth)
    (y : F.Cell) (y' : F'.Cell) (S : Finset (F.Site F.depth)) (S' : Finset (F'.Site F'.depth))
    (hS : ∀ u, OffsetInBox (3 * F.blockSide) u → (siteAtOffset y u : F.Site F.depth) ∈ S →
      (siteAtOffset y' u : F'.Site F'.depth) ∈ S')
    (hag : ∀ (u : Fin 4 → ℤ) (i : Fin 4), OffsetInBox (3 * F.blockSide) u →
      OffsetInBox (3 * F.blockSide) (u + Pi.single i 1) → X (siteAtOffset y u) i = X' (siteAtOffset y' u) i)
    {z : Fin 4 → ℤ} (hz : InNearBlocks F.blockSide z)
    (hin : lumpOf g (siteAtOffset y z : F.Site F.depth) ∈ hotLumps g s S X) :
    lumpOf g' (siteAtOffset y' z : F'.Site F'.depth) ∈ hotLumps g' s S' X' := by
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
  obtain ⟨hzw, hzK⟩ := lumpBox_inWindow hL hodd g hz
  have hvK := hzK v hv
  obtain ⟨hvw, -⟩ := lumpBox_inWindow hL hodd g hvK
  have hrep : lumpBox g v = lumpBox g z := by
    refine boxAtOffset_injective hbig hL2 y hvw hzw ?_
    rw [← lumpOf_siteAtOffset, ← lumpOf_siteAtOffset]
    exact hxl
  obtain ⟨δ, hδ, hxδ⟩ := mem_plaquetteCorners_iff.mp hx
  simp only [] at hδ hxδ
  have hp₀ : p₀ = siteAtOffset y (v - δ) := by
    have : (siteAtOffset y (v - δ) : F.Site F.depth) = siteAtOffset y v - siteOfCoords F.depth δ := by
      simp only [siteAtOffset, sub_eq_add_neg, TorusContours.siteOfCoords_add, TorusContours.siteOfCoords_neg]
      abel
    rw [this, hxδ]
    abel
  subst hp₀
  have hbound : ∀ k, |(v - δ) k| + 2 ≤ ((3 * F.blockSide : ℕ) : ℤ) := by
    intro k
    have h1 := abs_le.mp (hvK k)
    have h2 := cornerOffset_bound hδ k
    have h3 : |(v - δ) k| ≤ 2 * (F.blockSide : ℤ) + ((F.blockSide : ℤ) - 1) / 2 + 2 := by
      simp only [Pi.sub_apply]
      rw [abs_le]
      omega
    push_cast
    omega
  have hcur := plaquetteDefect_congr X X' y y' hag μ ν (v - δ) hbound
  have hmemP := Finset.mem_filter.mp hpc
  have hlt : μ < ν := hmemP.2.1
  have hcor := hmemP.2.2
  have hnear : ∀ {G : BlockFrame} (w : G.Cell) (c d : Fin 4 → ℤ),
      (siteAtOffset w c : G.Site G.depth) + siteOfCoords G.depth d = siteAtOffset w (c + d) := by
    intro G w c d
    simp only [siteAtOffset, TorusContours.siteOfCoords_add, add_assoc]
  have hcorner : ∀ d ∈ cornerOffsetList μ ν, (siteAtOffset y' (v - δ + d) : F'.Site F'.depth) ∈ S' := by
    intro d hd
    refine hS _ (fun k => ?_) (hcor (mem_plaquetteCorners_iff.mpr ⟨d, hd, (hnear y _ _).symm⟩))
    have h1 := hbound k
    have h2 := cornerOffset_bound hd k
    have h3 := abs_le.mp (le_refl |(v - δ) k|)
    rw [abs_le]
    simp only [Pi.add_apply]
    constructor <;> omega
  have hx' : (siteAtOffset y' v : F'.Site F'.depth) ∈ plaquetteCorners (siteAtOffset y' (v - δ), μ, ν) := by
    refine mem_plaquetteCorners_iff.mpr ⟨δ, hδ, ?_⟩
    simp only [siteAtOffset, sub_eq_add_neg, TorusContours.siteOfCoords_add, TorusContours.siteOfCoords_neg]
    abel
  have hzero : (0 : Fin 4 → ℤ) ∈ cornerOffsetList μ ν := by simp [cornerOffsetList]
  refine Finset.mem_biUnion.mpr ⟨(siteAtOffset y' (v - δ), μ, ν), Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
  · refine Finset.mem_filter.mpr ⟨?_, hlt, fun x hx => ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩
      have := hcorner 0 hzero
      simpa using this
    · obtain ⟨d, hd, rfl⟩ := mem_plaquetteCorners_iff.mp hx
      simp only []
      rw [hnear]
      exact hcorner d hd
  · rw [← hcur]
    exact hps
  · refine Finset.mem_image.mpr ⟨_, hx', ?_⟩
    rw [lumpOf_siteAtOffset, lumpOf_siteAtOffset, ← hg v, ← hg z, hrep]
omit [∀ j i, NeZero (F.period j i)] [∀ j i, NeZero (F'.period j i)] in
theorem mem_nearbyLumps {h : Finset (Finset (F.Site F.depth))} {y : F.Cell} {l : Finset (F.Site F.depth)} :
    l ∈ nearbyLumps h y ↔ l ∈ h ∧ l ⊆ cutBelow F.depth (cellBall y 2) := by
  simp only [nearbyLumps, Finset.mem_filter]
theorem mem_nearbyLumps_iff (hL : 2 ≤ F.blockSide) (hodd : Odd F.blockSide) {h : Finset (Finset (F.Site F.depth))}
    {y : F.Cell} {l : Finset (F.Site F.depth)} :
    l ∈ nearbyLumps h y ↔ l ∈ h ∧ ∀ x ∈ l, ∃ z, InNearBlocks F.blockSide z ∧ x = siteAtOffset y z := by
  rw [mem_nearbyLumps, Finset.subset_iff]
  simp only [mem_cutBelow_cellBall_iff hL hodd y]
theorem lumpOf_in_nearBlocks (hL : 2 ^ 16 ≤ F.blockSide) (hodd : Odd F.blockSide) (g : LumpGrid F.blockSide)
    (y : F.Cell) {z : Fin 4 → ℤ} (hz : InNearBlocks F.blockSide z) :
    ∀ x ∈ lumpOf g (siteAtOffset y z : F.Site F.depth), ∃ v, InNearBlocks F.blockSide v ∧ x = siteAtOffset y v := by
  intro x hx
  rw [lumpOf_siteAtOffset] at hx
  obtain ⟨v, hv, rfl⟩ := mem_boxAtOffset.mp hx
  exact ⟨v, (lumpBox_inWindow hL hodd g hz).2 v hv, rfl⟩
def nearBlockOffsets (L : ℕ) : Finset (Fin 4 → ℤ) := centredCube (2 * (2 * L + (L - 1) / 2) + 1)
theorem mem_nearBlockOffsets {L : ℕ} (hL : 1 ≤ L) {z : Fin 4 → ℤ} : z ∈ nearBlockOffsets L ↔ InNearBlocks L z := by
  unfold nearBlockOffsets InNearBlocks
  rw [mem_centredCube_odd_iff]
  have h : ((2 * L + (L - 1) / 2 : ℕ) : ℤ) = 2 * (L : ℤ) + ((L : ℤ) - 1) / 2 := by omega
  rw [h]
  simp only [abs_le]
theorem exists_lumpOf_of_mem_hotLumps {L : ℕ} {g : LumpGrid L} {s : ℝ} {j : ℕ} {X : Finset (F.Site j)}
    {W : F.GaugeField j} {l : Finset (F.Site j)} (hl : l ∈ hotLumps g s X W) : ∃ x : F.Site j, l = lumpOf g x := by
  classical
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hp
  exact ⟨x, rfl⟩
theorem sameNearbyLumps_of_agree (hL : 2 ^ 16 ≤ F.blockSide) (hodd : Odd F.blockSide)
    (hbig : ∀ i, 16 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ))
    (hbig' : ∀ i, 16 * (F'.blockSide : ℤ) ≤ (F'.period F'.depth i : ℤ)) (hLL : F'.blockSide = F.blockSide)
    (g : LumpGrid F.blockSide) (g' : LumpGrid F'.blockSide) (hg : ∀ z, (lumpBox g z) = (lumpBox g' z)) (s : ℝ)
    (X : F.GaugeField F.depth) (X' : F'.GaugeField F'.depth) (y : F.Cell) (y' : F'.Cell)
    (S : Finset (F.Site F.depth)) (S' : Finset (F'.Site F'.depth))
    (hS : ∀ u, OffsetInBox (3 * F.blockSide) u →
      ((siteAtOffset y u : F.Site F.depth) ∈ S ↔ (siteAtOffset y' u : F'.Site F'.depth) ∈ S'))
    (hag : ∀ (u : Fin 4 → ℤ) (i : Fin 4), OffsetInBox (3 * F.blockSide) u →
      OffsetInBox (3 * F.blockSide) (u + Pi.single i 1) → X (siteAtOffset y u) i = X' (siteAtOffset y' u) i) :
    SameNearbyLumps (hotLumps g s S X) (hotLumps g' s S' X') y y' := by
  classical
  have hL2 : 2 ≤ F.blockSide := by omega
  have hL' : 2 ^ 16 ≤ F'.blockSide := by omega
  have hL2' : 2 ≤ F'.blockSide := by omega
  have hodd' : Odd F'.blockSide := hLL ▸ hodd
  have hag' : ∀ (u : Fin 4 → ℤ) (i : Fin 4), OffsetInBox (3 * F'.blockSide) u →
      OffsetInBox (3 * F'.blockSide) (u + Pi.single i 1) → X' (siteAtOffset y' u) i = X (siteAtOffset y u) i := by
    intro u i h1 h2
    rw [hLL] at h1 h2
    exact (hag u i h1 h2).symm
  have hS₁ : ∀ u, OffsetInBox (3 * F.blockSide) u → (siteAtOffset y u : F.Site F.depth) ∈ S →
      (siteAtOffset y' u : F'.Site F'.depth) ∈ S' :=
    fun u hu => (hS u hu).mp
  have hS₂ : ∀ u, OffsetInBox (3 * F'.blockSide) u → (siteAtOffset y' u : F'.Site F'.depth) ∈ S' →
      (siteAtOffset y u : F.Site F.depth) ∈ S := by
    intro u hu
    rw [hLL] at hu
    exact (hS u hu).mpr
  have hKK : ∀ {z : Fin 4 → ℤ}, InNearBlocks F.blockSide z → InNearBlocks F'.blockSide z := fun h => by rwa [hLL]
  have hKK' : ∀ {z : Fin 4 → ℤ}, InNearBlocks F'.blockSide z → InNearBlocks F.blockSide z := fun h => by
    rwa [hLL] at h
  set h := hotLumps g s S X with hh
  set h' := hotLumps g' s S' X' with hh'
  refine ⟨((nearBlockOffsets F.blockSide).filter fun z => lumpOf g (siteAtOffset y z : F.Site F.depth) ∈ h).image
    (lumpBox g), ?_, ?_, ?_⟩
  · intro q hq i
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
    have hzK := (mem_nearBlockOffsets (by omega)).mp (Finset.mem_filter.mp hz).1
    obtain ⟨⟨hord, -, -⟩, hK⟩ := lumpBox_inWindow hL hodd g hzK
    have h1 := abs_le.mp (hK _ (lower_mem_box hord) i)
    have h2 := abs_le.mp (hK _ (upper_mem_box hord) i)
    have h3 := lumpBox_spec (L := F.blockSide) (by omega) hodd g z i
    omega
  · ext l
    rw [mem_nearbyLumps_iff hL2 hodd, Finset.image_image, Finset.mem_image]
    constructor
    · rintro ⟨hlh, hsub⟩
      obtain ⟨x₀, rfl⟩ := exists_lumpOf_of_mem_hotLumps hlh
      obtain ⟨w, rfl⟩ := exists_siteAtOffset y x₀
      obtain ⟨z, hz, he⟩ := hsub _ (mem_lumpOf_self hL2 hodd g y w)
      have hlz : lumpOf g (siteAtOffset y w : F.Site F.depth) = lumpOf g (siteAtOffset y z : F.Site F.depth) := by
        rw [he]
      refine ⟨z, Finset.mem_filter.mpr ⟨(mem_nearBlockOffsets (by omega)).mpr hz, hlz ▸ hlh⟩, ?_⟩
      rw [Function.comp_apply, ← lumpOf_siteAtOffset, hlz]
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hzK, hin⟩ := Finset.mem_filter.mp hz
      rw [Function.comp_apply, ← lumpOf_siteAtOffset]
      exact ⟨hin, lumpOf_in_nearBlocks hL hodd g y ((mem_nearBlockOffsets (by omega)).mp hzK)⟩
  · ext l
    rw [mem_nearbyLumps_iff hL2' hodd', Finset.image_image, Finset.mem_image]
    constructor
    · rintro ⟨hlh, hsub⟩
      obtain ⟨x₀, rfl⟩ := exists_lumpOf_of_mem_hotLumps hlh
      obtain ⟨w, rfl⟩ := exists_siteAtOffset y' x₀
      obtain ⟨z, hz, he⟩ := hsub _ (mem_lumpOf_self hL2' hodd' g' y' w)
      have hlz : lumpOf g' (siteAtOffset y' w : F'.Site F'.depth) =
          lumpOf g' (siteAtOffset y' z : F'.Site F'.depth) := by rw [he]
      have hback := mem_hotLumps_transfer hL' hodd' hbig' g' g (fun z => (hg z).symm) s X' X y' y S' S hS₂ hag' hz
        (hlz ▸ hlh)
      refine ⟨z, Finset.mem_filter.mpr ⟨(mem_nearBlockOffsets (by omega)).mpr (hKK' hz), hback⟩, ?_⟩
      rw [Function.comp_apply, hg z, ← lumpOf_siteAtOffset, hlz]
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hzK, hin⟩ := Finset.mem_filter.mp hz
      have hzI := (mem_nearBlockOffsets (by omega)).mp hzK
      rw [Function.comp_apply, hg z, ← lumpOf_siteAtOffset]
      exact ⟨mem_hotLumps_transfer hL hodd hbig g g' hg s X X' y y' S S' hS₁ hag hzI hin,
        lumpOf_in_nearBlocks hL' hodd' g' y' (hKK hzI)⟩
end Lumps
section Step
theorem period_ge_stepBlockFrame (L k : ℕ) [NeZero L] [NeZero k] (h : 16 ≤ k) (i : Fin 4) :
    16 * ((stepBlockFrame L k).blockSide : ℤ) ≤
      ((stepBlockFrame L k).period (stepBlockFrame L k).depth i : ℤ) := by
  show 16 * (L : ℤ) ≤ ((stepBlockFrame L k).period 0 i : ℤ)
  rw [TorusContours.stepBlockFrame_period_zero]
  push_cast
  nlinarith
end Step
section Coordinates
variable {ℓ : StepParameters} {n n' : ℕ} [NeZero n] [NeZero n']
theorem axialGauge_siteAtOffset (hfit : ℓ.Admissible) (h2 : 2 ≤ n) (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (y : (stepBlockFrame ℓ.side n).Cell) {z : Fin 4 → ℤ} (hz : z ∈ centredCube ℓ.side) :
    axialGauge 1 W (siteAtOffset y z : (stepBlockFrame ℓ.side n).Site 0) =
      pathHolonomy W (siteAtOffset y 0 : (stepBlockFrame ℓ.side n).Site 0) (axisPath z 1) := by
  have hs : ∀ i, 2 ≤ (stepBlockFrame ℓ.side n).extent i := fun _ => h2
  unfold axialGauge
  have e1 := TopLevelSites.enclosingCell_centre_add (F := stepBlockFrame ℓ.side n) hfit.L_odd hs y z hz
  have e2 := TopLevelSites.cellOffset_centre_add (F := stepBlockFrame ℓ.side n) hfit.L_odd hs y z hz
  have e3 : (siteAtOffset y 0 : (stepBlockFrame ℓ.side n).Site 0) = cellCentre 0 y := by
    rw [siteAtOffset, TorusContours.siteOfCoords_zero, add_zero]
    rfl
  rw [e3]
  unfold siteAtOffset
  exact congrArg₂ _ (congrArg _ e1) (congrArg₂ _ e2 rfl)
theorem pathHolonomy_axisPath_congr (hfit : ℓ.Admissible) (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (W' : (stepBlockFrame ℓ.side n').GaugeField 0)
    (y : (stepBlockFrame ℓ.side n).Cell) (y' : (stepBlockFrame ℓ.side n').Cell)
    (hag : ∀ (u : Fin 4 → ℤ) (i : Fin 4), OffsetInBox (3 * ℓ.side) u → OffsetInBox (3 * ℓ.side) (u + Pi.single i 1) →
      W (siteAtOffset y u) i = W' (siteAtOffset y' u) i) {c z : Fin 4 → ℤ} (hc : ∀ k, |c k| ≤ (ℓ.side : ℤ))
    (hz : z ∈ centredCube ℓ.side) :
    pathHolonomy W (siteAtOffset y c : (stepBlockFrame ℓ.side n).Site 0) (axisPath z 1) =
      pathHolonomy W' (siteAtOffset y' c : (stepBlockFrame ℓ.side n').Site 0) (axisPath z 1) := by
  refine pathHolonomy_congr (F := stepBlockFrame ℓ.side n) (F' := stepBlockFrame ℓ.side n') (R := 3 * ℓ.side)
    W W' y y' hag _ c fun p hp => ?_
  have hcz := TorusContours.mem_centredCube_iff.mp hz
  have hu : InOffsetRange (fun _ => -(ℓ.side : ℤ) - (ℓ.side : ℤ)) (fun _ => (ℓ.side : ℤ) + (ℓ.side : ℤ)) c :=
    fun k => by
      have := abs_le.mp (hc k)
      show -(ℓ.side : ℤ) - (ℓ.side : ℤ) ≤ c k ∧ c k ≤ (ℓ.side : ℤ) + (ℓ.side : ℤ)
      constructor <;> omega
  have hv : InOffsetRange (fun _ => -(ℓ.side : ℤ) - (ℓ.side : ℤ)) (fun _ => (ℓ.side : ℤ) + (ℓ.side : ℤ)) (c + z) :=
    fun k => by
      have h1 := abs_le.mp (hc k)
      have h2 := hcz k
      show -(ℓ.side : ℤ) - (ℓ.side : ℤ) ≤ c k + z k ∧ c k + z k ≤ (ℓ.side : ℤ) + (ℓ.side : ℤ)
      constructor <;> omega
  have hin := (axisPath_offsetPath hu hv 1).1 p hp
  intro k
  have h3 : -(ℓ.side : ℤ) - (ℓ.side : ℤ) ≤ p k ∧ p k ≤ (ℓ.side : ℤ) + (ℓ.side : ℤ) := hin k
  push_cast
  rw [abs_le]
  constructor <;> omega
theorem bondCoordinate_congr (hfit : ℓ.Admissible) (h2 : 2 ≤ n) (h2' : 2 ≤ n')
    (W : (stepBlockFrame ℓ.side n).GaugeField 0) (W' : (stepBlockFrame ℓ.side n').GaugeField 0)
    (y : (stepBlockFrame ℓ.side n).Cell) (y' : (stepBlockFrame ℓ.side n').Cell)
    (hag : ∀ (u : Fin 4 → ℤ) (i : Fin 4), OffsetInBox (3 * ℓ.side) u → OffsetInBox (3 * ℓ.side) (u + Pi.single i 1) →
      W (siteAtOffset y u) i = W' (siteAtOffset y' u) i)
    (V : (stepBlockFrame ℓ.side n).GaugeField 1) (V' : (stepBlockFrame ℓ.side n').GaugeField 1) (z : Fin 4 → ℤ)
    (i : Fin 4) (hz : z ∈ centredCube ℓ.side) (hV : V y i = V' y' i) :
    bondCoordinate 1 V W (siteAtOffset y z, i) = bondCoordinate 1 V' W' (siteAtOffset y' z, i) := by
  classical
  have hs : ∀ i, 2 ≤ (stepBlockFrame ℓ.side n).extent i := fun _ => h2
  have hs' : ∀ i, 2 ≤ (stepBlockFrame ℓ.side n').extent i := fun _ => h2'
  have hodd := hfit.L_odd
  have hLpos : (1 : ℤ) ≤ ℓ.side := by
    have := hfit.L_ge
    exact_mod_cast (by omega : 1 ≤ ℓ.side)
  have hcz := (TopLevelSites.mem_centredCube_iff z).mp hz
  have hhalf : TopLevelSites.halfWidth ℓ.side = ((ℓ.side : ℤ) - 1) / 2 := rfl
  have hcr := TopLevelSites.isCrossingBond_iff (F := stepBlockFrame ℓ.side n) hodd hs y z hz i
  have hcr' := TopLevelSites.isCrossingBond_iff (F := stepBlockFrame ℓ.side n') hodd hs' y' z hz i
  have hcell := TopLevelSites.enclosingCell_centre_add (F := stepBlockFrame ℓ.side n) hodd hs y z hz
  have hcell' := TopLevelSites.enclosingCell_centre_add (F := stepBlockFrame ℓ.side n') hodd hs' y' z hz
  have hzero : ∀ k, |(0 : Fin 4 → ℤ) k| ≤ (ℓ.side : ℤ) := fun k => by
    simp only [Pi.zero_apply, abs_zero]
    omega
  have hfirst : axialGauge 1 W (siteAtOffset y z : (stepBlockFrame ℓ.side n).Site 0) =
      axialGauge 1 W' (siteAtOffset y' z : (stepBlockFrame ℓ.side n').Site 0) := by
    rw [axialGauge_siteAtOffset hfit h2 W y hz, axialGauge_siteAtOffset hfit h2' W' y' hz]
    exact pathHolonomy_axisPath_congr hfit W W' y y' hag hzero hz
  have hbox : ∀ k, |z k| ≤ ((3 * ℓ.side : ℕ) : ℤ) := fun k => by
    have := hcz k
    have e : TopLevelSites.halfWidth ℓ.side ≤ ℓ.side := by
      rw [hhalf]
      omega
    rw [abs_le]
    push_cast
    constructor <;> omega
  have hbox' : ∀ k, |(z + Pi.single i 1 : Fin 4 → ℤ) k| ≤ ((3 * ℓ.side : ℕ) : ℤ) := fun k => by
    have h1 := abs_le.mp (hbox k)
    have h3 : (Pi.single i 1 : Fin 4 → ℤ) k ≤ 1 ∧ 0 ≤ (Pi.single i 1 : Fin 4 → ℤ) k := by
      by_cases hk : k = i
      · subst hk
        simp
      · simp [hk]
    have hc := hcz k
    have e : TopLevelSites.halfWidth ℓ.side ≤ ℓ.side := by
      rw [hhalf]
      omega
    simp only [Pi.add_apply]
    rw [abs_le]
    push_cast
    constructor <;> omega
  have hbond : W (siteAtOffset y z) i = W' (siteAtOffset y' z) i := hag z i hbox hbox'
  have hnext : axialGauge 1 W ((siteAtOffset y z : (stepBlockFrame ℓ.side n).Site 0) + unitStep 0 i) =
      axialGauge 1 W' ((siteAtOffset y' z : (stepBlockFrame ℓ.side n').Site 0) + unitStep 0 i) := by
    by_cases he : z i = TopLevelSites.halfWidth ℓ.side
    · obtain ⟨hin₀, e⟩ :=
        TopLevelSites.centre_add_add_unitStep_of_edge (F := stepBlockFrame ℓ.side n) hodd hs y z hz i he
      obtain ⟨-, e'⟩ :=
        TopLevelSites.centre_add_add_unitStep_of_edge (F := stepBlockFrame ℓ.side n') hodd hs' y' z hz i he
      have hin : z + Pi.single i (1 - (ℓ.side : ℤ)) ∈ centredCube ℓ.side := hin₀
      have e₁ : (siteAtOffset y z : (stepBlockFrame ℓ.side n).Site 0) + unitStep 0 i =
          siteAtOffset (y + unitStep 1 i) (z + Pi.single i (1 - (ℓ.side : ℤ))) := e
      have e₂ : (siteAtOffset y' z : (stepBlockFrame ℓ.side n').Site 0) + unitStep 0 i =
          siteAtOffset (y' + unitStep 1 i) (z + Pi.single i (1 - (ℓ.side : ℤ))) := e'
      have s₁ : (siteAtOffset (y + unitStep 1 i) 0 : (stepBlockFrame ℓ.side n).Site 0) =
          siteAtOffset y (0 + Pi.single i (ℓ.side : ℤ)) :=
        siteAtOffset_add_unitStep (F := stepBlockFrame ℓ.side n) y i 0
      have s₂ : (siteAtOffset (y' + unitStep 1 i) 0 : (stepBlockFrame ℓ.side n').Site 0) =
          siteAtOffset y' (0 + Pi.single i (ℓ.side : ℤ)) :=
        siteAtOffset_add_unitStep (F := stepBlockFrame ℓ.side n') y' i 0
      rw [e₁, e₂, axialGauge_siteAtOffset hfit h2 W _ hin, axialGauge_siteAtOffset hfit h2' W' _ hin, s₁, s₂]
      refine pathHolonomy_axisPath_congr hfit W W' y y' hag (fun k => ?_) hin
      by_cases hk : k = i
      · subst hk
        simp [abs_of_nonneg (by omega : (0 : ℤ) ≤ ℓ.side)]
      · simp [hk]
    · have hin : z + Pi.single i 1 ∈ centredCube ℓ.side := by
        rw [TopLevelSites.mem_centredCube_iff]
        intro l
        by_cases hl : l = i
        · subst hl
          simp only [Pi.add_apply, Pi.single_eq_same]
          have := hcz l
          omega
        · simp only [Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
          exact hcz l
      have e₁ : (siteAtOffset y z : (stepBlockFrame ℓ.side n).Site 0) + unitStep 0 i =
          siteAtOffset y (z + Pi.single i 1) :=
        TopLevelSites.centre_add_add_unitStep (F := stepBlockFrame ℓ.side n) y z i
      have e₂ : (siteAtOffset y' z : (stepBlockFrame ℓ.side n').Site 0) + unitStep 0 i =
          siteAtOffset y' (z + Pi.single i 1) :=
        TopLevelSites.centre_add_add_unitStep (F := stepBlockFrame ℓ.side n') y' z i
      rw [e₁, e₂, axialGauge_siteAtOffset hfit h2 W _ hin, axialGauge_siteAtOffset hfit h2' W' _ hin]
      exact pathHolonomy_axisPath_congr hfit W W' y y' hag hzero hin
  have hg : gaugeTransform (axialGauge 1 W) W (siteAtOffset y z) i =
      gaugeTransform (axialGauge 1 W') W' (siteAtOffset y' z) i := by
    unfold gaugeTransform
    rw [hfirst, hbond]
    exact congrArg _ (congrArg _ hnext)
  unfold bondCoordinate
  simp only []
  by_cases he : z i = TopLevelSites.halfWidth ℓ.side
  · have c1 : IsCrossingBond ((siteAtOffset y z : (stepBlockFrame ℓ.side n).Site 0), i) := hcr.mpr he
    have c2 : IsCrossingBond ((siteAtOffset y' z : (stepBlockFrame ℓ.side n').Site 0), i) := hcr'.mpr he
    rw [if_pos c1, if_pos c2, hg]
    have d1 : enclosingCell (siteAtOffset y z : (stepBlockFrame ℓ.side n).Site 0) = y := hcell
    have d2 : enclosingCell (siteAtOffset y' z : (stepBlockFrame ℓ.side n').Site 0) = y' := hcell'
    rw [d1, d2, hV]
  · have c1 : ¬ IsCrossingBond ((siteAtOffset y z : (stepBlockFrame ℓ.side n).Site 0), i) :=
      fun h => he (hcr.mp h)
    have c2 : ¬ IsCrossingBond ((siteAtOffset y' z : (stepBlockFrame ℓ.side n').Site 0), i) :=
      fun h => he (hcr'.mp h)
    rw [if_neg c1, if_neg c2, hg]
end Coordinates
theorem blockDataIsLocal : BlockDataIsLocal := by
  intro ℓ hfit n n' _ _ h16 h16' W W' y y' hag
  have hL : 2 ^ 16 ≤ ℓ.side := hfit.L_ge
  have hodd : Odd ℓ.side := hfit.L_odd
  have hLam : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side := hfit.depth_lt
  have hbig := period_ge_stepBlockFrame ℓ.side n h16
  have hbig' := period_ge_stepBlockFrame ℓ.side n' h16'
  refine ⟨fun S S' hS => ?_, fun V V' z i hz hV => ?_⟩
  · obtain ⟨Q, hQ, e, e'⟩ := sameNearbyLumps_of_agree (F := stepBlockFrame ℓ.side n) (F' := stepBlockFrame ℓ.side n')
      hL hodd hbig hbig' rfl ℓ.grid ℓ.grid (fun _ => rfl) ℓ.threshold W W' y y' S S' hS hag
    obtain ⟨M, hM⟩ := exists_mergedFamily _ (Q.image collarBox) rfl (by
      classical
      intro r hr
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
      intro i
      have := hQ q hq i
      simp only [collarBox]
      omega)
    refine ⟨(card_baseSitesAt (F := stepBlockFrame ℓ.side n) hbig hL hLam hQ hM e).trans
      (card_baseSitesAt (F := stepBlockFrame ℓ.side n') hbig' hL hLam hQ hM e').symm, fun z hz => ?_⟩
    exact (siteAtOffset_mem_baseSitesAt_iff (F := stepBlockFrame ℓ.side n) hbig hL hLam hQ hM e hz).trans
      (siteAtOffset_mem_baseSitesAt_iff (F := stepBlockFrame ℓ.side n') hbig' hL hLam hQ hM e' hz).symm
  · exact bondCoordinate_congr hfit (by omega) (by omega) W W' y y' hag V V' z i hz hV
end YangMills.Construction.BlockLocality
end
