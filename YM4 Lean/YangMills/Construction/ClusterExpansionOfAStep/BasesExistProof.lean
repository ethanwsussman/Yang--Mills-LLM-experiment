import YangMills.Construction.ClusterExpansionOfAStep.BasesExist
import YangMills.Construction.HoleBesideASecondHole.BoxesByTheirCorners
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open BlockAverages LumpContours
section BoxMerging
variable {F : BlockFrame} {j : ℕ}
abbrev CornerPair : Type := (Fin 4 → ℤ) × (Fin 4 → ℤ)
def boxOfCorners (F : BlockFrame) (j : ℕ) (q : CornerPair) : Finset (F.Site j) := boxSites j q.1 q.2
def sideWidth (q : CornerPair) (i : Fin 4) : ℤ := q.2 i - q.1 i + 1
theorem mem_boxOfCorners {q : CornerPair} {x : F.Site j} :
    x ∈ boxOfCorners F j q ↔ ∃ a : Fin 4 → ℤ, (∀ i, q.1 i ≤ a i ∧ a i ≤ q.2 i) ∧ siteOfCoords j a = x := by apply _root_.YangMills.Construction.CornerBoxes.mem_boxOfCorners <;> assumption
theorem siteOfCoords_add_period_mul (a k : Fin 4 → ℤ) :
    (siteOfCoords j (fun i => a i + (F.period j i : ℤ) * k i) : F.Site j) = siteOfCoords j a := by apply _root_.YangMills.Construction.CornerBoxes.siteOfCoords_add_period_mul <;> assumption
theorem exists_box_merge [∀ i, NeZero (F.period j i)] {q q' : CornerPair} (hq : ∀ i, q.1 i ≤ q.2 i)
    (hq' : ∀ i, q'.1 i ≤ q'.2 i) (hw : AreWithin 2 (boxOfCorners F j q) (boxOfCorners F j q')) :
    ∃ q'' : CornerPair, (∀ i, q''.1 i ≤ q''.2 i) ∧ boxOfCorners F j q ⊆ boxOfCorners F j q'' ∧
      boxOfCorners F j q' ⊆ boxOfCorners F j q'' ∧
      ∀ i, sideWidth q'' i + 2 ≤ (sideWidth q i + 2) + (sideWidth q' i + 2) := by
  obtain ⟨x, hx, x', hx', hd⟩ := hw
  obtain ⟨a, ha, rfl⟩ := mem_boxOfCorners.mp hx
  obtain ⟨a', ha', rfl⟩ := mem_boxOfCorners.mp hx'
  have hcoord : ∀ i, ∃ k e : ℤ, |e| ≤ 2 ∧ a i - a' i = e + (F.period j i : ℤ) * k := by
    intro i
    have h1 : ((siteOfCoords j a : F.Site j) i - (siteOfCoords j a' : F.Site j) i).valMinAbs.natAbs ≤ 2 := by
      have := Finset.le_sup (f := fun i => (((siteOfCoords j a : F.Site j) i -
        (siteOfCoords j a' : F.Site j) i).valMinAbs).natAbs) (Finset.mem_univ i)
      exact this.trans hd
    set e := ((siteOfCoords j a : F.Site j) i - (siteOfCoords j a' : F.Site j) i).valMinAbs with he
    have h2 : ((e : ℤ) : ZMod (F.period j i)) = ((a i - a' i : ℤ) : ZMod (F.period j i)) := by
      rw [he, ZMod.coe_valMinAbs]
      simp [siteOfCoords]
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h2
    obtain ⟨k, hk⟩ := h2
    refine ⟨k, e, ?_, by linarith⟩
    rw [abs_le]
    omega
  choose k e he hae using hcoord
  let s : Fin 4 → ℤ := fun i => (F.period j i : ℤ) * k i
  let lo : Fin 4 → ℤ := fun i => min (q.1 i) (q'.1 i + s i)
  let hi : Fin 4 → ℤ := fun i => max (q.2 i) (q'.2 i + s i)
  refine ⟨(lo, hi), fun i => ?_, ?_, ?_, fun i => ?_⟩
  · have := hq i
    exact (min_le_left _ _).trans (this.trans (le_max_left _ _))
  · intro x hx
    obtain ⟨b, hb, rfl⟩ := mem_boxOfCorners.mp hx
    exact mem_boxOfCorners.mpr ⟨b, fun i => ⟨(min_le_left _ _).trans (hb i).1,
      (hb i).2.trans (le_max_left _ _)⟩, rfl⟩
  · intro x hx
    obtain ⟨b, hb, rfl⟩ := mem_boxOfCorners.mp hx
    refine mem_boxOfCorners.mpr ⟨fun i => b i + s i, fun i => ⟨?_, ?_⟩, siteOfCoords_add_period_mul b k⟩
    · exact (min_le_right _ _).trans (by linarith [(hb i).1])
    · exact le_trans (by linarith [(hb i).2]) (le_max_right _ _)
  · have h1 := ha i
    have h2 := ha' i
    have h3 := he i
    have h4 := hae i
    rw [abs_le] at h3
    simp only [sideWidth, lo, hi]
    have hs : s i = (F.period j i : ℤ) * k i := rfl
    rcases le_total (q.1 i) (q'.1 i + s i) with c1 | c1 <;>
      rcases le_total (q.2 i) (q'.2 i + s i) with c2 | c2 <;>
      simp only [min_eq_left c1, min_eq_right c1, max_eq_left c2, max_eq_right c2] <;>
      omega
theorem sideWidth_pos {q : CornerPair} (hq : ∀ i, q.1 i ≤ q.2 i) (i : Fin 4) : 0 < sideWidth q i := by
  have := hq i
  simp only [sideWidth]
  omega
theorem exists_separated_merge [∀ i, NeZero (F.period j i)] (M : ℤ) :
    ∀ (N : ℕ) (S : Finset CornerPair), S.card = N → (∀ q ∈ S, ∀ i, q.1 i ≤ q.2 i) →
      (∀ i, ∑ q ∈ S, (sideWidth q i + 2) ≤ M) →
      ∃ T : Finset CornerPair, (∀ q ∈ T, ∀ i, q.1 i ≤ q.2 i) ∧ (∀ i, ∑ q ∈ T, (sideWidth q i + 2) ≤ M) ∧
        (∀ q ∈ S, ∃ q' ∈ T, boxOfCorners F j q ⊆ boxOfCorners F j q') ∧
        ∀ q ∈ T, ∀ q' ∈ T, boxOfCorners F j q ≠ boxOfCorners F j q' →
          ¬ AreWithin 2 (boxOfCorners F j q) (boxOfCorners F j q') := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro S hcard hS hsum
    by_cases hbad : ∃ q ∈ S, ∃ q' ∈ S, boxOfCorners F j q ≠ boxOfCorners F j q' ∧
        AreWithin 2 (boxOfCorners F j q) (boxOfCorners F j q')
    · classical
      obtain ⟨q, hq, q', hq', hne, hw⟩ := hbad
      have hqq : q ≠ q' := fun h => hne (by rw [h])
      obtain ⟨q'', h1, h2, h3, h4⟩ := exists_box_merge (hS q hq) (hS q' hq') hw
      set R := (S.erase q).erase q' with hR
      have hq'R : q' ∈ S.erase q := Finset.mem_erase.mpr ⟨hqq.symm, hq'⟩
      have hcardR : R.card + 2 = S.card := by
        rw [hR, Finset.card_erase_of_mem hq'R, Finset.card_erase_of_mem hq]
        have : 2 ≤ S.card := by
          have := Finset.card_le_card (show ({q, q'} : Finset CornerPair) ⊆ S by
            intro u hu
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl <;> assumption)
          rwa [Finset.card_pair hqq] at this
        omega
      have hsplit : ∀ i, ∑ u ∈ S, (sideWidth u i + 2) =
          (sideWidth q i + 2) + ((sideWidth q' i + 2) + ∑ u ∈ R, (sideWidth u i + 2)) := by
        intro i
        have e1 := Finset.add_sum_erase (S.erase q) (fun u => sideWidth u i + 2) hq'R
        have e2 := Finset.add_sum_erase S (fun u => sideWidth u i + 2) hq
        rw [hR]
        linarith
      have hRS : ∀ u ∈ R, u ∈ S := fun u hu =>
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hu)
      have hpos : ∀ u ∈ S, ∀ i, 0 < sideWidth u i + 2 := fun u hu i => by
        have := sideWidth_pos (hS u hu) i
        omega
      have hS' : ∀ u ∈ insert q'' R, ∀ i, u.1 i ≤ u.2 i := by
        intro u hu i
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact h1 i
        · exact hS u (hRS u hu) i
      have hsum' : ∀ i, ∑ u ∈ insert q'' R, (sideWidth u i + 2) ≤ M := by
        intro i
        have hb := hsum i
        rw [hsplit i] at hb
        by_cases hin : q'' ∈ R
        · rw [Finset.insert_eq_of_mem hin]
          have := hpos q hq i
          have := hpos q' hq' i
          linarith
        · rw [Finset.sum_insert hin]
          have := h4 i
          linarith
      have hlt : (insert q'' R).card < N := by
        have := Finset.card_insert_le q'' R
        omega
      obtain ⟨T, t1, t2, t3, t4⟩ := ih _ hlt _ rfl hS' hsum'
      refine ⟨T, t1, t2, fun u hu => ?_, t4⟩
      obtain ⟨w, hw1, hw2⟩ := t3 q'' (Finset.mem_insert_self _ _)
      by_cases e1 : u = q
      · subst e1
        exact ⟨w, hw1, h2.trans hw2⟩
      · by_cases e2 : u = q'
        · subst e2
          exact ⟨w, hw1, h3.trans hw2⟩
        · exact t3 u (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨e2, Finset.mem_erase.mpr ⟨e1, hu⟩⟩))
    · push_neg at hbad
      exact ⟨S, hS, hsum, fun q hq => ⟨q, hq, subset_rfl⟩, fun q hq q' hq' hne => hbad q hq q' hq' hne⟩
theorem card_image_coord_le [∀ i, NeZero (F.period j i)] (T : Finset CornerPair)
    (hT : ∀ q ∈ T, ∀ i, q.1 i ≤ q.2 i) (i : Fin 4) :
    (((T.biUnion (boxOfCorners F j)).image fun x => x i).card : ℤ) ≤ ∑ q ∈ T, sideWidth q i := by
  classical
  have h1 : (T.biUnion (boxOfCorners F j)).image (fun x => x i) ⊆
      T.biUnion fun q => (Finset.Icc (q.1 i) (q.2 i)).image fun c : ℤ => (c : ZMod (F.period j i)) := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨q, hq, hxq⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨a, ha, rfl⟩ := mem_boxOfCorners.mp hxq
    exact Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_image.mpr
      ⟨a i, Finset.mem_Icc.mpr (ha i), rfl⟩⟩
  have h2 := (Finset.card_le_card h1).trans Finset.card_biUnion_le
  have h3 : ∀ q ∈ T, (((Finset.Icc (q.1 i) (q.2 i)).image
      fun c : ℤ => (c : ZMod (F.period j i))).card : ℤ) ≤ sideWidth q i := by
    intro q hq
    have h4 := Finset.card_image_le (s := Finset.Icc (q.1 i) (q.2 i))
      (f := fun c : ℤ => (c : ZMod (F.period j i)))
    rw [Int.card_Icc] at h4
    have h5 := hT q hq i
    simp only [sideWidth]
    omega
  calc _ ≤ ((∑ q ∈ T, ((Finset.Icc (q.1 i) (q.2 i)).image
          fun c : ℤ => (c : ZMod (F.period j i))).card : ℕ) : ℤ) := by exact_mod_cast h2
    _ = ∑ q ∈ T, (((Finset.Icc (q.1 i) (q.2 i)).image
          fun c : ℤ => (c : ZMod (F.period j i))).card : ℤ) := by push_cast; rfl
    _ ≤ _ := Finset.sum_le_sum h3
theorem thicken_boxSites (m : ℕ) (lo hi : Fin 4 → ℤ) (hlo : ∀ i, lo i ≤ hi i) :
    thicken m (boxSites j lo hi : Finset (F.Site j)) =
      boxOfCorners F j (fun i => lo i - m, fun i => hi i + m) := by apply _root_.YangMills.Construction.CornerBoxes.thicken_boxSites <;> assumption
end BoxMerging
section BaseChoice
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
theorem exists_eq_lumpOf_of_mem_hotLumps {s : ℝ} {X : Finset ((stepBlockFrame ℓ.side n).Site 0)}
    {W : (stepBlockFrame ℓ.side n).GaugeField 0}
    {l : Finset ((stepBlockFrame ℓ.side n).Site 0)} (hl : l ∈ hotLumps ℓ.grid s X W) :
    ∃ x : (stepBlockFrame ℓ.side n).Site 0, l = lumpOf ℓ.grid x := by
  classical
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hp
  exact ⟨x, rfl⟩
theorem exists_corners_lumpCollar (hfit : ℓ.Admissible) (x : (stepBlockFrame ℓ.side n).Site 0) :
    ∃ q : CornerPair, (∀ i, q.1 i ≤ q.2 i) ∧
      lumpCollar (lumpOf ℓ.grid x) = boxOfCorners (stepBlockFrame ℓ.side n) 0 q ∧
      ∀ i, sideWidth q i + 2 ≤ 11 * 2 ^ 12 := by
  have hLpos : 0 < ℓ.side := by have := hfit.L_ge; omega
  let c : Fin 4 → ℤ := fun i => siteCoords x i
  let lo : Fin 4 → ℤ := fun i =>
    c i - offsetFromCentre ℓ.side (c i) + ℓ.grid.lower (offsetFromCentre ℓ.side (c i))
  let hi : Fin 4 → ℤ := fun i =>
    c i - offsetFromCentre ℓ.side (c i) + ℓ.grid.upper (offsetFromCentre ℓ.side (c i))
  have hb : ∀ i, lo i ≤ hi i ∧ hi i - lo i + 1 < 2 ^ 15 := by
    intro i
    obtain ⟨_, ho⟩ := offsetFromCentre_spec hLpos hfit.L_odd (c i)
    obtain ⟨b1, b2, b3, b4⟩ := ℓ.grid.mem_interval _ ho
    have hs := ℓ.grid.interval_length _ ho
    simp only [lo, hi]
    constructor <;> linarith [hs.2]
  have hw : lumpRange + 2 = 4098 := rfl
  refine ⟨(fun i => lo i - ((lumpRange + 2 : ℕ) : ℤ), fun i => hi i + ((lumpRange + 2 : ℕ) : ℤ)),
    fun i => ?_, thicken_boxSites _ lo hi fun i => (hb i).1, fun i => ?_⟩
  · have := (hb i).1
    simp only [hw]
    omega
  · have := (hb i).2
    simp only [sideWidth, hw]
    omega
theorem exists_base_avoiding_boxes (hfit : ℓ.Admissible) (hLam : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side)
    (W : (stepBlockFrame ℓ.side n).GaugeField 0) (y : (stepBlockFrame ℓ.side n).Cell)
    (hcr : ¬ IsCrowded ℓ.baseDepth
      (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W) y) :
    ∃ c ∈ sitesBelow 0 y, ∀ B ∈ excludedBoxes ℓ.baseDepth
      (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W) y,
      ∀ x ∈ B, ∀ i, x i ≠ c i := by
  classical
  set h := hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W with hh
  set Ls := nearbyLumps h y with hLs
  have hcard : Ls.card < ℓ.baseDepth := not_le.mp hcr
  have hrep : ∀ l ∈ Ls, ∃ q : CornerPair, (∀ i, q.1 i ≤ q.2 i) ∧
      lumpCollar l = boxOfCorners (stepBlockFrame ℓ.side n) 0 q ∧
      ∀ i, sideWidth q i + 2 ≤ 11 * 2 ^ 12 := by
    intro l hl
    obtain ⟨x, rfl⟩ := exists_eq_lumpOf_of_mem_hotLumps (Finset.mem_filter.mp hl).1
    exact exists_corners_lumpCollar hfit x
  choose! r hr1 hr2 hr3 using hrep
  set S := Ls.image r with hS
  have hSord : ∀ q ∈ S, ∀ i, q.1 i ≤ q.2 i := by
    intro q hq
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
    exact hr1 l hl
  have hsum : ∀ i, ∑ q ∈ S, (sideWidth q i + 2) ≤ ((11 * 2 ^ 12 * ℓ.baseDepth : ℕ) : ℤ) := by
    intro i
    have h1 : ∀ q ∈ S, sideWidth q i + 2 ≤ 11 * 2 ^ 12 := by
      intro q hq
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
      exact hr3 l hl i
    have h2 := Finset.sum_le_card_nsmul _ _ _ h1
    have h3 : S.card ≤ ℓ.baseDepth := Finset.card_image_le.trans hcard.le
    rw [nsmul_eq_mul] at h2
    have h4 : (S.card : ℤ) ≤ ℓ.baseDepth := by exact_mod_cast h3
    push_cast
    nlinarith
  obtain ⟨T, t1, t2, t3, t4⟩ :=
    exists_separated_merge (F := stepBlockFrame ℓ.side n) (j := 0) _ _ S rfl hSord hsum
  have hLam' : ((11 * 2 ^ 12 * ℓ.baseDepth : ℕ) : ℤ) < ℓ.side := by exact_mod_cast hLam
  have hcover : IsSeparatedCover (Ls.image lumpCollar)
      (T.image (boxOfCorners (stepBlockFrame ℓ.side n) 0)) := by
    refine ⟨fun B hB => ?_, fun l hl => ?_, fun B hB B' hB' hne => ?_⟩
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
      refine ⟨q.1, q.2, fun i => ⟨t1 q hq i, ?_⟩, rfl⟩
      have h1 := Finset.single_le_sum (f := fun u : CornerPair => sideWidth u i + 2)
        (fun u hu => by
          have := sideWidth_pos (t1 u hu) i
          show 0 ≤ sideWidth u i + 2
          omega) hq
      have h2 := t2 i
      simp only [sideWidth] at h1 h2 ⊢
      have hL : (stepBlockFrame ℓ.side n).blockSide = ℓ.side := rfl
      rw [hL]
      omega
    · obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨q', hq', hsub⟩ := t3 (r l₀) (Finset.mem_image_of_mem _ hl₀)
      exact ⟨_, Finset.mem_image_of_mem _ hq', by rw [hr2 l₀ hl₀]; exact hsub⟩
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hB'
      exact t4 q hq q' hq' hne
  have hin : ∀ B ∈ excludedBoxes ℓ.baseDepth h y, ∀ x ∈ B,
      x ∈ T.biUnion (boxOfCorners (stepBlockFrame ℓ.side n) 0) := by
    intro B hB x hx
    unfold excludedBoxes at hB
    split_ifs at hB with h0
    · simp at hB
    unfold mergedBoxes at hB
    split_ifs at hB with hex
    · obtain ⟨B', hB', hsub⟩ := hex.choose_spec.2 _ hcover B hB
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB'
      exact Finset.mem_biUnion.mpr ⟨q, hq, hsub hx⟩
    · simp at hB
  have hper : ∀ i, (ℓ.side : ℤ) ≤ ((stepBlockFrame ℓ.side n).period 0 i : ℤ) := by
    intro i
    have h1 : (stepBlockFrame ℓ.side n).period 0 i = n * ℓ.side ^ 1 := rfl
    have h2 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    rw [h1, pow_one]
    exact_mod_cast Nat.le_mul_of_pos_left _ h2
  obtain ⟨k, hk⟩ := hfit.L_odd
  have hhalf : ((ℓ.side : ℤ) - 1) / 2 = k := by
    rw [hk]
    push_cast
    omega
  have hchoice : ∀ i, ∃ c : ℤ, c ∈ Finset.Icc (-(((ℓ.side : ℤ) - 1) / 2)) (((ℓ.side : ℤ) - 1) / 2) ∧
      (((ℓ.side : ℤ) * siteCoords y i + c : ℤ) : ZMod ((stepBlockFrame ℓ.side n).period 0 i)) ∉
        (T.biUnion (boxOfCorners (stepBlockFrame ℓ.side n) 0)).image fun x => x i := by
    intro i
    have hp := card_image_coord_le (F := stepBlockFrame ℓ.side n) (j := 0) T t1 i
    have hs2 : ∑ q ∈ T, sideWidth q i ≤ ∑ q ∈ T, (sideWidth q i + 2) :=
      Finset.sum_le_sum fun q _ => by omega
    have hs3 := t2 i
    have hlt : ((T.biUnion (boxOfCorners (stepBlockFrame ℓ.side n) 0)).image fun x => x i).card
        < ℓ.side := by
      have : (((T.biUnion (boxOfCorners (stepBlockFrame ℓ.side n) 0)).image fun x => x i).card : ℤ)
          < ℓ.side := by
        linarith
      exact_mod_cast this
    set I := Finset.Icc (-(((ℓ.side : ℤ) - 1) / 2)) (((ℓ.side : ℤ) - 1) / 2) with hI
    have hinj : Set.InjOn (fun c : ℤ => (((ℓ.side : ℤ) * siteCoords y i + c : ℤ) :
        ZMod ((stepBlockFrame ℓ.side n).period 0 i))) I := by
      intro c hc c' hc' he
      simp only at he
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at he
      have h1 := Finset.mem_Icc.mp (Finset.mem_coe.mp hc)
      have h2 := Finset.mem_Icc.mp (Finset.mem_coe.mp hc')
      have h3 : ((stepBlockFrame ℓ.side n).period 0 i : ℤ) ∣ c' - c := by
        have : (ℓ.side : ℤ) * siteCoords y i + c' - ((ℓ.side : ℤ) * siteCoords y i + c) = c' - c := by
          ring
        rwa [this] at he
      have h4 := hper i
      have h5 := Int.eq_zero_of_abs_lt_dvd h3 (by
        rw [abs_lt]
        rw [hhalf] at h1 h2
        have : (ℓ.side : ℤ) = 2 * k + 1 := by rw [hk]; push_cast; ring
        constructor <;> omega)
      omega
    have hcardI : ((I.image fun c : ℤ => (((ℓ.side : ℤ) * siteCoords y i + c : ℤ) :
        ZMod ((stepBlockFrame ℓ.side n).period 0 i)))).card = ℓ.side := by
      rw [Finset.card_image_of_injOn hinj, hI, Int.card_Icc, hhalf, hk]
      push_cast
      omega
    have hlt' : ((T.biUnion (boxOfCorners (stepBlockFrame ℓ.side n) 0)).image fun x => x i).card <
        (I.image fun c : ℤ => (((ℓ.side : ℤ) * siteCoords y i + c : ℤ) :
          ZMod ((stepBlockFrame ℓ.side n).period 0 i))).card := by
      rw [hcardI]
      exact hlt
    obtain ⟨e, he1, he2⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp he1
    exact ⟨c, hc, he2⟩
  choose c hc1 hc2 using hchoice
  refine ⟨siteOfCoords 0 fun i => (ℓ.side : ℤ) * siteCoords y i + c i, ?_, fun B hB x hx i he => ?_⟩
  · unfold sitesBelow
    refine Finset.mem_image.mpr ⟨c, Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩
    · have hL : (((stepBlockFrame ℓ.side n).blockSide ^ ((stepBlockFrame ℓ.side n).top - 0) : ℕ) : ℤ)
          = (ℓ.side : ℤ) := by
        show ((ℓ.side ^ 1 : ℕ) : ℤ) = _
        simp
      rw [hL]
      exact hc1 i
    · have hL : ((stepBlockFrame ℓ.side n).blockSide : ℤ) ^ ((stepBlockFrame ℓ.side n).top - 0)
          = (ℓ.side : ℤ) := by
        show ((ℓ.side : ℤ)) ^ 1 = _
        simp
      rw [hL]
  · refine hc2 i (Finset.mem_image.mpr ⟨x, hin B hB x hx, ?_⟩)
    rw [he]
    rfl
end BaseChoice
theorem baseChoices_nonempty : BaseChoicesNonempty := by
  classical
  intro ℓ hfit hLam n _ W
  set h := hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W with hh
  have hch : ∀ y : (stepBlockFrame ℓ.side n).Cell, ∃ c : (stepBlockFrame ℓ.side n).Site 0,
      ((nearbyLumps h y = ∅ ∨ IsCrowded ℓ.baseDepth h y) → c = cellCentre 0 y) ∧
      (¬ (nearbyLumps h y = ∅ ∨ IsCrowded ℓ.baseDepth h y) → c ∈ sitesBelow 0 y ∧
        ∀ B ∈ excludedBoxes ℓ.baseDepth h y, ∀ x ∈ B, ∀ i, x i ≠ c i) := by
    intro y
    by_cases hc : nearbyLumps h y = ∅ ∨ IsCrowded ℓ.baseDepth h y
    · exact ⟨cellCentre 0 y, fun _ => rfl, fun hn => absurd hc hn⟩
    · have hnc : ¬ IsCrowded ℓ.baseDepth h y := fun hcr => hc (Or.inr hcr)
      obtain ⟨c, h1, h2⟩ := exists_base_avoiding_boxes hfit hLam W y hnc
      exact ⟨c, fun hy => absurd hy hc, fun _ => ⟨h1, h2⟩⟩
  choose b hb using hch
  exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩
end YangMills.Construction.TorusLumps
end
