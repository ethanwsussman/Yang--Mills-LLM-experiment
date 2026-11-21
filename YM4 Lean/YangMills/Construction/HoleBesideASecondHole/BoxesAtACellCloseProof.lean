import YangMills.Construction.HoleBesideASecondHole.BoxesAtACellClose
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LumpContours
open YangMills.Construction.BlockAverages YangMills.Construction.CornerBoxes
namespace ExcludedBoxes
variable {F : BlockFrame} {j : ℕ}
theorem exists_merged_box {q q' : CornerPair} (hq : ∀ i, q.1 i ≤ q.2 i)
    (hq' : ∀ i, q'.1 i ≤ q'.2 i) [∀ i, NeZero (F.period j i)]
    (hw : AreWithin 2 (boxOfCorners F j q) (boxOfCorners F j q')) :
    ∃ q'' : CornerPair, (∀ i, q''.1 i ≤ q''.2 i) ∧ boxOfCorners F j q ⊆ boxOfCorners F j q'' ∧
      boxOfCorners F j q' ⊆ boxOfCorners F j q'' ∧
      maxSideWidth q'' + 2 ≤ (maxSideWidth q + 2) + (maxSideWidth q' + 2) ∧
      ∀ lo hi : Fin 4 → ℤ, (∀ i, hi i - lo i + 3 ≤ F.period j i) → boxOfCorners F j q ⊆ boxSites j lo hi →
        boxOfCorners F j q' ⊆ boxSites j lo hi → boxOfCorners F j q'' ⊆ boxSites j lo hi := by
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
  refine ⟨(lo, hi), fun i => ?_, ?_, ?_, ?_, ?_⟩
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
  · have : maxSideWidth (lo, hi) ≤ maxSideWidth q + maxSideWidth q' + 2 := by
      refine Finset.sup_le fun i _ => ?_
      have h1 := ha i
      have h2 := ha' i
      have h3 := he i
      have h4 := hae i
      have h5 := sideWidth_le_maxSideWidth q i
      have h6 := sideWidth_le_maxSideWidth q' i
      rw [abs_le] at h3
      simp only [sideWidth, lo, hi] at h5 h6 ⊢
      have hs : s i = (F.period j i : ℤ) * k i := rfl
      rcases le_total (q.1 i) (q'.1 i + s i) with c1 | c1 <;>
        rcases le_total (q.2 i) (q'.2 i + s i) with c2 | c2 <;>
        simp only [min_eq_left c1, min_eq_right c1, max_eq_left c2, max_eq_right c2] <;>
        omega
    omega
  · intro lo' hi' hgap h₁ h₂
    have step : ∀ i, ∃ m : ℤ, lo' i + m * F.period j i ≤ lo i ∧ hi i ≤ hi' i + m * F.period j i := by
      intro i
      have hg : hi' i - lo' i + 2 ≤ F.period j i := by linarith [hgap i]
      obtain ⟨m₁, m₁a, m₁b⟩ := exists_period_translate_of_interval (P := F.period j i) (q.1 i) (q.2 i)
        (lo' i) (hi' i) (hq i) hg
        fun c c₁ c₂ => exists_residue_of_boxOfCorners_subset hq h₁ i c c₁ c₂
      obtain ⟨m₂, m₂a, m₂b⟩ := exists_period_translate_of_interval (P := F.period j i) (q'.1 i + s i)
        (q'.2 i + s i) (lo' i) (hi' i)
        (by linarith [hq' i]) hg fun c c₁ c₂ => by
          obtain ⟨b, b₁, b₂, b₃⟩ := exists_residue_of_boxOfCorners_subset hq' h₂ i (c - s i)
            (by linarith) (by linarith)
          refine ⟨b, b₁, b₂, ?_⟩
          rw [← b₃]
          simp [s]
      have h1 := ha i
      have h2 := ha' i
      have h3 := he i
      have h4 := hae i
      rw [abs_le] at h3
      have hs : s i = (F.period j i : ℤ) * k i := rfl
      have hP := hgap i
      have hmm : m₁ = m₂ := by
        rcases lt_trichotomy m₁ m₂ with c | c | c
        · have : (m₁ + 1) * (F.period j i : ℤ) ≤ m₂ * F.period j i :=
            mul_le_mul_of_nonneg_right (by omega) (by positivity)
          nlinarith
        · exact c
        · have : (m₂ + 1) * (F.period j i : ℤ) ≤ m₁ * F.period j i :=
            mul_le_mul_of_nonneg_right (by omega) (by positivity)
          nlinarith
      subst hmm
      refine ⟨m₁, ?_, ?_⟩
      · exact le_min m₁a m₂a
      · exact max_le m₁b m₂b
    choose m hm using step
    exact boxOfCorners_subset_of_translate (q := (lo, hi)) (k := m) hm
def IsForcedBox (seeds : Finset (Finset (F.Site j))) (q : CornerPair) : Prop :=
  ∀ Z', IsSeparatedCover (seeds.filter fun l => l ⊆ boxOfCorners F j q) Z' → ∃ B ∈ Z', boxOfCorners F j q ⊆ B
theorem isSeparatedCover_of_subset {seeds seeds' Z' : Finset (Finset (F.Site j))} (h : seeds ⊆ seeds')
    (hc : IsSeparatedCover seeds' Z') : IsSeparatedCover seeds Z' :=
  ⟨hc.1, fun l hl => hc.2.1 l (h hl), hc.2.2⟩
theorem areWithin_mono {A A' B B' : Finset (F.Site j)} (hA : A ⊆ A') (hB : B ⊆ B') (h : AreWithin 2 A B) :
    AreWithin 2 A' B' := by
  obtain ⟨x, hx, y, hy, hd⟩ := h
  exact ⟨x, hA hx, y, hB hy, hd⟩
theorem isForcedBox_merge [∀ i, NeZero (F.period j i)] {seeds : Finset (Finset (F.Site j))}
    {q q' q'' : CornerPair}
    (hL : ∀ i, (F.blockSide : ℤ) + 1 ≤ F.period j i)
    (h₁ : IsForcedBox seeds q) (h₂ : IsForcedBox seeds q')
    (hs₁ : boxOfCorners F j q ⊆ boxOfCorners F j q'') (hs₂ : boxOfCorners F j q' ⊆ boxOfCorners F j q'')
    (hw : AreWithin 2 (boxOfCorners F j q) (boxOfCorners F j q'))
    (hmin : ∀ lo hi : Fin 4 → ℤ, (∀ i, hi i - lo i + 3 ≤ F.period j i) → boxOfCorners F j q ⊆ boxSites j lo hi →
        boxOfCorners F j q' ⊆ boxSites j lo hi → boxOfCorners F j q'' ⊆ boxSites j lo hi) :
    IsForcedBox seeds q'' := by
  classical
  intro Z' hc
  obtain ⟨B, hB, hqB⟩ := h₁ Z' (isSeparatedCover_of_subset (fun l hl => by
    obtain ⟨l₁, l₂⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_filter.mpr ⟨l₁, l₂.trans hs₁⟩) hc)
  obtain ⟨B', hB', hqB'⟩ := h₂ Z' (isSeparatedCover_of_subset (fun l hl => by
    obtain ⟨l₁, l₂⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_filter.mpr ⟨l₁, l₂.trans hs₂⟩) hc)
  have hBB : B = B' := by
    by_contra hne
    exact hc.2.2 B hB B' hB' hne (areWithin_mono hqB hqB' hw)
  subst hBB
  refine ⟨B, hB, ?_⟩
  obtain ⟨lo, hi, hbox, rfl⟩ := hc.1 B hB
  refine hmin lo hi (fun i => ?_) hqB hqB'
  have := (hbox i).2
  have := hL i
  omega
theorem exists_separated_family [∀ i, NeZero (F.period j i)] (seeds : Finset (Finset (F.Site j))) (M : ℕ)
    (hL : ∀ i, (F.blockSide : ℤ) + 1 ≤ F.period j i) :
    ∀ (N : ℕ) (S : Finset CornerPair), S.card = N → (∀ q ∈ S, ∀ i, q.1 i ≤ q.2 i) →
      (∑ q ∈ S, (maxSideWidth q + 2) ≤ M) → (∀ q ∈ S, IsForcedBox seeds q) →
      ∃ T : Finset CornerPair, (∀ q ∈ T, ∀ i, q.1 i ≤ q.2 i) ∧ (∑ q ∈ T, (maxSideWidth q + 2) ≤ M) ∧
        (∀ q ∈ S, ∃ q' ∈ T, boxOfCorners F j q ⊆ boxOfCorners F j q') ∧ (∀ q ∈ T, IsForcedBox seeds q) ∧
        ∀ q ∈ T, ∀ q' ∈ T, boxOfCorners F j q ≠ boxOfCorners F j q' →
          ¬ AreWithin 2 (boxOfCorners F j q) (boxOfCorners F j q') := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro S hcard hS hsum hold
    by_cases hbad : ∃ q ∈ S, ∃ q' ∈ S, boxOfCorners F j q ≠ boxOfCorners F j q' ∧
        AreWithin 2 (boxOfCorners F j q) (boxOfCorners F j q')
    · classical
      obtain ⟨q, hq, q', hq', hne, hw⟩ := hbad
      have hqq : q ≠ q' := fun h => hne (by rw [h])
      obtain ⟨q'', h1, h2, h3, h4, h5⟩ := exists_merged_box (hS q hq) (hS q' hq') hw
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
      have hsplit : ∑ u ∈ S, (maxSideWidth u + 2) =
          (maxSideWidth q + 2) + ((maxSideWidth q' + 2) + ∑ u ∈ R, (maxSideWidth u + 2)) := by
        have e1 := Finset.add_sum_erase (S.erase q) (fun u => maxSideWidth u + 2) hq'R
        have e2 := Finset.add_sum_erase S (fun u => maxSideWidth u + 2) hq
        rw [hR]
        omega
      have hRS : ∀ u ∈ R, u ∈ S := fun u hu =>
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hu)
      have hS' : ∀ u ∈ insert q'' R, ∀ i, u.1 i ≤ u.2 i := by
        intro u hu i
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact h1 i
        · exact hS u (hRS u hu) i
      have hsum' : ∑ u ∈ insert q'' R, (maxSideWidth u + 2) ≤ M := by
        by_cases hin : q'' ∈ R
        · rw [Finset.insert_eq_of_mem hin]
          omega
        · rw [Finset.sum_insert hin]
          omega
      have hold' : ∀ u ∈ insert q'' R, IsForcedBox seeds u := by
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact isForcedBox_merge hL (hold q hq) (hold q' hq') h2 h3 hw h5
        · exact hold u (hRS u hu)
      have hlt : (insert q'' R).card < N := by
        have := Finset.card_insert_le q'' R
        omega
      obtain ⟨T, t1, t2, t3, t4, t5⟩ := ih _ hlt (insert q'' R) rfl hS' hsum' hold'
      refine ⟨T, t1, t2, fun u hu => ?_, t4, t5⟩
      by_cases e1 : u = q
      · subst e1
        obtain ⟨v, hv, hs⟩ := t3 q'' (Finset.mem_insert_self _ _)
        exact ⟨v, hv, h2.trans hs⟩
      by_cases e2 : u = q'
      · subst e2
        obtain ⟨v, hv, hs⟩ := t3 q'' (Finset.mem_insert_self _ _)
        exact ⟨v, hv, h3.trans hs⟩
      exact t3 u (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨e2, Finset.mem_erase.mpr ⟨e1, hu⟩⟩))
    · refine ⟨S, hS, hsum, fun q hq => ⟨q, hq, subset_rfl⟩, hold,
        fun q hq q' hq' hne hw => hbad ⟨q, hq, q', hq', hne, hw⟩⟩
theorem nonempty_of_isSmallBox {B : Finset (F.Site j)} (hB : IsSmallBox F B) : B.Nonempty := by
  obtain ⟨lo, hi, h, rfl⟩ := hB
  exact ⟨siteOfCoords j lo, (mem_boxOfCorners (q := (lo, hi))).mpr ⟨lo, fun i => ⟨le_rfl, (h i).1⟩, rfl⟩⟩
theorem areWithin_of_subset [∀ i, NeZero (F.period j i)] {B B' : Finset (F.Site j)} (hB : B.Nonempty)
    (h : B ⊆ B') : AreWithin 2 B B' := by
  obtain ⟨x, hx⟩ := hB
  refine ⟨x, hx, x, h hx, ?_⟩
  simp [supDist]
theorem leastSeparatedCover_subset [∀ i, NeZero (F.period j i)] {seeds Z Z₂ : Finset (Finset (F.Site j))}
    (h : IsLeastSeparatedCover seeds Z) (h₂ : IsLeastSeparatedCover seeds Z₂) : Z ⊆ Z₂ := by
  intro B hB
  obtain ⟨B₂, hB₂, s₁⟩ := h.2 Z₂ h₂.1 B hB
  obtain ⟨B₃, hB₃, s₂⟩ := h₂.2 Z h.1 B₂ hB₂
  have hne := nonempty_of_isSmallBox (h.1.1 B hB)
  have e : B = B₃ := by
    by_contra hn
    exact h.1.2.2 B hB B₃ hB₃ hn (areWithin_of_subset hne (s₁.trans s₂))
  have : B = B₂ := le_antisymm s₁ (e ▸ s₂)
  rwa [this]
theorem sum_image_le_sum {α β : Type} [DecidableEq α] [DecidableEq β] (T : Finset α) (f : α → β)
    (g : β → ℕ) : ∑ b ∈ T.image f, g b ≤ ∑ a ∈ T, g (f a) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.image_insert, Finset.sum_insert ha]
    by_cases hm : f a ∈ s.image f
    · rw [Finset.insert_eq_of_mem hm]
      omega
    · rw [Finset.sum_insert hm]
      omega
end ExcludedBoxes
open ExcludedBoxes in
theorem excludedBoxesAtUncrowdedCell_holds : ExcludedBoxesAtUncrowdedCell := by
  classical
  intro F g J₀ h y hodd hside hLam hlump hcr
  have hLpos : 0 < F.blockSide := hodd.pos
  have hper : ∀ i, F.period F.depth i = F.extent i * F.blockSide := by
    intro i
    simp [BlockFrame.period]
  haveI : ∀ i, NeZero (F.period F.depth i) := fun i => ⟨by
    rw [hper]
    have := hside i
    exact Nat.mul_ne_zero (by omega) hLpos.ne'⟩
  have hL : ∀ i, (F.blockSide : ℤ) + 1 ≤ F.period F.depth i := by
    intro i
    rw [hper]
    have h2 : 2 * F.blockSide ≤ F.extent i * F.blockSide := Nat.mul_le_mul_right _ (hside i)
    have : F.blockSide + 1 ≤ F.extent i * F.blockSide := by omega
    exact_mod_cast this
  set Ls := nearbyLumps h y with hLs
  have hcard : Ls.card < J₀ := not_le.mp hcr
  have hrep : ∀ l ∈ Ls, ∃ q : CornerPair, (∀ i, q.1 i ≤ q.2 i) ∧ lumpCollar l = boxOfCorners F F.depth q ∧
      maxSideWidth q + 2 ≤ 11 * 2 ^ 12 := by
    intro l hl
    obtain ⟨x, rfl⟩ := hlump l (Finset.mem_filter.mp hl).1
    exact lumpCollar_eq_box hLpos hodd g x
  choose! r hr1 hr2 hr3 using hrep
  set seeds := lumpSeeds h y with hseeds
  set S := Ls.image r with hS
  have hSord : ∀ q ∈ S, ∀ i, q.1 i ≤ q.2 i := by
    intro q hq
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
    exact hr1 l hl
  have hsum : ∑ q ∈ S, (maxSideWidth q + 2) ≤ 11 * 2 ^ 12 * J₀ := by
    have h1 : ∀ q ∈ S, maxSideWidth q + 2 ≤ 11 * 2 ^ 12 := by
      intro q hq
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
      exact hr3 l hl
    have h2 := Finset.sum_le_card_nsmul _ _ _ h1
    have h3 : S.card ≤ J₀ := Finset.card_image_le.trans hcard.le
    rw [smul_eq_mul] at h2
    nlinarith
  have hold : ∀ q ∈ S, IsForcedBox seeds q := by
    intro q hq Z' hc
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
    have := hc.2.1 (lumpCollar l) (Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem _ hl, (hr2 l hl).le⟩)
    rwa [hr2 l hl] at this
  obtain ⟨T, t1, t2, t3, t4, t5⟩ := exists_separated_family seeds _ hL _ S rfl hSord hsum hold
  have hlt : ∀ q ∈ T, maxSideWidth q + 2 < F.blockSide + 2 := by
    intro q hq
    have h1 := Finset.single_le_sum (f := fun u : CornerPair => maxSideWidth u + 2)
      (fun u _ => Nat.zero_le _) hq
    omega
  have hlam : ∀ q ∈ T, maxSideWidth q ≤ 11 * 2 ^ 12 * J₀ := by
    intro q hq
    have h1 := Finset.single_le_sum (f := fun u : CornerPair => maxSideWidth u + 2)
      (fun u _ => Nat.zero_le _) hq
    omega
  have hcover : IsSeparatedCover seeds (T.image (boxOfCorners F F.depth)) := by
    refine ⟨fun B hB => ?_, fun l hl => ?_, fun B hB B' hB' hne => ?_⟩
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
      refine ⟨q.1, q.2, fun i => ⟨t1 q hq i, ?_⟩, rfl⟩
      have h1 := sideWidth_le_maxSideWidth q i
      have h2 := hlt q hq
      simp only [sideWidth] at h1
      omega
    · obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨q', hq', hsub⟩ := t3 (r l₀) (Finset.mem_image_of_mem _ hl₀)
      exact ⟨_, Finset.mem_image_of_mem _ hq', by rw [hr2 l₀ hl₀]; exact hsub⟩
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hB'
      exact t5 q hq q' hq' hne
  have hleast : IsLeastSeparatedCover seeds (T.image (boxOfCorners F F.depth)) := by
    refine ⟨hcover, fun Z' hZ' B hB => ?_⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
    exact t4 q hq Z' (isSeparatedCover_of_subset (Finset.filter_subset _ _) hZ')
  have hZ : excludedBoxes J₀ h y = T.image (boxOfCorners F F.depth) := by
    unfold excludedBoxes
    rw [if_neg hcr]
    unfold mergedBoxes
    have hex : ∃ Z, IsLeastSeparatedCover ((nearbyLumps h y).image lumpCollar) Z := ⟨_, hleast⟩
    rw [dif_pos hex]
    exact le_antisymm (leastSeparatedCover_subset hex.choose_spec hleast)
      (leastSeparatedCover_subset hleast hex.choose_spec)
  rw [hZ]
  refine ⟨hleast, ?_, fun Z hZ' => ?_, fun Z hZ' Z' hc => ?_⟩
  · refine (sum_image_le_sum T _ _).trans (le_trans (Finset.sum_le_sum fun q hq => ?_) t2)
    have := largestSide_boxOfCorners_le (F := F) (j := F.depth) q (t1 q hq)
    omega
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hZ'
    refine ⟨q.1, q.2, rfl, fun i => ⟨t1 q hq i, ?_⟩⟩
    have h1 := sideWidth_le_maxSideWidth q i
    have h2 := hlam q hq
    simp only [sideWidth] at h1
    omega
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hZ'
    exact t4 q hq Z' hc
end YangMills.Construction.LumpContours
end
