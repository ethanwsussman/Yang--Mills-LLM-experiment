import YangMills.Construction.ClusterExpansionOfAStep.LumpsAreFibres
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open BlockAverages LumpContours TorusFields
section Offsets
variable {n : ℕ} [NeZero n]
theorem int_eq_of_zmod_cast_eq {a b : ℤ} (h : (a : ZMod n) = b) (hab : |a - b| < n) : a = b := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  have hdvd : ((n : ℕ) : ℤ) ∣ a - b := by
    have := dvd_neg.mpr h
    simpa using this
  have := Int.eq_zero_of_abs_lt_dvd hdvd hab
  linarith
theorem eq_of_siteOfInt_eq {a b : Fin 4 → ℤ} (h : (siteOfInt a : TorusSite n) = siteOfInt b)
    (hab : ∀ i, |a i - b i| < n) : a = b := by
  funext i
  exact int_eq_of_zmod_cast_eq (congrFun h i) (hab i)
theorem unitStep_eq_siteOfInt (i : Fin 4) : TorusFields.unitStep n i = siteOfInt (Pi.single i 1) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [siteOfInt, TorusFields.unitStep]
  · simp [siteOfInt, TorusFields.unitStep, hk]
theorem add_siteOfInt_add (y : TorusSite n) (a b : Fin 4 → ℤ) :
    y + siteOfInt (a + b) = y + siteOfInt a + siteOfInt b := by
  rw [siteOfInt_add, add_assoc]
def plaquetteOffsets (μ ν : Fin 4) : List (Fin 4 → ℤ) :=
  [0, Pi.single μ 1, Pi.single ν 1, Pi.single μ 1 + Pi.single ν 1]
theorem siteOfInt_zero_offset : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite n) = 0 := by
  funext i
  simp [siteOfInt]
theorem mem_plaquetteVertices_iff_offset (x z : TorusSite n) (μ ν : Fin 4) :
    z ∈ plaquetteVertices x μ ν ↔ ∃ d ∈ plaquetteOffsets μ ν, z = x + siteOfInt d := by
  simp only [plaquetteVertices, plaquetteOffsets, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, siteOfInt_zero_offset, add_zero, siteOfInt_add, unitStep_eq_siteOfInt, add_assoc]
theorem abs_le_two_of_mem_plaquetteOffsets {μ ν : Fin 4} {d : Fin 4 → ℤ} (hd : d ∈ plaquetteOffsets μ ν)
    (i : Fin 4) : |d i| ≤ 2 := by
  have h1 : ∀ k : Fin 4, |(Pi.single k 1 : Fin 4 → ℤ) i| ≤ 1 := by
    intro k
    by_cases hk : i = k
    · subst hk
      simp
    · simp [hk]
  simp only [plaquetteOffsets, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · simp
  · exact (h1 μ).trans (by norm_num)
  · exact (h1 ν).trans (by norm_num)
  · simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans (by linarith [h1 μ, h1 ν])
theorem offsetInBox_add_of_ball_subset {y z : TorusSite n} {a : Fin 4 → ℤ} {m R : ℕ}
    {S : Finset (TorusSite n)} (hn : 2 * m + 2 < n)
    (hS : ∀ s ∈ S, ∃ h, OffsetInBox m h ∧ s = y + siteOfInt h) (ha : OffsetInBox m a)
    (hz : z = y + siteOfInt a) (hball : ∀ e : Fin 4 → ℤ, (∀ i, |e i| ≤ R) → z + siteOfInt e ∈ S) :
    ∀ e : Fin 4 → ℤ, (∀ i, |e i| ≤ R) → OffsetInBox m (a + e) := by
  have key : ∀ (N : ℕ) (e : Fin 4 → ℤ), ∑ i, (e i).natAbs = N → (∀ i, |e i| ≤ R) →
      OffsetInBox m (a + e) := by
    intro N
    induction N with
    | zero =>
      intro e he _
      have h0 : e = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff.mp he) i (Finset.mem_univ i)
        simpa using this
      simpa [h0] using ha
    | succ N ih =>
      intro e he hR
      have hne : ∃ i, e i ≠ 0 := by
        by_contra hc
        push Not at hc
        simp [hc] at he
      obtain ⟨i, hi⟩ := hne
      let e' : Fin 4 → ℤ := Function.update e i (e i - Int.sign (e i))
      have hsign : (e i - Int.sign (e i)).natAbs + 1 = (e i).natAbs := by
        rcases lt_or_gt_of_ne hi with h | h
        · rw [Int.sign_eq_neg_one_of_neg h]
          omega
        · rw [Int.sign_eq_one_of_pos h]
          omega
      have hsum : ∑ j, (e' j).natAbs = N := by
        have h1 : ∑ j, (e j).natAbs = (e i).natAbs + ∑ j ∈ Finset.univ.erase i, (e j).natAbs :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
        have h2 : ∑ j, (e' j).natAbs = (e' i).natAbs + ∑ j ∈ Finset.univ.erase i, (e' j).natAbs :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
        have h3 : ∑ j ∈ Finset.univ.erase i, (e' j).natAbs = ∑ j ∈ Finset.univ.erase i, (e j).natAbs :=
          Finset.sum_congr rfl fun j hj => by
            simp [e', Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        have h4 : (e' i).natAbs = (e i - Int.sign (e i)).natAbs := by simp [e']
        omega
      have hR' : ∀ j, |e' j| ≤ R := by
        intro j
        by_cases hj : j = i
        · subst hj
          have h1 := hR j
          simp only [e', Function.update_self]
          rw [abs_le] at h1 ⊢
          rcases lt_or_gt_of_ne hi with h | h
          · rw [Int.sign_eq_neg_one_of_neg h]
            omega
          · rw [Int.sign_eq_one_of_pos h]
            omega
        · simp only [e', Function.update_of_ne hj]
          exact hR j
      have hbox' := ih e' hsum hR'
      obtain ⟨h, hh, hs⟩ := hS _ (hball e hR)
      have heq : h = a + e := by
        have h1 : y + siteOfInt (a + e) = y + siteOfInt h := by rw [add_siteOfInt_add, ← hz, hs]
        refine (eq_of_siteOfInt_eq (add_left_cancel h1) fun j => ?_).symm
        have b1 := hh j
        have b2 := hbox' j
        have b3 : |(a + e) j - (a + e') j| ≤ 1 := by
          by_cases hj : j = i
          · subst hj
            simp only [Pi.add_apply, e', Function.update_self]
            rcases lt_or_gt_of_ne hi with h | h
            · rw [Int.sign_eq_neg_one_of_neg h, abs_le]
              omega
            · rw [Int.sign_eq_one_of_pos h, abs_le]
              omega
          · simp [e', Function.update_of_ne hj]
        rw [abs_le] at b1 b2 b3
        rw [abs_lt]
        constructor <;> omega
      rw [← heq]
      exact hh
  exact fun e he => key _ e rfl he
end Offsets
section Strips
variable {ℓ : StepParameters}
theorem stripStart_near (hfit : ℓ.Admissible) (u : ℤ) :
    0 ≤ u - stripStart ℓ.grid u ∧ u - stripStart ℓ.grid u < 2 ^ 15 := by
  have hLpos : 0 < ℓ.side := by have := hfit.L_ge; omega
  obtain ⟨_, ho⟩ := offsetFromCentre_spec hLpos hfit.L_odd u
  obtain ⟨b1, b2, b3, b4⟩ := ℓ.grid.mem_interval _ ho
  have hs := ℓ.grid.interval_length _ ho
  unfold stripStart
  constructor <;> linarith [hs.2]
theorem lumpCorner_eq_of_sameBlockPosition (hfit : ℓ.Admissible) {n n' : ℕ} [NeZero n] [NeZero n']
    (hLn : ℓ.side ∣ n) (hLn' : ℓ.side ∣ n') (hbig : 2 ^ 17 < n) {y : TorusSite n} {y' : TorusSite n'}
    (hb : SameBlockPosition ℓ y y') (a e : Fin 4 → ℤ) (he : ∀ i, |e i| ≤ 2 ^ 15)
    (hk : lumpCorner ℓ (y + siteOfInt a) = lumpCorner ℓ (y + siteOfInt (a + e))) :
    lumpCorner ℓ (y' + siteOfInt a) = lumpCorner ℓ (y' + siteOfInt (a + e)) := by
  have hLpos : 0 < ℓ.side := by have := hfit.L_ge; omega
  have hY : ∀ b : Fin 4 → ℤ, y + siteOfInt b = siteOfInt ((fun i => ((y i).cast : ℤ)) + b) := by
    intro b
    rw [siteOfInt_add, ← eq_siteOfInt_cast y]
  have hY' : ∀ b : Fin 4 → ℤ, y' + siteOfInt b = siteOfInt ((fun i => ((y' i).cast : ℤ)) + b) := by
    intro b
    rw [siteOfInt_add, ← eq_siteOfInt_cast y']
  rw [hY, hY, lumpCorner_siteOfInt hfit hLn, lumpCorner_siteOfInt hfit hLn] at hk
  rw [hY', hY', lumpCorner_siteOfInt hfit hLn', lumpCorner_siteOfInt hfit hLn']
  funext i
  have h1 := congrFun hk i
  simp only [Pi.add_apply] at h1 ⊢
  set c : ℤ := ((y i).cast : ℤ) with hc
  set c' : ℤ := ((y' i).cast : ℤ) with hc'
  have hD : stripStart ℓ.grid (c + a i) = stripStart ℓ.grid (c + (a i + e i)) := by
    refine int_eq_of_zmod_cast_eq h1 ?_
    have s1 := stripStart_near hfit (c + a i)
    have s2 := stripStart_near hfit (c + (a i + e i))
    have hei := he i
    rw [abs_le] at hei
    rw [abs_lt]
    constructor <;> linarith [s1.1, s1.2, s2.1, s2.2, hei.1, hei.2]
  have hdv : (ℓ.side : ℤ) ∣ c' - c := by
    have := hb i
    have h2 : (ℓ.side : ℤ) ∣ c - c' := Int.dvd_of_emod_eq_zero this
    have := dvd_neg.mpr h2
    simpa using this
  have e1 : c' + a i = (c + a i) + (c' - c) := by ring
  have e2 : c' + (a i + e i) = (c + (a i + e i)) + (c' - c) := by ring
  rw [e1, e2, stripStart_add_dvd hLpos hfit.L_odd _ _ _ hdv, stripStart_add_dvd hLpos hfit.L_odd _ _ _ hdv, hD]
end Strips
section Matching
variable {ℓ : StepParameters} {n n' : ℕ} [NeZero n] [NeZero n'] {r : ℕ}
variable {W : TorusField n} {W' : TorusField n'} {Y : Finset (TorusSite n)} {Y' : Finset (TorusSite n')}
  {X : Finset (TorusSite n)} {X' : Finset (TorusSite n')} {y : TorusSite n} {y' : TorusSite n'} {m : ℕ}
theorem bondFrom_fst_add_unitStep (y : TorusSite n) (b : (Fin 4 → ℤ) × Fin 4) :
    (bondFrom y b).1 + TorusFields.unitStep n b.2 = y + siteOfInt (b.1 + Pi.single b.2 1) := by
  rw [add_siteOfInt_add, unitStep_eq_siteOfInt]
  rfl
end Matching
end YangMills.Construction.TorusLumps
end
