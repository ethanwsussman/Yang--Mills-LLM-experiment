import YangMills.Construction.Geometry.SegmentDeterminesEndpoints
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Segment
theorem segmentDeterminesEndpoints_holds : SegmentDeterminesEndpoints := by
  intro a a' b b' hS
  have hS' : ∀ z : Fin 4 → ℝ, (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = a + t • (a' - a)) ↔
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = b + t • (b' - b)) := fun z => Set.ext_iff.mp hS z
  have extreme : ∀ p d : Fin 4 → ℝ, b ≠ b' →
      (∀ z : Fin 4 → ℝ, (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = b + t • (b' - b)) →
        ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = p + t • d) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = b + t • (b' - b)) → p = b ∨ p = b' := by
    rintro p d hne hall ⟨t, ht0, ht1, hp⟩
    rcases ht0.eq_or_lt with h0 | ht0'
    · left
      rw [hp, ← h0]
      simp
    rcases ht1.eq_or_lt with h1 | ht1'
    · right
      rw [hp, h1]
      simp
    exfalso
    have hdir : b' - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    obtain ⟨s, hs0, hs1, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s ≤ t ∧ t + s ≤ 1 :=
      ⟨min t (1 - t), lt_min ht0' (by linarith), min_le_left _ _, by
        have := min_le_right t (1 - t)
        linarith⟩
    obtain ⟨u, hu0, -, hu⟩ := hall (b + (t - s) • (b' - b)) ⟨t - s, by linarith, by linarith, rfl⟩
    obtain ⟨w, hw0, -, hw⟩ := hall (b + (t + s) • (b' - b)) ⟨t + s, by linarith, by linarith, rfl⟩
    rw [hp] at hu hw
    have hu' : u • d = -(s • (b' - b)) := by
      have h : u • d = (b + (t - s) • (b' - b)) - (b + t • (b' - b)) := by
        rw [hu]
        abel
      rw [h, sub_smul]
      abel
    have hw' : w • d = s • (b' - b) := by
      have h : w • d = (b + (t + s) • (b' - b)) - (b + t • (b' - b)) := by
        rw [hw]
        abel
      rw [h, add_smul]
      abel
    have hsum : (u + w) • d = 0 := by
      rw [add_smul, hu', hw']
      simp
    have hsd : s • (b' - b) = 0 := by
      rcases smul_eq_zero.mp hsum with h | h
      · have hw00 : w = 0 := by linarith
        rw [← hw', hw00, zero_smul]
      · rw [← hw', h, smul_zero]
    exact hdir ((smul_eq_zero.mp hsd).resolve_left hs0.ne')
  have ha : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ a = a + t • (a' - a) := ⟨0, le_rfl, zero_le_one, by simp⟩
  have ha' : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ a' = a + t • (a' - a) :=
    ⟨1, zero_le_one, le_rfl, by simp⟩
  have hb : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ b = b + t • (b' - b) := ⟨0, le_rfl, zero_le_one, by simp⟩
  have hb' : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ b' = b + t • (b' - b) :=
    ⟨1, zero_le_one, le_rfl, by simp⟩
  by_cases hne : b = b'
  · left
    obtain ⟨t, -, -, h⟩ := (hS' a).mp ha
    obtain ⟨t', -, -, h'⟩ := (hS' a').mp ha'
    rw [← hne, sub_self, smul_zero, add_zero] at h h'
    exact ⟨h.symm, hne ▸ h'.symm⟩
  have haa : a ≠ a' := by
    intro h
    apply hne
    obtain ⟨t, -, -, h1⟩ := (hS' b).mpr hb
    obtain ⟨t', -, -, h2⟩ := (hS' b').mpr hb'
    rw [← h, sub_self, smul_zero, add_zero] at h1 h2
    exact h1.trans h2.symm
  have k1 : a = b ∨ a = b' :=
    extreme a (a' - a) hne (fun z hz => (hS' z).mpr hz) ((hS' a).mp ha)
  have k2 : a' = b ∨ a' = b' := by
    refine extreme a' (a - a') hne (fun z hz => ?_) ((hS' a').mp ha')
    obtain ⟨t, ht0, ht1, h⟩ := (hS' z).mpr hz
    refine ⟨1 - t, by linarith, by linarith, ?_⟩
    rw [h]
    ext i
    simp
    ring
  rcases k1 with h1 | h1 <;> rcases k2 with h2 | h2
  · exact absurd (h1.trans h2.symm) haa
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h2.symm, h1.symm⟩
  · exact absurd (h1.trans h2.symm) haa
end YangMills.Construction.Segment
