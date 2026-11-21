import YangMills.Construction.ParameterData.TheWindowHasMembers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
theorem passageWindowNonemptyAt_of_admissible {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ}
    (P : TrajectoryParameters T y) (hP : P.Admissible) :
    passageWindowNonemptyAt P := by
  intro g _ hy
  have hb := hP.errorMargin
  have hdrop : ∀ (β : ℝ) (i j : ℕ), i ≤ j → (∀ l < j, P.X₀ ≤ P.coupling β l) →
      3 / 4 * P.c₀ * ((j : ℝ) - i) - 2 * P.cH ≤ P.coupling β i - P.coupling β j ∧
        P.coupling β i - P.coupling β j ≤ 5 / 4 * P.c₀ * ((j : ℝ) - i) + 2 * P.cH :=
    hb.drop_two_sided
  have hinit : ∀ β : ℝ, P.coupling β 0 = β := fun _ => rfl
  have hc₀ : 10 < P.c₀ := hb.slope_gt
  have hB : 0 < T.B := hb.admissible.B_pos
  have hshift : 0 ≤ P.shift := by linarith [hP.shift_ge]
  have hcH : 0 ≤ P.cH := by
    have h := hb.slope 0 0 le_rfl
    simp only [Finset.Ico_self, Finset.sum_empty, Nat.cast_zero, sub_self, zero_mul, abs_zero] at h
    linarith
  have hXg : P.X₀ ≤ g ^ (-2 : ℤ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hvg : P.v₀ ≤ g ^ (-2 : ℤ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hthr : P.threshold g = g ^ (-2 : ℤ) + P.shift := rfl
  have hXthr : P.X₀ ≤ P.threshold g := by rw [hthr]; linarith
  have hX : 8 ≤ P.X₀ := hb.floor_ge
  have hmem_le : ∀ (K : ℕ) (β : ℝ), β ∈ P.passageWindow K g →
      β ≤ P.threshold g + 5 / 4 * P.c₀ * (K : ℝ) + 2 * P.cH := by
    intro K β hβ
    obtain ⟨-, hK, hpre⟩ : SequencePassage.passageThreshold P.shift g ≤ β ∧
        SequencePassage.IsFirstPassageIndex P.shift g (P.coupling β) K := hβ
    have hK' : P.coupling β K ≤ P.threshold g := hK
    have hl := (hdrop β 0 K (Nat.zero_le K)
      (fun l hl => hXthr.trans (le_of_lt (hpre l hl)))).2
    rw [hinit] at hl
    simp only [Nat.cast_zero, sub_zero] at hl
    linarith
  have hexists : ∀ K₀ : ℕ, ∃ K : ℕ, K₀ < K ∧ K ≤ K₀ + P.windowCount ∧
      (P.passageWindow K g).Nonempty := by
    intro K₀
    have hvt : P.v₀ ≤ P.threshold g + 2 * P.cH + 1 := by rw [hthr]; linarith
    obtain ⟨β, ⟨hβv, hβf⟩, -⟩ := hb.flow_above.existsUnique_value K₀ (P.threshold g + 2 * P.cH + 1) hvt
    have hfb := hb.bounds β
    have hnv := hfb.near_value K₀ (P.threshold g + 2 * P.cH + 1) hvt hβv hβf
    have hstay : ∀ l ≤ K₀, P.X₀ ≤ P.coupling β l := hfb.staysAbove_of_flow K₀ hβf
    have hlow : P.threshold g + 2 * P.cH + 1 - 1 / 2 ≤ P.coupling β K₀ := hnv.1
    have hclose : |P.coupling β K₀ - (P.threshold g + 2 * P.cH + 1)| ≤
        2 * P.Cr * (P.coupling β K₀) ^ (-(1 / 4) : ℝ) := hnv.2.1
    have hXpos : 0 < P.X₀ := by linarith
    have hrpow : (P.coupling β K₀) ^ (-(1 / 4) : ℝ) ≤ P.X₀ ^ (-(1 / 4) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hXpos (hstay K₀ le_rfl) (by norm_num)
    have hCr : 0 ≤ P.Cr := hb.Cr_nonneg
    have hCrsmall : 8 * P.Cr * P.X₀ ^ (-(1 / 4) : ℝ) ≤ 1 := hb.Cr_small
    have hquarter : 2 * P.Cr * (P.coupling β K₀) ^ (-(1 / 4) : ℝ) ≤ 1 / 4 := by
      have := mul_le_mul_of_nonneg_left hrpow hCr
      nlinarith
    have hupper : P.coupling β K₀ ≤ P.threshold g + 2 * P.cH + 1 + 1 / 4 := by
      have := (abs_le.mp hclose).2
      linarith
    have habove : ∀ l ≤ K₀, P.threshold g + 1 / 2 ≤ P.coupling β l := by
      intro l hl
      have h := (hdrop β l K₀ hl (fun m hm => hstay m hm.le)).1
      have hlK : (0 : ℝ) ≤ (K₀ : ℝ) - l := by
        have : (l : ℝ) ≤ K₀ := by exact_mod_cast hl
        linarith
      have : 0 ≤ 3 / 4 * P.c₀ * ((K₀ : ℝ) - l) := by positivity
      linarith
    have hβthr : P.threshold g ≤ β := by
      have := habove 0 (Nat.zero_le K₀)
      rw [hinit] at this
      linarith
    have hpass : ∃ k, P.coupling β k ≤ P.threshold g := by
      by_contra hnone
      have hgt : ∀ k, P.threshold g < P.coupling β k := fun k => not_le.mp fun h => hnone ⟨k, h⟩
      obtain ⟨j, hj⟩ := exists_nat_gt ((β - P.threshold g + 2 * P.cH) / (3 / 4 * P.c₀))
      have hc₀' : 0 < 3 / 4 * P.c₀ := by linarith
      rw [div_lt_iff₀ hc₀'] at hj
      have h := (hdrop β 0 j (Nat.zero_le j) (fun l _ => hXthr.trans (hgt l).le)).1
      rw [hinit] at h
      simp only [Nat.cast_zero, sub_zero] at h
      have := hgt j
      nlinarith
    classical
    have hK : P.coupling β (Nat.find hpass) ≤ P.threshold g := Nat.find_spec hpass
    have hpre : ∀ k < Nat.find hpass, P.threshold g < P.coupling β k := fun k hk =>
      not_le.mp (Nat.find_min hpass hk)
    generalize Nat.find hpass = K at hK hpre
    have hlt : K₀ < K := by
      by_contra hnot
      have := habove K (not_lt.mp hnot)
      linarith
    refine ⟨K, hlt, ?_, β, ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, K = K₀ + m + 1 := ⟨K - K₀ - 1, by omega⟩
      have hprev := hpre (K₀ + m) (by omega)
      have h := (hdrop β K₀ (K₀ + m) (by omega)
        (fun l hl => hXthr.trans (hpre l (by omega)).le)).1
      have hcast : (((K₀ + m : ℕ) : ℝ) - K₀) = m := by push_cast; ring
      rw [hcast] at h
      have hc₀' : 0 < 3 * P.c₀ := by linarith
      have hm : (m : ℝ) ≤ (16 * P.cH + 5) / (3 * P.c₀) := by
        rw [le_div_iff₀ hc₀']
        nlinarith
      have hfloor : m ≤ ⌊(16 * P.cH + 5) / (3 * P.c₀)⌋₊ :=
        Nat.le_floor hm
      have hcount : P.windowCount = 1 + ⌊(16 * P.cH + 5) / (3 * P.c₀)⌋₊ := rfl
      omega
    · exact (⟨hβthr, hK, hpre⟩ : SequencePassage.passageThreshold P.shift g ≤ β ∧
        SequencePassage.IsFirstPassageIndex P.shift g (P.coupling β) K)
  refine ⟨?_, ?_, hexists⟩
  · intro K₀
    refine ⟨P.threshold g + 5 / 4 * P.c₀ * (K₀ : ℝ) + 2 * P.cH + 1, fun β hβ K hmem => ?_⟩
    by_contra hnot
    have hKK : (K : ℝ) ≤ K₀ := by exact_mod_cast (not_le.mp hnot).le
    have := hmem_le K β hmem
    have hc₀' : 0 ≤ 5 / 4 * P.c₀ := by linarith
    have := mul_le_mul_of_nonneg_left hKK hc₀'
    linarith
  · refine Set.infinite_of_forall_exists_gt fun K₀ => ?_
    obtain ⟨K, hlt, -, hne⟩ := hexists K₀
    exact ⟨K, hne, hlt⟩
theorem passageWindowNonempty : passageWindowNonemptyStatement := by apply _root_.YangMills.Construction.TrajectoryData.passageWindowNonemptyAt_of_admissible <;> assumption
end YangMills.Construction.TrajectoryData
end
