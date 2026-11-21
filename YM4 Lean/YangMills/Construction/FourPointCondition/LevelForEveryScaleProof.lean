import YangMills.Construction.FourPointCondition.LevelForEveryScale
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice TorusLumps
namespace FourPointBounds
private theorem clusterRange_le_two_mul {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : v ≤ 3 * u) :
    clusterRange v ≤ 2 * clusterRange u := by
  have hthree : (3 : ℝ) ^ ((1 : ℝ) / 100) ≤ 2 := by
    have h : (3 : ℝ) ≤ (2 : ℝ) ^ (100 : ℝ) := by
      rw [show (100 : ℝ) = ((100 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    calc (3 : ℝ) ^ ((1 : ℝ) / 100) ≤ ((2 : ℝ) ^ (100 : ℝ)) ^ ((1 : ℝ) / 100) :=
          Real.rpow_le_rpow (by norm_num) h (by norm_num)
      _ = 2 := by
          rw [← Real.rpow_mul (by norm_num)]
          norm_num
  have hceil : u ^ ((1 : ℝ) / 100) ≤ (clusterRange u : ℝ) := Nat.le_ceil _
  unfold clusterRange at hceil ⊢
  apply Nat.ceil_le.mpr
  push_cast
  calc v ^ ((1 : ℝ) / 100) ≤ (3 * u) ^ ((1 : ℝ) / 100) :=
        Real.rpow_le_rpow hv huv (by norm_num)
    _ = (3 : ℝ) ^ ((1 : ℝ) / 100) * u ^ ((1 : ℝ) / 100) :=
        Real.mul_rpow (by norm_num) hu
    _ ≤ 2 * u ^ ((1 : ℝ) / 100) := by gcongr
    _ ≤ 2 * (⌈u ^ ((1 : ℝ) / 100)⌉₊ : ℝ) := by gcongr
private theorem one_le_clusterRange {u : ℝ} (hu : 0 < u) : (1 : ℝ) ≤ (clusterRange u : ℝ) := by
  have h : 0 < clusterRange u := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hu _)
  exact_mod_cast h
abbrev _root_.YangMills.SharedProofs.p30320 := @one_le_clusterRange
private theorem natCast_le_pow_of_two_le {b : ℝ} (hb : 2 ≤ b) (k : ℕ) : (k : ℝ) ≤ b ^ k := by
  induction k with
  | zero => simp
  | succ m ih =>
      have h1 : 1 ≤ b ^ m := one_le_pow₀ (by linarith)
      have h2 : b ^ m * 2 ≤ b ^ m * b := mul_le_mul_of_nonneg_left hb (by linarith)
      rw [pow_succ]
      push_cast
      linarith
theorem scaleLevelExists_holds : ScaleLevelExists := by
  classical
  intro p X nv d K x hadm hX16 hBX hnv hfloor hx0 hstep hd hlast
  have hBpos : 0 < p.B := hadm.B_pos
  have hside16 : (2 : ℝ) ^ 16 ≤ (p.side : ℝ) := by exact_mod_cast hadm.L_ge
  have hside2 : (2 : ℝ) ≤ (p.side : ℝ) := by linarith [show (2 : ℝ) ≤ 2 ^ 16 by norm_num]
  have hsidepos : (0 : ℝ) < (p.side : ℝ) := by linarith
  have hnvpos : 0 < nv := by linarith
  have hmesh : ∀ j : ℤ, 0 < meshSize p.side j := fun j => zpow_pos hsidepos _
  have hnext : ∀ k : ℕ, d / meshSize p.side ((K : ℤ) - (k : ℤ)) =
      (p.side : ℝ) * (d / meshSize p.side ((K : ℤ) - ((k + 1 : ℕ) : ℤ))) := by
    intro k
    have he : -((K : ℤ) - ((k + 1 : ℕ) : ℤ)) = -((K : ℤ) - (k : ℤ)) + 1 := by
      push_cast
      ring
    have hz : (p.side : ℝ) ^ (-((K : ℤ) - (k : ℤ))) ≠ 0 := (zpow_pos hsidepos _).ne'
    unfold meshSize
    rw [he, zpow_add_one₀ hsidepos.ne']
    field_simp
  have hd0 : nv ≤ d / meshSize p.side ((K : ℤ) - ((0 : ℕ) : ℤ)) := by simpa using hd
  have hmesh0 : meshSize p.side (K : ℤ) / d = 1 / (d / meshSize p.side ((K : ℤ) - ((0 : ℕ) : ℤ))) := by
    simp
  have hdnn : 0 ≤ d := by
    have h1 : 0 < d / meshSize p.side (K : ℤ) := by linarith
    have h2 := mul_pos h1 (hmesh (K : ℤ))
    rw [div_mul_cancel₀ _ (hmesh (K : ℤ)).ne'] at h2
    exact h2.le
  obtain ⟨n, hn⟩ : ∃ n : ℕ → ℝ, ∀ k : ℕ, d / meshSize p.side ((K : ℤ) - (k : ℤ)) = n k :=
    ⟨_, fun _ => rfl⟩
  simp only [hn] at hnext hd0 hmesh0 hlast ⊢
  have hmd : 0 ≤ meshSize p.side (K : ℤ) / d := div_nonneg (hmesh _).le hdnn
  have hX0 : X ≤ x 0 := by linarith
  have hXpos : 0 < X := by linarith
  have hpow : ∀ k : ℕ, n k * (p.side : ℝ) ^ k = n 0 := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
        rw [← ih, hnext m, pow_succ]
        ring
  obtain ⟨P, hP⟩ : ∃ P : ℕ → Prop, ∀ k, P k ↔ ((∀ j ≤ k, X ≤ x j) ∧
      2 ^ 12 * (p.side : ℝ) * (clusterRange (x k) : ℝ) ≤ n k) := ⟨_, fun _ => Iff.rfl⟩
  have hbound : ∀ k, P k → k ≤ ⌈n 0⌉₊ := by
    intro k hk
    obtain ⟨hj, hlow⟩ := (hP k).mp hk
    have hr := one_le_clusterRange (lt_of_lt_of_le hXpos (hj k le_rfl))
    have h1 : (1 : ℝ) ≤ 2 ^ 12 * (p.side : ℝ) := by nlinarith
    have h2 : (1 : ℝ) ≤ 2 ^ 12 * (p.side : ℝ) * (clusterRange (x k) : ℝ) := by nlinarith
    have h4 : (k : ℝ) ≤ (p.side : ℝ) ^ k := natCast_le_pow_of_two_le hside2 k
    have h5 : (p.side : ℝ) ^ k ≤ n 0 := by
      rw [← hpow k]
      have : 0 ≤ (p.side : ℝ) ^ k := by positivity
      nlinarith
    have h6 : (k : ℝ) ≤ (⌈n 0⌉₊ : ℝ) := by linarith [Nat.le_ceil (n 0)]
    exact_mod_cast h6
  by_cases hA : ∃ k, P k
  · obtain ⟨k0, hk0⟩ := hA
    have hPk : P (Nat.findGreatest P ⌈n 0⌉₊) := Nat.findGreatest_spec (hbound k0 hk0) hk0
    have hnot : ¬ P (Nat.findGreatest P ⌈n 0⌉₊ + 1) := fun h =>
      Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hbound _ h) h
    generalize Nat.findGreatest P ⌈n 0⌉₊ = k at hPk hnot
    obtain ⟨hj, hlow⟩ := (hP k).mp hPk
    have hxk : X ≤ x k := hj k le_rfl
    have hnextX : X ≤ x (k + 1) := by
      by_contra h
      have := hlast k hj (not_le.mp h)
      linarith
    have hj' : ∀ j ≤ k + 1, X ≤ x j := by
      intro j hjk
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · exact hj j (Nat.lt_succ_iff.mp h)
      · rw [le_antisymm hjk h]
        exact hnextX
    have hlt : n (k + 1) < 2 ^ 12 * (p.side : ℝ) * (clusterRange (x (k + 1)) : ℝ) := by
      by_contra h
      exact hnot ((hP (k + 1)).mpr ⟨hj', not_lt.mp h⟩)
    have hle : x (k + 1) ≤ 3 * x k := by
      have := (abs_le.mp (hstep k hj)).2
      linarith
    have hr : (clusterRange (x (k + 1)) : ℝ) ≤ 2 * (clusterRange (x k) : ℝ) := by
      have := clusterRange_le_two_mul (by linarith : 0 ≤ x k) (by linarith : 0 ≤ x (k + 1)) hle
      exact_mod_cast this
    have hup : n k ≤ x k ^ ((1 : ℝ) / 90) := by
      rw [hnext k]
      calc (p.side : ℝ) * n (k + 1)
          ≤ (p.side : ℝ) * (2 ^ 12 * (p.side : ℝ) * (clusterRange (x (k + 1)) : ℝ)) := by gcongr
        _ ≤ (p.side : ℝ) * (2 ^ 12 * (p.side : ℝ) * (2 * (clusterRange (x k) : ℝ))) := by gcongr
        _ ≤ 2 ^ 14 * (p.side : ℝ) ^ 2 * (clusterRange (x k) : ℝ) := by
            have : 0 ≤ (p.side : ℝ) ^ 2 * (clusterRange (x k) : ℝ) := by positivity
            nlinarith
        _ ≤ x k ^ ((1 : ℝ) / 90) := hfloor (x k) hxk
    exact ⟨k, 0, hj, Or.inl ⟨hlow, hup, rfl⟩, le_rfl, by positivity, hmd⟩
  · have hj0 : ∀ j ≤ 0, X ≤ x j := by
      intro j hj
      rw [Nat.le_zero.mp hj]
      exact hX0
    have hlt : n 0 < 2 ^ 12 * (p.side : ℝ) * (clusterRange (x 0) : ℝ) := by
      by_contra h
      exact hA ⟨0, (hP 0).mpr ⟨hj0, not_lt.mp h⟩⟩
    have hup : n 0 ≤ x 0 ^ ((1 : ℝ) / 90) := by
      calc n 0 ≤ 2 ^ 12 * (p.side : ℝ) * (clusterRange (x 0) : ℝ) := hlt.le
        _ ≤ 2 ^ 14 * (p.side : ℝ) ^ 2 * (clusterRange (x 0) : ℝ) := by
            have h1 : 0 ≤ (p.side : ℝ) * (clusterRange (x 0) : ℝ) := by positivity
            nlinarith
        _ ≤ x 0 ^ ((1 : ℝ) / 90) := hfloor (x 0) hX0
    have hn1 : 1 ≤ n 0 := by linarith
    exact ⟨0, 1 / n 0, hj0, Or.inr ⟨rfl, hn1, hup, rfl⟩, by positivity,
      one_div_le_one_div_of_le hnvpos hd0, hmesh0.ge⟩
end FourPointBounds
end YangMills.Construction
end
