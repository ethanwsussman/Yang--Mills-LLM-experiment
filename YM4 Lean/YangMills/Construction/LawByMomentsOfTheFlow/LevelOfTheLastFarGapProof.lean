import YangMills.Construction.FourPointCondition.LevelForEveryScaleProof
import YangMills.Construction.LawByMomentsOfTheFlow.LastFarLevelNearTheScale
import YangMills.Construction.LawByMomentsOfTheFlow.LevelOfTheLastFarGap
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAtTheLastFarLevelInALimitFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelTestFunctions
open TorusLumps WeightedResponses
private theorem linear_le_eps_pow_add (L : ℝ) (hL : 1 < L) (ε A : ℝ) (hε : 0 < ε) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, A * m ≤ ε * L ^ m + C := by apply _root_.YangMills.SharedProofs.p107442 <;> assumption
private theorem rpow_hundredth_le_one_add (u : ℝ) (hu : 0 ≤ u) : u ^ ((1 : ℝ) / 100) ≤ 1 + u := by
  rcases le_total u 1 with h | h
  · have := Real.rpow_le_one hu h (by norm_num : (0 : ℝ) ≤ 1 / 100)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h (by norm_num : (1 : ℝ) / 100 ≤ 1)
    rw [Real.rpow_one] at this
    linarith
private theorem clusterRange_lt (x : ℝ) (hx : 0 ≤ x) : (clusterRange x : ℝ) < x ^ ((1 : ℝ) / 100) + 1 :=
  Nat.ceil_lt_add_one (Real.rpow_nonneg hx _)
private theorem rpow_hundredth_le_clusterRange (x : ℝ) : x ^ ((1 : ℝ) / 100) ≤ (clusterRange x : ℝ) :=
  Nat.le_ceil _
private theorem one_le_clusterRange (x : ℝ) (hx : 0 < x) : (1 : ℝ) ≤ (clusterRange x : ℝ) := by apply _root_.YangMills.SharedProofs.p30320 <;> assumption
private theorem one_lt_y₁ {ℓ : StepParameters} (hf : ℓ.Admissible) : 1 < ℓ.y₁ := by
  by_contra h
  have h1 : ℓ.y₁ = 1 := le_antisymm (not_lt.mp h) hf.y₁_ge
  have h2 := hf.range_ge
  rw [h1] at h2
  simp [clusterRange] at h2
open Classical in
private theorem separationLevel_spec {k : ℕ} (P : LevelData k) (ℓ : StepParameters) (β : ℝ) :
    P.separationLevel ℓ β ≤ P.windowLevel ∧ P.SeparatedBelow ℓ β (P.separationLevel ℓ β) ∧
      (P.separationLevel ℓ β < P.windowLevel → ¬ P.SeparatedBelow ℓ β (P.separationLevel ℓ β + 1)) := by
  unfold LevelData.separationLevel
  refine ⟨Nat.findGreatest_le _, Nat.findGreatest_spec (m := 0) (Nat.zero_le _) ?_, fun h =>
    Nat.findGreatest_is_greatest (Nat.lt_succ_self _) h⟩
  intro u hu
  exact absurd hu (Nat.not_lt_zero u)
theorem separationLevelScale_of_bounds (hG : separationLowerBoundStatement)
    (hN : separationLevelNearScaleStatement) (hW : CouplingFlowAboveWindow) :
    separationLevelScaleStatement := by
  intro ℓ hℓ g hg hy k hk R d hd
  have hf := hℓ.admissible
  have hL3 : 3 ≤ ℓ.side := by
    have := hf.L_ge
    omega
  obtain ⟨c, hc, hgap⟩ := hG ℓ.side hf.L_odd hL3 k hk R d hd
  obtain ⟨C₁, hnear⟩ := hN ℓ hf k hk R d hd
  have hB := hf.B_pos
  have hLr : (2 : ℝ) ≤ ℓ.side := by exact_mod_cast (by omega : 2 ≤ ℓ.side)
  have hy1 := one_lt_y₁ hf
  have hlg : 0 < Real.log ℓ.y₁ := Real.log_pos hy1
  have hlL : 0 < Real.log ℓ.side := Real.log_pos (by linarith)
  obtain ⟨C₂, hC₂, hlin⟩ := linear_le_eps_pow_add ℓ.side (by linarith) (c / 2) (2 ^ 10 * (2 * ℓ.B))
    (by positivity) (by positivity)
  obtain ⟨C₄, hC₄d⟩ : ∃ C₄ : ℝ, C₄ = 1 + 2 / c * (2 ^ 10 + 2 ^ 11 + 20 + C₂) := ⟨_, rfl⟩
  have hC₄ : 1 ≤ C₄ := by
    rw [hC₄d]
    have : 0 ≤ 2 / c * (2 ^ 10 + 2 ^ 11 + 20 + C₂) := by positivity
    linarith
  obtain ⟨C₅, hC₅d⟩ : ∃ C₅ : ℝ, C₅ = (|Real.log (2 * C₄)| / Real.log ℓ.y₁ + 1) / Real.log ℓ.side :=
    ⟨_, rfl⟩
  have hC₅ : 0 ≤ C₅ := by
    rw [hC₅d]
    positivity
  refine ⟨1 + C₄ + 2 * ℓ.B * C₅ + 2 * ℓ.B * |C₁| / Real.log ℓ.y₁, fun P hF β hβ hK => ?_⟩
  obtain ⟨hyj, hrun⟩ := hW ℓ hℓ g hg hy β P.windowLevel hβ hK
  obtain ⟨hle, hfar, hnf⟩ := separationLevel_spec P ℓ β
  have hsK := hF.scaleLevel_le
  generalize hxd : (couplingFlow ℓ β P.scaleLevel).1 = x at *
  have hxy : ℓ.y₁ ≤ x := hxd ▸ hyj _ hsK
  have hx1 : 1 < x := hy1.trans_le hxy
  have hlogx : Real.log ℓ.y₁ ≤ Real.log x := Real.log_le_log (by linarith) hxy
  have hlogpos : 0 < Real.log x := by linarith
  have hr1 := one_le_clusterRange x (by linarith)
  have hratio : 1 ≤ Real.log x / Real.log ℓ.y₁ := by
    rw [le_div_iff₀ hlg]
    linarith
  have hCsum : ∀ a : ℝ, 0 ≤ a → a ≤ 1 + C₄ + 2 * ℓ.B * C₅ + 2 * ℓ.B * |C₁| / Real.log ℓ.y₁ + a := by
    intro a ha
    have h1 : 0 ≤ 2 * ℓ.B * C₅ := by positivity
    have h2 : 0 ≤ 2 * ℓ.B * |C₁| / Real.log ℓ.y₁ := by positivity
    linarith
  have hterm1 : 0 ≤ 2 * ℓ.B * C₅ := by positivity
  have hterm2 : 0 ≤ 2 * ℓ.B * |C₁| / Real.log ℓ.y₁ := by positivity
  rcases Nat.lt_or_ge P.scaleLevel (P.separationLevel ℓ β) with hst | hts
  · refine ⟨?_, ?_⟩
    · have h1 : (ℓ.side : ℝ) ^ ((P.scaleLevel : ℤ) - (P.separationLevel ℓ β : ℤ)) ≤ 1 :=
        zpow_le_one_of_nonpos₀ (by linarith) (by omega)
      have h2 : (1 : ℝ) ≤ 1 + C₄ + 2 * ℓ.B * C₅ + 2 * ℓ.B * |C₁| / Real.log ℓ.y₁ := by linarith
      exact h1.trans (one_le_mul_of_one_le_of_one_le h2 hr1)
    · have hd1 := hrun P.scaleLevel (P.separationLevel ℓ β) hst.le hle
      rw [hxd] at hd1
      have hn := hnear P hF β
      have h3 : ((P.separationLevel ℓ β : ℝ) - (P.scaleLevel : ℝ)) ≤ |C₁| := by
        have := le_abs_self C₁
        linarith
      have h4 : 2 * ℓ.B * ((P.separationLevel ℓ β : ℝ) - (P.scaleLevel : ℝ)) ≤
          2 * ℓ.B * |C₁| / Real.log ℓ.y₁ * Real.log x := by
        have h5 : 2 * ℓ.B * ((P.separationLevel ℓ β : ℝ) - (P.scaleLevel : ℝ)) ≤ 2 * ℓ.B * |C₁| :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        have h6 : 2 * ℓ.B * |C₁| / Real.log ℓ.y₁ * Real.log x =
            2 * ℓ.B * |C₁| * (Real.log x / Real.log ℓ.y₁) := by
          ring
        rw [h6]
        have h7 : 0 ≤ 2 * ℓ.B * |C₁| := by positivity
        exact h5.trans (le_mul_of_one_le_right h7 hratio)
      have h8 : (1 + C₄ + 2 * ℓ.B * C₅) * Real.log x ≥ 0 := by positivity
      have h9 : (1 + C₄ + 2 * ℓ.B * C₅ + 2 * ℓ.B * |C₁| / Real.log ℓ.y₁) * Real.log x =
          (1 + C₄ + 2 * ℓ.B * C₅) * Real.log x + 2 * ℓ.B * |C₁| / Real.log ℓ.y₁ * Real.log x := by ring
      rw [h9]
      linarith
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, P.scaleLevel = P.separationLevel ℓ β + m :=
      ⟨P.scaleLevel - P.separationLevel ℓ β, by omega⟩
    have hz : (ℓ.side : ℝ) ^ ((P.scaleLevel : ℤ) - (P.separationLevel ℓ β : ℤ)) = (ℓ.side : ℝ) ^ m := by
      have : (P.scaleLevel : ℤ) - (P.separationLevel ℓ β : ℤ) = (m : ℤ) := by omega
      rw [this, zpow_natCast]
    have hLm : 0 < (ℓ.side : ℝ) ^ m := by positivity
    have hpow : (ℓ.side : ℝ) ^ m ≤ C₄ * (clusterRange x : ℝ) := by
      by_cases htK : P.separationLevel ℓ β < P.windowLevel
      · have hnot := hnf htK
        have hfail : P.separation ℓ.side (P.separationLevel ℓ β) ≤
            2 ^ 10 * clusterRange (couplingFlow ℓ β (P.separationLevel ℓ β)).1 + 8 := by
          by_contra hcon
          apply hnot
          intro u hu
          rcases Nat.lt_succ_iff_lt_or_eq.mp hu with h1 | h1
          · exact hfar u h1
          · subst h1
            constructor <;> omega
        have hfr : (P.separation ℓ.side (P.separationLevel ℓ β) : ℝ) ≤
            2 ^ 10 * (clusterRange (couplingFlow ℓ β (P.separationLevel ℓ β)).1 : ℝ) + 8 := by
          exact_mod_cast hfail
        have hgp := hgap P hF (P.separationLevel ℓ β) htK
        rw [hz] at hgp
        have hyt := hyj _ hle
        have hxt0 : 0 ≤ (couplingFlow ℓ β (P.separationLevel ℓ β)).1 := by linarith
        have hrt := clusterRange_lt _ hxt0
        have hd1 := hrun (P.separationLevel ℓ β) P.scaleLevel hts hsK
        rw [hxd] at hd1
        have hmr : (P.scaleLevel : ℝ) - (P.separationLevel ℓ β : ℝ) = m := by
          rw [hm]
          push_cast
          ring
        rw [hmr] at hd1
        have hxt : (couplingFlow ℓ β (P.separationLevel ℓ β)).1 ≤ x + 2 * ℓ.B * m := by
          have := (abs_le.mp hd1).1
          linarith
        have hu0 : 0 ≤ 2 * ℓ.B * (m : ℝ) := by positivity
        have hroot : (couplingFlow ℓ β (P.separationLevel ℓ β)).1 ^ ((1 : ℝ) / 100) ≤
            x ^ ((1 : ℝ) / 100) + (1 + 2 * ℓ.B * m) := by
          have h1 := Real.rpow_le_rpow hxt0 hxt (by norm_num : (0 : ℝ) ≤ 1 / 100)
          have h2 := Real.rpow_add_le_add_rpow (by linarith : 0 ≤ x) hu0 (by norm_num : (0 : ℝ) ≤ 1 / 100)
            (by norm_num : (1 : ℝ) / 100 ≤ 1)
          have h3 := rpow_hundredth_le_one_add _ hu0
          linarith
        have hl := hlin m
        have hxr := rpow_hundredth_le_clusterRange x
        have hmain : c / 2 * (ℓ.side : ℝ) ^ m ≤ (2 ^ 10 + 2 ^ 11 + 20 + C₂) * (clusterRange x : ℝ) := by
          have h1 : c * (ℓ.side : ℝ) ^ m ≤ 2 ^ 10 * (x ^ ((1 : ℝ) / 100) + (1 + 2 * ℓ.B * m) + 1) + 20 := by
            linarith
          have h2 : c / 2 * (ℓ.side : ℝ) ^ m ≤ 2 ^ 10 * x ^ ((1 : ℝ) / 100) + 2 ^ 11 + 20 + C₂ := by
            linarith
          have h3 : (2 ^ 10 + 2 ^ 11 + 20 + C₂) * (clusterRange x : ℝ) =
              2 ^ 10 * (clusterRange x : ℝ) + (2 ^ 11 + 20 + C₂) * (clusterRange x : ℝ) := by ring
          have h4 : (2 ^ 11 + 20 + C₂) * 1 ≤ (2 ^ 11 + 20 + C₂) * (clusterRange x : ℝ) :=
            mul_le_mul_of_nonneg_left hr1 (by positivity)
          linarith
        have h5 : (ℓ.side : ℝ) ^ m ≤ 2 / c * ((2 ^ 10 + 2 ^ 11 + 20 + C₂) * (clusterRange x : ℝ)) := by
          have : (ℓ.side : ℝ) ^ m = 2 / c * (c / 2 * (ℓ.side : ℝ) ^ m) := by
            field_simp
          rw [this]
          exact mul_le_mul_of_nonneg_left hmain (by positivity)
        have h6 : (1 + 2 / c * (2 ^ 10 + 2 ^ 11 + 20 + C₂)) * (clusterRange x : ℝ) =
            (clusterRange x : ℝ) + 2 / c * ((2 ^ 10 + 2 ^ 11 + 20 + C₂) * (clusterRange x : ℝ)) := by ring
        rw [hC₄d, h6]
        linarith
      · have hsame : m = 0 := by omega
        rw [hsame, pow_zero]
        exact one_le_mul_of_one_le_of_one_le hC₄ hr1
    refine ⟨?_, ?_⟩
    · rw [hz]
      have h2 : C₄ ≤ 1 + C₄ + 2 * ℓ.B * C₅ + 2 * ℓ.B * |C₁| / Real.log ℓ.y₁ := by linarith
      exact hpow.trans (mul_le_mul_of_nonneg_right h2 (by linarith))
    · have hd1 := hrun (P.separationLevel ℓ β) P.scaleLevel hts hsK
      rw [hxd] at hd1
      have hmr : (P.scaleLevel : ℝ) - (P.separationLevel ℓ β : ℝ) = m := by
        rw [hm]
        push_cast
        ring
      rw [hmr, abs_sub_comm] at hd1
      have hrx : (clusterRange x : ℝ) ≤ 2 * x := by
        have h1 := clusterRange_lt x (by linarith)
        have h2 := Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num : (1 : ℝ) / 100 ≤ 1)
        rw [Real.rpow_one] at h2
        linarith
      have hlog1 : (m : ℝ) * Real.log ℓ.side ≤ Real.log (2 * C₄) + Real.log x := by
        have h1 : (ℓ.side : ℝ) ^ m ≤ 2 * C₄ * x := by
          have h3 := mul_le_mul_of_nonneg_left hrx (by linarith : 0 ≤ C₄)
          have h4 : C₄ * (2 * x) = 2 * C₄ * x := by ring
          linarith
        have h2 := Real.log_le_log hLm h1
        rw [Real.log_pow, Real.log_mul (by positivity) (by linarith)] at h2
        exact h2
      have hlog2 : Real.log (2 * C₄) ≤ |Real.log (2 * C₄)| / Real.log ℓ.y₁ * Real.log x := by
        have h1 := le_abs_self (Real.log (2 * C₄))
        have h2 : |Real.log (2 * C₄)| / Real.log ℓ.y₁ * Real.log x =
            |Real.log (2 * C₄)| * (Real.log x / Real.log ℓ.y₁) := by ring
        rw [h2]
        have h3 := abs_nonneg (Real.log (2 * C₄))
        exact h1.trans (le_mul_of_one_le_right h3 hratio)
      have hmle : (m : ℝ) ≤ C₅ * Real.log x := by
        rw [hC₅d, div_mul_eq_mul_div, le_div_iff₀ hlL]
        have h1 : (|Real.log (2 * C₄)| / Real.log ℓ.y₁ + 1) * Real.log x =
            |Real.log (2 * C₄)| / Real.log ℓ.y₁ * Real.log x + Real.log x := by ring
        rw [h1]
        linarith
      have h9 : 2 * ℓ.B * (m : ℝ) ≤ 2 * ℓ.B * C₅ * Real.log x := by
        have := mul_le_mul_of_nonneg_left hmle (by positivity : 0 ≤ 2 * ℓ.B)
        linarith
      have h10 : 0 ≤ (1 + C₄ + 2 * ℓ.B * |C₁| / Real.log ℓ.y₁) * Real.log x := by positivity
      have h11 : (1 + C₄ + 2 * ℓ.B * C₅ + 2 * ℓ.B * |C₁| / Real.log ℓ.y₁) * Real.log x =
          (1 + C₄ + 2 * ℓ.B * |C₁| / Real.log ℓ.y₁) * Real.log x + 2 * ℓ.B * C₅ * Real.log x := by ring
      rw [h11]
      linarith
end YangMills.Construction.LevelTestFunctions
end
