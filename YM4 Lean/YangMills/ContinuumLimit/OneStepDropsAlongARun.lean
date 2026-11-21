import Mathlib
import YangMills.Construction.SummableBoundsOfTheFlow.SummabilityBoundsProof
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import YangMills.ContinuumLimit.TunedPairsAreFirstPassages
set_option autoImplicit false

noncomputable section

namespace YangMills.ContinuumLimit.Levels

open YangMills.Construction
open YangMills.Construction.ResponseInTheExpansion

namespace OneStepDropsAlongARun

theorem remainder_term_le {R s x : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hx : (8 * R / s) ^ (4 / 5 : ℝ) ≤ x) :
    R * x ^ (-(5 / 4) : ℝ) ≤ s / 8 := by
  have hq : 0 < 8 * R / s := by positivity
  have hx0 : 0 < x := lt_of_lt_of_le (Real.rpow_pos_of_pos hq _) hx
  have hpow : 8 * R / s ≤ x ^ (5 / 4 : ℝ) := by
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hq.le (4 / 5 : ℝ)) hx (by norm_num : (0 : ℝ) ≤ 5 / 4)
    rw [← Real.rpow_mul hq.le] at h1
    norm_num at h1
    exact h1
  have hxp : 0 < x ^ (5 / 4 : ℝ) := Real.rpow_pos_of_pos hx0 _
  rw [Real.rpow_neg hx0.le, ← div_eq_mul_inv, div_le_iff₀ hxp]
  rw [div_le_iff₀ hs] at hpow
  nlinarith

theorem second_term_le {M s x d : ℝ} (hs : 0 < s) (hd : |d| ≤ M) (hx1 : 1 ≤ x)
    (hx : 8 * M / s ≤ x) :
    |d / x| ≤ s / 8 := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
  rw [div_le_iff₀ hs] at hx
  nlinarith

theorem quarter_le_sub_succ {Tp : RenormalizationStepParameters.ParameterAssignment} {y C₁ M : ℝ}
    (hRef : FamilyNorms.RefinedExpansionHolds Tp y C₁ M) {s : ℝ} (hs : 0 < s) {t₀ : ℕ}
    (hb : ∀ t, t₀ ≤ t → s / 2 ≤ FamilyNorms.ParameterAssignment.oneLoop Tp t)
    (β : ℝ) (t : ℕ) (ht : t₀ ≤ t) (hrun : Run Tp y β t)
    (hX : max 1 (max (8 * M / s) ((8 * (C₁ * (2 * C₁ + 1)) / s) ^ (4 / 5 : ℝ))) ≤
      flowCouplings (Tp.stepParameters y) β t) :
    s / 4 ≤ flowCouplings (Tp.stepParameters y) β t - flowCouplings (Tp.stepParameters y) β (t + 1) := by
  have hstay : CouplingFlow.StaysAbove y (CouplingFlow.couplingAt (Tp.stepParameters y) β) t := hrun
  have hrem := CouplingFlow.followsFlowAbove_couplingAt hRef le_rfl β t hstay
  unfold CouplingFlow.stepRemainder at hrem
  have hxt : CouplingFlow.couplingAt (Tp.stepParameters y) β t = flowCouplings (Tp.stepParameters y) β t := rfl
  have hxs : CouplingFlow.couplingAt (Tp.stepParameters y) β (t + 1) =
      flowCouplings (Tp.stepParameters y) β (t + 1) := rfl
  rw [hxt, hxs] at hrem
  have hR : 0 < C₁ * (2 * C₁ + 1) := by
    have := hRef.C₁_pos
    positivity
  have hx1 : 1 ≤ flowCouplings (Tp.stepParameters y) β t := le_trans (le_max_left _ _) hX
  have hxM : 8 * M / s ≤ flowCouplings (Tp.stepParameters y) β t :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hxR : (8 * (C₁ * (2 * C₁ + 1)) / s) ^ (4 / 5 : ℝ) ≤ flowCouplings (Tp.stepParameters y) β t :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have h1 := remainder_term_le hR hs hxR
  have h2 := second_term_le hs (hRef.secondStep_le t) hx1 hxM
  have h3 := hb t ht
  have h4 := (abs_le.mp hrem).2
  have h5 := (abs_le.mp h2).1
  linarith

end OneStepDropsAlongARun

theorem one_step_drops {Tp : RenormalizationStepParameters.ParameterAssignment} {y C₁ M : ℝ}
    (hRef : FamilyNorms.RefinedExpansionHolds Tp y C₁ M) {s : ℝ} (hs : 0 < s) {t₀ : ℕ}
    (hb : ∀ t, t₀ ≤ t → s / 2 ≤ FamilyNorms.ParameterAssignment.oneLoop Tp t) :
    OneStepDrops Tp y t₀ (max 1 (max (8 * M / s) ((8 * (C₁ * (2 * C₁ + 1)) / s) ^ (4 / 5 : ℝ)))) := by
  intro β t ht hrun hX
  have h := OneStepDropsAlongARun.quarter_le_sub_succ hRef hs hb β t ht hrun hX
  linarith

end YangMills.ContinuumLimit.Levels

end
