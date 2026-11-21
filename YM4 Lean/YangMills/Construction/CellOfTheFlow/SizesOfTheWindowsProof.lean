import YangMills.Construction.CellOfTheFlow.SizesOfTheWindows
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses ResponseInTheExpansion
private lemma ceilDiv_le_mul_inv_pow (a L : ℕ) (hL : 2 ^ 40 ≤ L) : (ceilDiv a L : ℝ) ≤ (a : ℝ) * 2⁻¹ ^ 40 + 1 := by
  have hL1 : 1 ≤ L := le_trans (by norm_num) hL
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL1
  have hLbig : ((2 : ℝ) ^ 40) ≤ L := by exact_mod_cast hL
  have h1 : (((a + L - 1) / L : ℕ) : ℝ) ≤ ((a + L - 1 : ℕ) : ℝ) / L := Nat.cast_div_le
  have h2 : ((a + L - 1 : ℕ) : ℝ) = (a : ℝ) + L - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [h2] at h1
  have h3 : ((a : ℝ) + L - 1) / L ≤ (a : ℝ) / L + 1 := by
    have h4 : (a : ℝ) / L + 1 = ((a : ℝ) + L) / L := by
      field_simp
    rw [h4]
    exact div_le_div_of_nonneg_right (by linarith) hLr.le
  have h5 : (a : ℝ) / L ≤ (a : ℝ) * 2⁻¹ ^ 40 := by
    rw [div_eq_mul_inv, inv_pow]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hLbig) (Nat.cast_nonneg a)
  unfold ceilDiv
  linarith
private lemma windowDepth_succ_le {rj r' m H A G : ℝ} (hr' : 1 ≤ r') (hrj : rj ≤ 2 * r') (hm : 1 ≤ m)
    (hH : H ≤ rj * (7 + 2⁻¹ ^ 20 * m)) (hA : A ≤ H * 2⁻¹ ^ 40 + 1)
    (hG : G ≤ 2 ^ 12 * rj * m * 2⁻¹ ^ 40 + 1) :
    max (4 * r') (A + 1) + G + r' ≤ r' * (7 + 2⁻¹ ^ 20 * (m - 1)) := by
  have hP : 0 ≤ r' * m := by positivity
  have h1 : rj * (7 + 2⁻¹ ^ 20 * m) ≤ 2 * r' * (7 + 2⁻¹ ^ 20 * m) :=
    mul_le_mul_of_nonneg_right hrj (by positivity)
  have h2 : rj * m ≤ 2 * r' * m := mul_le_mul_of_nonneg_right hrj (by linarith)
  norm_num at hH hA hG h1 ⊢
  rcases le_total (4 * r') (A + 1) with h | h
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left h]
    nlinarith
private lemma windowDepth_le_stageRange {ℓ : StepParameters} (T : StageTower ℓ) (k : ℕ) (hL : 2 ^ 40 ≤ ℓ.side)
    (hr : ∀ j < k, stageRange T j ≤ 2 * stageRange T (j + 1)) (hpos : ∀ j < k, 1 ≤ stageRange T (j + 1)) :
    ∀ j ≤ k, (windowDepth T k j : ℝ) ≤ (stageRange T j : ℝ) * (7 + 2⁻¹ ^ 20 * ((k : ℝ) - j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    have hw : windowDepth T k 0 = 4 * stageRange T 0 := rfl
    rw [hw]
    push_cast
    nlinarith
  | succ j ih =>
    intro hj
    have hjk : j < k := hj
    have hjk' : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
    have hw : windowDepth T k (j + 1) =
        max (4 * stageRange T (j + 1)) (ceilDiv (windowDepth T k j) ℓ.side + 1) +
          ceilDiv (windowLength T k j) ℓ.side + stageRange T (j + 1) := rfl
    have hg : (windowLength T k j : ℝ) = 2 ^ 12 * (stageRange T j : ℝ) * ((k : ℝ) - j) := by
      unfold windowLength
      push_cast [Nat.cast_sub hjk.le]
      ring
    have hA := ceilDiv_le_mul_inv_pow (windowDepth T k j) ℓ.side hL
    have hG := ceilDiv_le_mul_inv_pow (windowLength T k j) ℓ.side hL
    rw [hg] at hG
    have hr1 : (1 : ℝ) ≤ (stageRange T (j + 1) : ℝ) := by exact_mod_cast hpos j hjk
    have hr2 : (stageRange T j : ℝ) ≤ 2 * (stageRange T (j + 1) : ℝ) := by exact_mod_cast hr j hjk
    have key := windowDepth_succ_le hr1 hr2 (m := (k : ℝ) - j) (by linarith) (ih hjk.le) hA hG
    rw [hw]
    push_cast
    have he : (k : ℝ) - ((j : ℝ) + 1) = (k : ℝ) - j - 1 := by ring
    rw [he]
    exact key
theorem windowDepthBound : windowDepthBoundStatement := by
  intro a _
  refine ⟨0, fun _ => 1, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hD _
  refine ⟨1, ?_⟩
  intro y hy _ _ T β k hk
  have hpos : ∀ j ≤ k, 1 ≤ stageRange T j := by
    intro j hj
    have hx : y ≤ (T.stage j).coupling := (hk.onFamily.onFamily j hj).le_coupling
    have hx0 : 0 < (T.stage j).coupling := by linarith
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hx0 _)
  have hr : ∀ j < k, stageRange T j ≤ 2 * stageRange T (j + 1) := by
    intro j hj
    have h1 : stageRange T j ≤ stageRange T (j + 1) + 1 := (hk.onFamily.onFamily j hj.le).isStep.2.2
    have h2 := hpos (j + 1) hj
    omega
  have hb := windowDepth_le_stageRange T k hD.L_ge hr (fun j hj => hpos (j + 1) hj)
  refine ⟨hb, ?_⟩
  have h := hb k le_rfl
  have h' : (windowDepth T k k : ℝ) ≤ 8 * (stageRange T k : ℝ) := by
    rw [sub_self, mul_zero, add_zero] at h
    linarith
  exact_mod_cast h'
end YangMills.Construction.CellWindows
end
