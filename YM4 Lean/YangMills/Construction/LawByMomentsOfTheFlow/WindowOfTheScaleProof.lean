import YangMills.Construction.LawByMomentsOfTheFlow.FarLevelNearTheScale
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAlongTheTelescopeProof
import YangMills.Construction.LawByMomentsOfTheFlow.TheFlowAboveTheWindow
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheScale
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open Classical in
private theorem lastSeparated_le_scaleLevel {Λ : MomentParameters} (S : MomentPoint Λ) :
    S.lastSeparated ≤ S.data.scaleLevel := by apply _root_.YangMills.SharedProofs.p10799 <;> assumption
private theorem window_bounds_at_point {Λ : MomentParameters}
    (hadm : LevelTestFunctions.AdmissibleStep Λ.stepParams) (hg : 0 < Λ.g)
    (hfloor : Λ.stepParams.y₁ ≤ (Λ.g ^ 2)⁻¹) (hflow : LevelTestFunctions.CouplingFlowAboveWindow)
    (S : MomentPoint Λ) {C₀ : ℝ}
    (hnear : |S.coupling S.lastSeparated - S.scaleCoupling| ≤ C₀ * Real.log S.scaleCoupling)
    (hx1 : Real.exp 1 ≤ S.scaleCoupling)
    (hxw : 2 * |WeightedResponses.couplingWindowTop Λ.stepParams Λ.g| ≤ S.scaleCoupling)
    (hxl : 80 * Λ.stepParams.B * Real.log S.scaleCoupling ≤ S.scaleCoupling) :
    (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) ≤ S.scaleCoupling⁻¹ ∧
    (2 : ℝ) ^ (-(S.logIndex : ℝ)) ≤ S.scaleCoupling ^ (-(1 / 2) : ℝ) ∧ 3 ≤ S.logIndex ∧
    (S.scaleCoupling - WeightedResponses.couplingWindowTop Λ.stepParams Λ.g) / (2 * Λ.stepParams.B) ≤
      (S.data.windowLevel : ℝ) - (S.data.scaleLevel : ℝ) ∧
    4 * (S.logIndex : ℝ) ≤
      (S.scaleCoupling - WeightedResponses.couplingWindowTop Λ.stepParams Λ.g) / (2 * Λ.stepParams.B) ∧
    S.lastSeparated + 2 * S.logIndex + 3 ≤ S.data.windowLevel ∧
    ∀ u, S.lastSeparated ≤ u → u ≤ S.lastSeparated + 2 * S.logIndex + 3 →
      |S.coupling u - S.scaleCoupling| ≤ (|C₀| + 30 * Λ.stepParams.B) * Real.log S.scaleCoupling ∧
        Λ.stepParams.side ^ S.logIndex ≤ S.levelSide u := by
  have hf := hadm.admissible
  have hBp : 0 < Λ.stepParams.B := hf.B_pos
  obtain ⟨-, hrun⟩ := hflow Λ.stepParams hadm Λ.g hg hfloor S.β S.data.windowLevel S.window_le S.passage
  have hsK : S.data.scaleLevel ≤ S.data.windowLevel := S.supAdmissible.scaleLevel_le
  have hts : S.lastSeparated ≤ S.data.scaleLevel := lastSeparated_le_scaleLevel S
  have hrs : |S.coupling S.data.windowLevel - S.scaleCoupling| ≤
      2 * Λ.stepParams.B * ((S.data.windowLevel : ℝ) - (S.data.scaleLevel : ℝ)) :=
    hrun S.data.scaleLevel S.data.windowLevel hsK le_rfl
  have hxK : S.coupling S.data.windowLevel ≤ WeightedResponses.couplingWindowTop Λ.stepParams Λ.g :=
    S.passage.1
  have hxpos : 0 < S.scaleCoupling := (Real.exp_pos 1).trans_le hx1
  have hlog1 : 1 ≤ Real.log S.scaleCoupling := (Real.le_log_iff_exp_le hxpos).mpr hx1
  have hN1 : 4 * Real.log S.scaleCoupling ≤ (S.logIndex : ℝ) := Nat.le_ceil _
  have hN2 : (S.logIndex : ℝ) < 4 * Real.log S.scaleCoupling + 1 := Nat.ceil_lt_add_one (by linarith)
  have hN5 : (S.logIndex : ℝ) ≤ 5 * Real.log S.scaleCoupling := by linarith
  have hN3 : 3 ≤ S.logIndex := by
    have : (3 : ℝ) ≤ (S.logIndex : ℝ) := by linarith
    exact_mod_cast this
  have hLr : (3 : ℝ) ≤ (Λ.stepParams.side : ℝ) := by
    have := hf.L_ge
    exact_mod_cast (by omega : 3 ≤ Λ.stepParams.side)
  have hlL : 1 ≤ Real.log (Λ.stepParams.side : ℝ) := by
    refine (Real.le_log_iff_exp_le (by linarith)).mpr ?_
    have := Real.exp_one_lt_d9
    linarith
  have hwx : WeightedResponses.couplingWindowTop Λ.stepParams Λ.g ≤ S.scaleCoupling / 2 := by
    have := le_abs_self (WeightedResponses.couplingWindowTop Λ.stepParams Λ.g)
    linarith
  have hq : (S.scaleCoupling - WeightedResponses.couplingWindowTop Λ.stepParams Λ.g) / (2 * Λ.stepParams.B) ≤
      (S.data.windowLevel : ℝ) - (S.data.scaleLevel : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have := (abs_le.mp hrs).1
    linarith
  have h8 : 8 * Λ.stepParams.B * (S.logIndex : ℝ) ≤ 8 * Λ.stepParams.B * (5 * Real.log S.scaleCoupling) :=
    mul_le_mul_of_nonneg_left hN5 (by positivity)
  have hq2 : 4 * (S.logIndex : ℝ) ≤
      (S.scaleCoupling - WeightedResponses.couplingWindowTop Λ.stepParams Λ.g) / (2 * Λ.stepParams.B) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hK4 : S.data.scaleLevel + 4 * S.logIndex ≤ S.data.windowLevel := by
    have h1 : ((S.data.scaleLevel + 4 * S.logIndex : ℕ) : ℝ) ≤ (S.data.windowLevel : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h1
  refine ⟨?_, ?_, hN3, hq, hq2, by omega, fun u hu hu' => ⟨?_, ?_⟩⟩
  · rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_log (inv_pos.mpr hxpos), Real.log_inv]
    refine Real.exp_le_exp.mpr ?_
    have h1 : (S.logIndex : ℝ) / 4 ≤ Real.log (Λ.stepParams.side : ℝ) * ((S.logIndex : ℝ) / 4) :=
      le_mul_of_one_le_left (by positivity) hlL
    linarith
  · rw [Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos hxpos]
    refine Real.exp_le_exp.mpr ?_
    have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have h1 : (1 / 2 : ℝ) * (S.logIndex : ℝ) ≤ Real.log 2 * (S.logIndex : ℝ) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    linarith
  · have huK : u ≤ S.data.windowLevel := by omega
    have hd1 : |S.coupling u - S.coupling S.lastSeparated| ≤
        2 * Λ.stepParams.B * ((u : ℝ) - (S.lastSeparated : ℝ)) := hrun S.lastSeparated u hu huK
    have h2 : (u : ℝ) - (S.lastSeparated : ℝ) ≤ 15 * Real.log S.scaleCoupling := by
      have h3 : (u : ℝ) ≤ ((S.lastSeparated + 2 * S.logIndex + 3 : ℕ) : ℝ) := by exact_mod_cast hu'
      push_cast at h3
      linarith
    have h3 : 2 * Λ.stepParams.B * ((u : ℝ) - (S.lastSeparated : ℝ)) ≤
        2 * Λ.stepParams.B * (15 * Real.log S.scaleCoupling) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 := abs_sub_le (S.coupling u) (S.coupling S.lastSeparated) S.scaleCoupling
    have h5 : C₀ * Real.log S.scaleCoupling ≤ |C₀| * Real.log S.scaleCoupling :=
      mul_le_mul_of_nonneg_right (le_abs_self C₀) (by linarith)
    linarith
  · have hNu : S.logIndex ≤ S.data.windowLevel - u := by omega
    have hLpos : 0 < Λ.stepParams.side := by
      have := hf.L_ge
      omega
    have htop : 0 < S.data.period Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
    calc Λ.stepParams.side ^ S.logIndex ≤ Λ.stepParams.side ^ (S.data.windowLevel - u) :=
          Nat.pow_le_pow_right hLpos hNu
      _ ≤ S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - u) :=
          Nat.le_mul_of_pos_left _ htop
theorem scaleWindowStatement_of_farLevel (hF : farLevelNearScaleStatement)
    (hflow : LevelTestFunctions.CouplingFlowAboveWindow) : scaleWindowStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, h⟩ := hF a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hLo hL Tb hTa hTL hD hCS hCH hrt' hCd Kr hKr => ?_⟩
  obtain ⟨y₀, h⟩ := h L hLo hL Tb hTa hTL hD hCS hCH hrt' hCd Kr hKr
  refine ⟨max y₀ Tb.floorMin, fun y hy hR hB g hg hyg k _ hk hk8 R d hd => ?_⟩
  obtain ⟨C, c, X₀, -, -, hnear⟩ := h y ((le_max_left _ _).trans hy) hR hB g hg hyg k hk hk8 R d hd
  have hadm : LevelTestFunctions.AdmissibleStep (Tb.stepParameters y) :=
    ⟨hD.fits y ((le_max_right _ _).trans hy), hR, hB⟩
  have hBp : 0 < (Tb.stepParameters y).B := hadm.admissible.B_pos
  have hlo := Real.isLittleO_log_id_atTop.def
    (show (0 : ℝ) < 1 / (80 * (Tb.stepParameters y).B) by positivity)
  obtain ⟨x₃, h₃⟩ := Filter.eventually_atTop.mp hlo
  refine ⟨fun _ => |C 0| + 30 * (Tb.stepParameters y).B, 1,
    max y (max x₃ (max (2 * |WeightedResponses.couplingWindowTop (Tb.stepParameters y) g|) (Real.exp 1))),
    one_pos, le_max_left _ _, fun S hx => ?_⟩
  have hx3 : x₃ ≤ S.scaleCoupling := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxw : 2 * |WeightedResponses.couplingWindowTop (Tb.stepParameters y) g| ≤ S.scaleCoupling :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hx
  have hxe : Real.exp 1 ≤ S.scaleCoupling :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hx
  have hxpos : 0 < S.scaleCoupling := (Real.exp_pos 1).trans_le hxe
  have hlogpos : 0 < Real.log S.scaleCoupling := by
    have := (Real.le_log_iff_exp_le hxpos).mpr hxe
    linarith
  have hxl : 80 * (Tb.stepParameters y).B * Real.log S.scaleCoupling ≤ S.scaleCoupling := by
    have h1 := h₃ S.scaleCoupling hx3
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hlogpos, abs_of_pos hxpos] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 80 * (Tb.stepParameters y).B by positivity)
    have h3 : 80 * (Tb.stepParameters y).B * (1 / (80 * (Tb.stepParameters y).B) * S.scaleCoupling) =
        S.scaleCoupling := by
      field_simp
    linarith
  exact window_bounds_at_point (Λ := ⟨Tb, Kr, y, g, k, R, d⟩) hadm hg hyg hflow S (hnear S).2.2 hxe hxw hxl
end YangMills.Construction.MomentLaw
end
