import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ResponseInTheExpansion.GasBlocksForget
import YangMills.Construction.ResponseInTheExpansion.HatsOfAgreeingGrounds
import YangMills.Construction.ResponseInTheExpansion.StoredScoresOfAGround
import YangMills.Construction.ResponseInTheExpansion.WeightsOnTwoTori
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.StepSettings YangMills.Construction.StepGas YangMills.Construction.RenormalizationStepParameters
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.BlockAverages
open YangMills.Construction.WeightedResponses YangMills.Construction.StepFloors
private theorem mul_sum_exp_le_exp_decay {rt f m Cn E₁ E₂ : ℝ} (hrt : 0 < rt) (hm : 0 ≤ m) (hf : f = rt / 2 ^ 12)
    (hE₁ : E₁ ≤ Real.exp (-(rt * m / 2 ^ 8))) (hE₂ : E₂ ≤ Real.exp (-(rt * m / 2 ^ 8)))
    (hbig : 2 * Cn ≤ 15 * rt * m / 2 ^ 12) (hC : 0 ≤ Cn) : Cn * (E₁ + E₂) ≤ Real.exp (-f * m) := by
  have e1 : Real.exp (-f * m) = Real.exp (-(rt * m / 2 ^ 8)) * Real.exp (15 * rt * m / 2 ^ 12) := by
    rw [← Real.exp_add, hf]
    congr 1
    ring
  have e2 : 2 * Cn ≤ Real.exp (15 * rt * m / 2 ^ 12) := by
    have := Real.add_one_le_exp (15 * rt * m / 2 ^ 12)
    linarith
  have hpos := Real.exp_pos (-(rt * m / 2 ^ 8))
  rw [e1]
  calc Cn * (E₁ + E₂) ≤ Cn * (2 * Real.exp (-(rt * m / 2 ^ 8))) :=
        mul_le_mul_of_nonneg_left (by linarith) hC
    _ = Real.exp (-(rt * m / 2 ^ 8)) * (2 * Cn) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left e2 hpos.le
private theorem abs_sub_sub_le_of_two_pairs {a b c d B₁ B₂ ε S σ Cn E : ℝ} (h1 : |a - c| ≤ (B₁ + σ) * ε * S)
    (h2 : |b - d| ≤ B₂ * ε * S)
    (hσ : 0 ≤ σ) (hS : 0 ≤ S) (hε : 0 ≤ ε) (hB : B₁ + B₂ ≤ Cn) (hC1 : 1 ≤ Cn) (hE : Cn * ε ≤ E) {s₂ S₂ : ℝ}
    (hs : σ ≤ s₂) (hSS : S ≤ S₂) :
    |(a - b) - (c - d)| ≤ (1 + s₂) * E * S₂ := by
  have hE0 : 0 ≤ E := le_trans (mul_nonneg (by linarith) hε) hE
  have e : (a - b) - (c - d) = (a - c) - (b - d) := by ring
  rw [e]
  have t := abs_sub (a - c) (b - d)
  have h3 : (B₁ + σ) * ε * S + B₂ * ε * S ≤ (1 + σ) * (Cn * ε) * S := by
    have h4 : B₁ + σ + B₂ ≤ (1 + σ) * Cn := by nlinarith
    have := mul_le_mul_of_nonneg_right h4 (mul_nonneg hε hS)
    nlinarith
  have h5 : (1 + σ) * (Cn * ε) * S ≤ (1 + s₂) * E * S₂ := by
    have h6 : (1 + σ) * (Cn * ε) ≤ (1 + s₂) * E :=
      mul_le_mul (by linarith) hE (mul_nonneg (by linarith) hε) (by linarith)
    exact mul_le_mul h6 hSS hS (mul_nonneg (by linarith) hE0)
  linarith
theorem centredGasBlockAgreement_holds (hB : gasBlockMeanDecorrelationStatement)
    (hW : WeightsCompatibleAcrossTori) (hfl : EventuallyFloorConditions) :
    centredGasBlockAgreementStatement := by
  obtain ⟨r₁, p₁, g₁⟩ := hB
  refine ⟨r₁, p₁, fun T hD hrt K => ?_⟩
  obtain ⟨y₁, B₁⟩ := g₁ T hD hrt K
  have hrtpos := hD.rt_pos
  set Cn : ℝ := 2 * (T.side : ℝ) ^ 4 + 16 * T.coupling + 1 with hCn
  have hCn0 : 0 < Cn := by
    have := hD.a_ge
    positivity
  set C₀ : ℝ := 2 ^ 21 * (T.side : ℝ) + 4 * T.n₀ + 2 ^ 17 + 2 + 2 ^ 22 * Cn / T.rt with hC₀
  have hC₀pos : 0 < C₀ := by positivity
  obtain ⟨yF, hF⟩ := hfl T hD C₀ 1 hC₀pos one_pos
  refine ⟨max y₁ yF, fun y hy R A hK hAt hFo => ?_⟩
  have hy1 : y₁ ≤ y := (le_max_left _ _).trans hy
  have hyF : yF ≤ y := (le_max_right _ _).trans hy
  have hR := hAt.onFamily
  have hxy := hR.le_coupling
  have hfit : R.params.Admissible := hFo.admissible
  have hodd := hfit.L_odd
  have hLq : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have haq : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
  have hrtq : R.params.rt = T.rt := by rw [hR.params_eq]; rfl
  have hLr : (R.params.side : ℝ) = T.side := by exact_mod_cast hLq
  have hFl := hF R.coupling (hyF.trans hxy)
  have hrC : C₀ ≤ R.range := hFl.range_ge
  have hrbig : 2 ^ 22 * Cn / T.rt ≤ R.range := by
    have h1 : 0 ≤ 4 * (T.n₀ : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ 2 ^ 17 := by positivity
    have h3 : 0 ≤ 2 ^ 21 * (T.side : ℝ) := by positivity
    linarith
  have hBk := B₁ y hy1 R A hK hAt
  have hsnn := hAt.admissible.price.nonneg
  have hx0 : 0 ≤ R.coupling := hFo.coupling_pos.le
  have hchx : 0 ≤ T.gasRate * R.coupling := (Real.rpow_nonneg hx0 _).trans hFl.gas_powers.2.1
  intro n n' _ _ G G' Y Y' m h h' s₂ hG hG' hn hn' hag hm hw hs₂
  have hNL : NeZero (n * R.params.side) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne R.params.side)⟩
  have hrr : (clusterRange R.nextCoupling : ℕ) = R.nextRange := rfl
  have hr1 := hFo.range_le
  have hr2 := hFo.nextRange_ge
  have hr64 : R.nextRange ≤ 64 * m := by
    have h1 : (R.nextRange : ℝ) ≤ 64 * m := by
      have : (R.nextRange : ℝ) / 64 ≤ m := hm
      linarith
    exact_mod_cast h1
  have hm₀ : 16 * R.frameReach ≤ m := by
    unfold StepSetup.frameReach
    omega
  have hG1 := coldCaseGround_trivialField_isAdmissible R n hn hfit
  have hG1' := coldCaseGround_trivialField_isAdmissible R n' hn' hfit
  have hag1 : GroundsAgreeNear (coldCaseGround R (trivialField n)) (coldCaseGround R (trivialField n')) Y Y' m :=
    ⟨hag.lt_extent, hag.lt_extent', fun _ _ => rfl, fun v _ => by simp [coldCaseGround], fun v _ => by
      rw [coldCaseGround_labelAt_eq_none, coldCaseGround_labelAt_eq_none]⟩
  have h1 := hBk n n' G G' Y Y' m h h' hG hG' hag hm₀ hw
  have h2 := hBk n n' _ _ Y Y' m h h' hG1 hG1' hag1 hm₀ hw
  rw [sum_recordedSiteScore_coldCaseGround A hodd] at h2
  have hS0 : 0 ≤ weightNorm R.params.side R.depth h :=
    le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
  have hσ0 : 0 ≤ ∑ o ∈ centredCube R.params.side, recordedSiteScore A G (fineSite R.params.side Y 0 o) :=
    Finset.sum_nonneg fun o _ => recordedSiteScore_nonneg A hsnn G _
  have hrtR : 0 < R.params.rt := by rw [hrtq]; exact hrtpos
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hE : Cn * (Real.exp (-(15 / 16 * R.params.rt * m / 2 ^ 5)) +
      Real.exp (-(2 * T.gasRate * R.coupling) - R.params.rt * m / 2 ^ 8)) ≤
      Real.exp (-R.params.decayRate * m) := by
    refine mul_sum_exp_le_exp_decay hrtR hm0 rfl ?_ ?_ ?_ hCn0.le
    · apply Real.exp_le_exp.mpr
      have : 0 ≤ R.params.rt * m := by positivity
      linarith
    · apply Real.exp_le_exp.mpr
      linarith
    · rw [hrtq]
      have h3 : 2 ^ 22 * Cn ≤ R.range * T.rt := by
        rwa [div_le_iff₀ hrtpos] at hrbig
      have h4 : (R.range : ℝ) ≤ 128 * m := by
        have : R.range ≤ 128 * m := by omega
        exact_mod_cast this
      have h5 : (R.range : ℝ) * T.rt ≤ 128 * m * T.rt := mul_le_mul_of_nonneg_right h4 hrtpos.le
      have h6 : 0 ≤ T.rt * m := by positivity
      nlinarith
  have hS2 : weightNorm R.params.side R.depth h ≤ weightNorm R.params.side (R.depth + 1) h :=
    (hW R.params.side hodd R.depth (n * R.params.side) (n * R.params.side)).2.2 h
  have hε0 : 0 ≤ Real.exp (-(15 / 16 * R.params.rt * m / 2 ^ 5)) +
      Real.exp (-(2 * T.gasRate * R.coupling) - R.params.rt * m / 2 ^ 8) := by positivity
  refine abs_sub_sub_le_of_two_pairs (B₁ := (R.params.side : ℝ) ^ 4 + 8 * R.params.coupling)
    (B₂ := (R.params.side : ℝ) ^ 4 + 0 + 8 * R.params.coupling) (Cn := Cn)
    (σ := ∑ o ∈ centredCube R.params.side, recordedSiteScore A G (fineSite R.params.side Y 0 o))
    (h1.trans (le_of_eq (by ring))) h2 hσ0 hS0 hε0 ?_ ?_ hE hs₂ hS2
  · rw [hLr, haq, hCn]
    linarith
  · rw [hCn]
    have := hD.a_ge
    have h0 : (0 : ℝ) ≤ (T.side : ℝ) ^ 4 := by positivity
    linarith
end YangMills.Construction.ResponseInTheExpansion
end
