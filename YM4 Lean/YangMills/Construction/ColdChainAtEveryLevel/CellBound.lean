import YangMills.Construction.ColdChainAtEveryLevel.CellBalls
import YangMills.Construction.ColdChainAtEveryLevel.CellSecondDifference
import YangMills.Construction.ColdChainAtEveryLevel.PlaquettesNearACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.CellBounds
open YangMills.Construction
open YangMills.Construction.BlockAverages YangMills.Construction.ComplexDifferences YangMills.Construction.ComplexCells YangMills.Construction.CellSources YangMills.Construction.ComplexLevels YangMills.Construction.ComplexRemainders YangMills.Construction.HullBounds YangMills.Construction.LevelRecursion YangMills.Construction.ComplexPlaquettes YangMills.Construction.PlaquettesNearCell YangMills.Construction.ComplexifiedQuaternions
variable {F : BlockFrame}
theorem norm_sum_complexBondTerm_second_diff_top_le {R : F.FieldChain} {S : Finset F.Cell} {z : F.Cell}
    {W₀ W₁ W₂ W₃ : ComplexChainChart F} {C₀ s η B : ℝ}
    (h : FourDeviationBalls R (cellBall S z 1) W₀ W₁ W₂ W₃ C₀ s η B) (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (V : F.GaugeField F.top)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) (p : F.Site 0) {T₁ T₂ T₁₂ ε : ℝ} (hT₁₂0 : 0 ≤ T₁₂) (hT₁0 : 0 ≤ T₁) (hT₂0 : 0 ≤ T₂)
    (hε0 : 0 < ε) (hε : 3 * (ε + C₀ * s) < hullBallRadius F.blockSide)
    (hK : 200000 * (F.blockSide : ℝ) ^ 2 * (ε + C₀ * s) ≤ 1)
    (htε : 3 * (2 * (hullBondCount F.blockSide * η)) ≤ ε / 48)
    (hT₁ : ∀ m, m < F.top → weightedScaleNorm (cellBall S z 1) p θ 4 m (deviationFirstDiff R W₀ W₁ m) ≤ T₁)
    (hT₂ : ∀ m, m < F.top → weightedScaleNorm (cellBall S z 1) p (-θ) 4 m (deviationFirstDiff R W₀ W₂ m) ≤ T₂)
    (hT₁₂ : ∀ m, m < F.top →
      weightedScaleNorm (cellBall S z 1) p 0 2 m (deviationSecondDiff R W₀ W₁ W₂ W₃ m) ≤ T₁₂)
    (j : ℕ) (hj : j + 1 = F.top) :
    ∑ c ∈ bondsOver S {z} (j + 1),
        ‖complexBondTerm R W₃ V j c - complexBondTerm R W₁ V j c - complexBondTerm R W₂ V j c +
          complexBondTerm R W₀ V j c‖ ≤
      4 * (240 * (hullFactor F.blockSide * T₁₂) +
        30720 / ε * ((hullFactor F.blockSide * T₁) * (hullFactor F.blockSide * T₂))) := by
  have hθ' : |(-θ)| ≤ 1 / 8 := by rwa [abs_neg]
  have hF0 := hullFactor_nonneg F.blockSide
  have hm' : j < F.top := by omega
  have hη0 := h.radius_nonneg
  have hH0 := hullBondCount_nonneg F.blockSide
  have hHη : 0 ≤ hullBondCount F.blockSide * η := mul_nonneg hH0 hη0
  have hη : η < 1 := by
    have := h.nine_radius_le_one
    linarith
  set t := 2 * (hullBondCount F.blockSide * η) with ht
  have ht0 : 0 ≤ t := mul_nonneg (by norm_num) hHη
  have hb : ∀ c ∈ bondsOver S {z} (j + 1),
      ‖complexBondTerm R W₃ V j c - complexBondTerm R W₁ V j c - complexBondTerm R W₂ V j c +
          complexBondTerm R W₀ V j c‖ ≤
        240 * (hullFactor F.blockSide * T₁₂) +
          30720 / ε * ((hullFactor F.blockSide * T₁) * (hullFactor F.blockSide * T₂)) := by
    intro c hc0
    have hc := bondsOver_singleton_subset_innerBonds hamb hodd (by omega) hc0
    set σ := contourSpread F C₀ s j with hσd
    have hσle : σ ≤ C₀ * s := contourSpread_le hodd h.const_pos.le h.scale_pos.le j
    have hN : ∀ {W : ComplexChainChart F}, DeviationBall R (cellBall S z 1) W η B →
        bondHullNorm c (levelDeviation R W j) ≤ t := by
      intro W hW
      have := hW.bondHullNorm_le hodd hη0 hm' hc
      rw [ht]
      linarith
    have hst := norm_complexBondTerm_second_diff_le_top hodd hj R W₀ W₁ W₂ W₃ V (t := t) (σ := C₀ * s)
      h.spread_le hε0
      (fun g hg π => (h.near j (by omega) c hc g hg π).trans (by
        have : C₀ * s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 = contourSpread F C₀ s j := rfl
        rw [this]
        exact hσle)) hε hK ht0 htε
      (hN h.ball₀) (hN h.ball₁) (hN h.ball₂) (hN h.ball₃)
      (FourDeviationBalls.bondHullNorm_sub_le h.ball₀ h.ball₁ hodd hη0 hm' hc)
      (FourDeviationBalls.bondHullNorm_sub_le h.ball₀ h.ball₂ hodd hη0 hm' hc)
      (h.ball₀.det_eq_one hodd hη hm' hc) (h.ball₁.det_eq_one hodd hη hm' hc)
      (h.ball₂.det_eq_one hodd hη hm' hc) (h.ball₃.det_eq_one hodd hη hm' hc)
    refine hst.trans ?_
    have q1 : scaleWeight p θ (j + 1) c.1 * bondHullSum c (deviationFirstDiff R W₀ W₁ j) ≤
        hullFactor F.blockSide * T₁ :=
      scaleWeight_mul_bondHullSum_le hodd hθ hm' p 4 (by norm_num) (fun _ _ => norm_nonneg _) (hT₁ j hm') hc
    have q2 : scaleWeight p (-θ) (j + 1) c.1 * bondHullSum c (deviationFirstDiff R W₀ W₂ j) ≤
        hullFactor F.blockSide * T₂ :=
      scaleWeight_mul_bondHullSum_le hodd hθ' hm' p 4 (by norm_num) (fun _ _ => norm_nonneg _) (hT₂ j hm') hc
    have q3 : scaleWeight p 0 (j + 1) c.1 * bondHullSum c (deviationSecondDiff R W₀ W₁ W₂ W₃ j) ≤
        hullFactor F.blockSide * T₁₂ :=
      scaleWeight_mul_bondHullSum_le hodd (θ := 0) (by norm_num) hm' p 2 (by norm_num)
        (fun _ _ => norm_nonneg _) (hT₁₂ j hm') hc
    have e0 : scaleWeight p 0 (j + 1) c.1 = 1 := by simp [scaleWeight]
    rw [e0, one_mul] at q3
    have hvv := scaleWeight_mul_scaleWeight_neg hodd p θ (j + 1) c.1
    have hvp' := scaleWeight_pos hodd p (-θ) (j + 1) c.1
    have hn₂0 : 0 ≤ bondHullSum c (deviationFirstDiff R W₀ W₂ j) :=
      bondHullSum_nonneg _ fun _ _ => norm_nonneg _
    have hnn : bondHullSum c (deviationFirstDiff R W₀ W₁ j) * bondHullSum c (deviationFirstDiff R W₀ W₂ j) ≤
        (hullFactor F.blockSide * T₁) * (hullFactor F.blockSide * T₂) := by
      have e : bondHullSum c (deviationFirstDiff R W₀ W₁ j) * bondHullSum c (deviationFirstDiff R W₀ W₂ j) =
          (scaleWeight p θ (j + 1) c.1 * bondHullSum c (deviationFirstDiff R W₀ W₁ j)) *
            (scaleWeight p (-θ) (j + 1) c.1 * bondHullSum c (deviationFirstDiff R W₀ W₂ j)) := by
        calc _ = (scaleWeight p θ (j + 1) c.1 * scaleWeight p (-θ) (j + 1) c.1) *
              (bondHullSum c (deviationFirstDiff R W₀ W₁ j) * bondHullSum c (deviationFirstDiff R W₀ W₂ j)) := by
                rw [hvv, one_mul]
          _ = _ := by ring
      rw [e]
      exact mul_le_mul q1 q2 (mul_nonneg hvp'.le hn₂0) (mul_nonneg hF0 hT₁0)
    have e1 : bondHullNorm c (levelDeviation R W₃ j - levelDeviation R W₁ j - levelDeviation R W₂ j +
        levelDeviation R W₀ j) = bondHullSum c (deviationSecondDiff R W₀ W₁ W₂ W₃ j) := rfl
    have e2 : bondHullNorm c (levelDeviation R W₁ j - levelDeviation R W₀ j) =
        bondHullSum c (deviationFirstDiff R W₀ W₁ j) := rfl
    have e3 : bondHullNorm c (levelDeviation R W₂ j - levelDeviation R W₀ j) =
        bondHullSum c (deviationFirstDiff R W₀ W₂ j) := rfl
    rw [e1, e2, e3, mul_assoc (30720 / ε)]
    exact add_le_add (mul_le_mul_of_nonneg_left q3 (by norm_num))
      (mul_le_mul_of_nonneg_left hnn (by positivity))
  have hx0 : 0 ≤ 240 * (hullFactor F.blockSide * T₁₂) +
      30720 / ε * ((hullFactor F.blockSide * T₁) * (hullFactor F.blockSide * T₂)) :=
    add_nonneg (mul_nonneg (by norm_num) (mul_nonneg hF0 hT₁₂0))
      (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hF0 hT₁0) (mul_nonneg hF0 hT₂0)))
  refine (Finset.sum_le_card_nsmul _ _ _ hb).trans ?_
  rw [nsmul_eq_mul]
  have hcard : ((bondsOver S {z} (j + 1)).card : ℝ) ≤ 4 := by
    exact_mod_cast card_bondsOver_singleton_top_le hj
  exact mul_le_mul_of_nonneg_right hcard hx0
section Arithmetic
def secondDiffConst (Hf K : ℝ) : ℝ :=
  2 * (142 * 8256 + 284 * (128 * K * (Hf * 80000) ^ 2 + 6 * 8256 + 8 * (Hf * 80000)))
def cellSecondDiffConst (Hf K ε a : ℝ) : ℝ :=
  129 ^ 2 + 44288 * 128 ^ 2 + |a| * (41300 + 2 * (Hf * secondDiffConst Hf K + 64 * K * (Hf * 80000) ^ 2) +
    4 * (Hf * 80000) + 4 * (240 * (Hf * secondDiffConst Hf K) + 30720 / ε * (Hf * 80000) ^ 2))
set_option maxHeartbeats 2000000 in
theorem cellSecondDiff_le_const {u₁ u₂ A₁ A₂ C₁ C₂ Hf K ε a T₁ T₂ T₁₂ Y Ts Ys : ℝ} (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hHf : 0 ≤ Hf) (hK : 0 ≤ K) (hε : 0 < ε)
    (hY0 : 0 ≤ Y) (hY : Y ≤ 1) (hTs0 : 0 ≤ Ts) (hTs : Ts ≤ 1) (hYs0 : 0 ≤ Ys) (hYs : Ys ≤ 1)
    (eT₁ : T₁ = 2 * (20000 * (2 * u₁) + 284 * (4 * A₁))) (eT₂ : T₂ = 2 * (20000 * (2 * u₂) + 284 * (4 * A₂)))
    (eT₁₂ : T₁₂ = 2 * (142 * (8256 * (u₁ * u₂)) + 284 * (128 * K * ((Hf * T₁) * (Hf * T₂)) +
      6 * 8256 * (A₁ * A₂) + 4 * (A₁ * (Hf * T₂)) + 4 * (A₂ * (Hf * T₁))))) :
    (C₁ + Ts * (128 * u₁)) * (C₂ + Ts * (128 * u₂)) + 44288 * ((128 * u₁) * (128 * u₂)) * Ys +
        |a| * ((41300 * (A₁ * A₂) + 2 * (Hf * T₁₂ + 64 * K * ((Hf * T₁) * (Hf * T₂))) * Y ^ 2 +
            2 * (Hf * T₁) * (A₂ * Y) + 2 * (Hf * T₂) * (A₁ * Y)) +
          4 * (240 * (Hf * T₁₂) + 30720 / ε * ((Hf * T₁) * (Hf * T₂)))) ≤
      cellSecondDiffConst Hf K ε a * ((u₁ + A₁ + C₁) * (u₂ + A₂ + C₂)) := by
  set P₁ := u₁ + A₁ + C₁ with hP₁
  set P₂ := u₂ + A₂ + C₂ with hP₂
  have hP₁0 : 0 ≤ P₁ := by positivity
  have hP₂0 : 0 ≤ P₂ := by positivity
  set X := P₁ * P₂ with hX
  have b₁ : u₁ ≤ P₁ := by linarith
  have b₂ : u₂ ≤ P₂ := by linarith
  have b₃ : A₁ ≤ P₁ := by linarith
  have b₄ : A₂ ≤ P₂ := by linarith
  have hT₁ : T₁ ≤ 80000 * P₁ := by
    rw [eT₁]
    linarith
  have hT₂ : T₂ ≤ 80000 * P₂ := by
    rw [eT₂]
    linarith
  have hT₁0 : 0 ≤ T₁ := by
    rw [eT₁]
    positivity
  have hT₂0 : 0 ≤ T₂ := by
    rw [eT₂]
    positivity
  set c := Hf * 80000 with hc
  have hc0 : 0 ≤ c := by positivity
  have hK₁ : Hf * T₁ ≤ c * P₁ := by
    have := mul_le_mul_of_nonneg_left hT₁ hHf
    rw [hc]
    linarith
  have hK₂ : Hf * T₂ ≤ c * P₂ := by
    have := mul_le_mul_of_nonneg_left hT₂ hHf
    rw [hc]
    linarith
  have hK₁0 : 0 ≤ Hf * T₁ := mul_nonneg hHf hT₁0
  have hK₂0 : 0 ≤ Hf * T₂ := mul_nonneg hHf hT₂0
  have hKK : (Hf * T₁) * (Hf * T₂) ≤ c ^ 2 * X := by
    have := mul_le_mul hK₁ hK₂ hK₂0 (mul_nonneg hc0 hP₁0)
    calc _ ≤ c * P₁ * (c * P₂) := this
      _ = _ := by rw [hX]; ring
  have hAA : A₁ * A₂ ≤ X := mul_le_mul b₃ b₄ hA₂ hP₁0
  have huu : u₁ * u₂ ≤ X := mul_le_mul b₁ b₂ hu₂ hP₁0
  have hAK₁ : A₁ * (Hf * T₂) ≤ c * X := by
    have := mul_le_mul b₃ hK₂ hK₂0 hP₁0
    calc _ ≤ P₁ * (c * P₂) := this
      _ = _ := by rw [hX]; ring
  have hAK₂ : A₂ * (Hf * T₁) ≤ c * X := by
    have := mul_le_mul b₄ hK₁ hK₁0 hP₂0
    calc _ ≤ P₂ * (c * P₁) := this
      _ = _ := by rw [hX]; ring
  have hT₁₂ : T₁₂ ≤ secondDiffConst Hf K * X := by
    rw [eT₁₂, secondDiffConst, ← hc]
    have h1 : 128 * K * ((Hf * T₁) * (Hf * T₂)) ≤ 128 * K * (c ^ 2 * X) :=
      mul_le_mul_of_nonneg_left hKK (by positivity)
    have e : 2 * (142 * 8256 + 284 * (128 * K * c ^ 2 + 6 * 8256 + 8 * c)) * X =
        2 * (142 * (8256 * X) + 284 * (128 * K * (c ^ 2 * X) + 6 * 8256 * X + 4 * (c * X) + 4 * (c * X))) := by
      ring
    rw [e]
    linarith
  set c₂ := secondDiffConst Hf K with hc₂
  have hHT : Hf * T₁₂ ≤ Hf * c₂ * X := by
    have := mul_le_mul_of_nonneg_left hT₁₂ hHf
    linarith
  have hYY : Y ^ 2 ≤ 1 := pow_le_one₀ hY0 hY
  have hplaq : (C₁ + Ts * (128 * u₁)) * (C₂ + Ts * (128 * u₂)) + 44288 * ((128 * u₁) * (128 * u₂)) * Ys ≤
      (129 ^ 2 + 44288 * 128 ^ 2) * X := by
    have k1 : Ts * (128 * u₁) ≤ 1 * (128 * u₁) := mul_le_mul_of_nonneg_right hTs (by positivity)
    have k2 : Ts * (128 * u₂) ≤ 1 * (128 * u₂) := mul_le_mul_of_nonneg_right hTs (by positivity)
    have h1 : C₁ + Ts * (128 * u₁) ≤ 129 * P₁ := by linarith
    have h2 : C₂ + Ts * (128 * u₂) ≤ 129 * P₂ := by linarith
    have h3 := mul_le_mul h1 h2 (add_nonneg hC₂ (mul_nonneg hTs0 (by positivity)))
      (mul_nonneg (by norm_num) hP₁0)
    have h4 : 44288 * ((128 * u₁) * (128 * u₂)) * Ys ≤ 44288 * ((128 * u₁) * (128 * u₂)) * 1 :=
      mul_le_mul_of_nonneg_left hYs (by positivity)
    have e : (129 ^ 2 + 44288 * 128 ^ 2) * X = 129 * P₁ * (129 * P₂) + 44288 * 128 ^ 2 * X := by
      rw [hX]
      ring
    rw [e]
    linarith
  have hmid : 41300 * (A₁ * A₂) + 2 * (Hf * T₁₂ + 64 * K * ((Hf * T₁) * (Hf * T₂))) * Y ^ 2 +
      2 * (Hf * T₁) * (A₂ * Y) + 2 * (Hf * T₂) * (A₁ * Y) ≤
      (41300 + 2 * (Hf * c₂ + 64 * K * c ^ 2) + 4 * c) * X := by
    have g0 : 0 ≤ Hf * T₁₂ + 64 * K * ((Hf * T₁) * (Hf * T₂)) := by
      have hT₁₂0 : 0 ≤ T₁₂ := by
        rw [eT₁₂]
        positivity
      positivity
    have g1 : 2 * (Hf * T₁₂ + 64 * K * ((Hf * T₁) * (Hf * T₂))) * Y ^ 2 ≤
        2 * (Hf * T₁₂ + 64 * K * ((Hf * T₁) * (Hf * T₂))) * 1 :=
      mul_le_mul_of_nonneg_left hYY (by positivity)
    have g2 : 64 * K * ((Hf * T₁) * (Hf * T₂)) ≤ 64 * K * (c ^ 2 * X) :=
      mul_le_mul_of_nonneg_left hKK (by positivity)
    have g3 : A₂ * Y ≤ A₂ * 1 := mul_le_mul_of_nonneg_left hY hA₂
    have g4 : A₁ * Y ≤ A₁ * 1 := mul_le_mul_of_nonneg_left hY hA₁
    have g5 : 2 * (Hf * T₁) * (A₂ * Y) ≤ 2 * (A₂ * (Hf * T₁)) := by
      have := mul_le_mul_of_nonneg_left g3 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK₁0)
      calc _ ≤ 2 * (Hf * T₁) * (A₂ * 1) := this
        _ = _ := by ring
    have g6 : 2 * (Hf * T₂) * (A₁ * Y) ≤ 2 * (A₁ * (Hf * T₂)) := by
      have := mul_le_mul_of_nonneg_left g4 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK₂0)
      calc _ ≤ 2 * (Hf * T₂) * (A₁ * 1) := this
        _ = _ := by ring
    have e : (41300 + 2 * (Hf * c₂ + 64 * K * c ^ 2) + 4 * c) * X =
        41300 * X + 2 * (Hf * c₂ * X + 64 * K * (c ^ 2 * X)) + 4 * (c * X) := by ring
    rw [e]
    linarith
  have htop : 4 * (240 * (Hf * T₁₂) + 30720 / ε * ((Hf * T₁) * (Hf * T₂))) ≤
      4 * (240 * (Hf * c₂) + 30720 / ε * c ^ 2) * X := by
    have g1 : 30720 / ε * ((Hf * T₁) * (Hf * T₂)) ≤ 30720 / ε * (c ^ 2 * X) :=
      mul_le_mul_of_nonneg_left hKK (by positivity)
    have e : 4 * (240 * (Hf * c₂) + 30720 / ε * c ^ 2) * X =
        4 * (240 * (Hf * c₂ * X) + 30720 / ε * (c ^ 2 * X)) := by ring
    rw [e]
    linarith
  have hsum := add_le_add hmid htop
  have habs := mul_le_mul_of_nonneg_left hsum (abs_nonneg a)
  have e : cellSecondDiffConst Hf K ε a * X = (129 ^ 2 + 44288 * 128 ^ 2) * X +
      |a| * ((41300 + 2 * (Hf * c₂ + 64 * K * c ^ 2) + 4 * c) * X +
        4 * (240 * (Hf * c₂) + 30720 / ε * c ^ 2) * X) := by
    unfold cellSecondDiffConst
    rw [← hc₂, ← hc]
    ring
  rw [e]
  linarith
end Arithmetic
section Main
def lowerBondSize (R : F.FieldChain) (W₀ W₁ W₂ : ComplexChainChart F)
    (x : Σ m : ℕ, F.Site (m + 1) × Fin 4) : ℝ :=
  ‖levelSource W₀ x.1 x.2.1 x.2.2 * ofUnit (referenceDefect R x.1 x.2) - 1‖ +
    ‖levelSource W₁ x.1 x.2.1 x.2.2 - levelSource W₀ x.1 x.2.1 x.2.2‖ +
    ‖levelSource W₂ x.1 x.2.1 x.2.2 - levelSource W₀ x.1 x.2.1 x.2.2‖
def baseSourceDiff (W W' : ComplexChainChart F) : F.Site 0 → Fin 4 → ComplexQuat := baseSource W' - baseSource W
set_option maxHeartbeats 4000000 in
theorem norm_complexCellTerms_second_diff_le_const (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (a : ℝ) {S : Finset F.Cell} {z : F.Cell}
    {R : F.FieldChain} (V : F.GaugeField F.top) {W₀ W₁ W₂ W₃ : ComplexChainChart F} {C₀ s η B ε σ₀ : ℝ}
    (h : FourDeviationBalls R (cellBall S z 1) W₀ W₁ W₂ W₃ C₀ s η B)
    (s₀ : SourcesSmall (cellBall S z 1) W₀) (s₁ : SourcesSmall (cellBall S z 1) W₁)
    (s₂ : SourcesSmall (cellBall S z 1) W₂) (s₃ : SourcesSmall (cellBall S z 1) W₃)
    (par : SourceParallelogram W₀ W₁ W₂ W₃) {θ : ℝ} (hθ : |θ| ≤ 1 / 8) (p : F.Site 0)
    (hB0 : 0 ≤ B) (hfac1 : 568 * firstDiffFactor F.blockSide C₀ s B * hullFactor F.blockSide ≤ 1)
    (hfac2 : 568 * secondDiffFactor F.blockSide C₀ s η * hullFactor F.blockSide ≤ 1)
    (hε0 : 0 < ε) (hε : 3 * (ε + C₀ * s) < hullBallRadius F.blockSide)
    (hK : 200000 * (F.blockSide : ℝ) ^ 2 * (ε + C₀ * s) ≤ 1)
    (htε : 3 * (2 * (hullBondCount F.blockSide * η)) ≤ ε / 48) (hσ₀ : 0 < σ₀)
    (hcurv : ∀ q ∈ plaquettesOver S {z} 0, ‖ofUnit (basePlaquetteHolonomy (R 0) q) - 1‖ ≤ σ₀)
    (hsmq : ∀ q ∈ plaquettesOver S {z} 0,
      24 * (3 * (plaquetteSourceNorm q (baseSource W₀) + plaquetteSourceNorm q (baseSourceDiff W₀ W₁) +
        plaquetteSourceNorm q (baseSourceDiff W₀ W₂)) + σ₀) < 1 / 256)
    (hTs : finsetLpNorm 4 (plaquettesOver S {z} 0) (fun q => 12 * 173 *
      (3 * (plaquetteSourceNorm q (baseSource W₀) + plaquetteSourceNorm q (baseSourceDiff W₀ W₁) +
        plaquetteSourceNorm q (baseSourceDiff W₀ W₂)) + σ₀)) ≤ 1)
    (hYs : finsetLpNorm 2 (plaquettesOver S {z} 0) (fun q => ‖plaquetteGap (R 0) q (baseSource W₀)‖ +
      ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₁)‖ +
      ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₂)‖ +
      ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₁ + baseSourceDiff W₀ W₂)‖) ≤ 1)
    (hY : finsetLpNorm 2 (lowerBonds (cellBall S z 1)) (lowerBondSize R W₀ W₁ W₂) ≤ 1)
    (hy1 : ∀ x ∈ lowerBonds (cellBall S z 1), lowerBondSize R W₀ W₁ W₂ x + ‖levelSource W₃ x.1 x.2.1 x.2.2 -
      levelSource W₁ x.1 x.2.1 x.2.2 - levelSource W₂ x.1 x.2.1 x.2.2 + levelSource W₀ x.1 x.2.1 x.2.2‖ ≤ 1) :
    ‖complexCellTerms a S R W₃ V z - complexCellTerms a S R W₁ V z - complexCellTerms a S R W₂ V z +
        complexCellTerms a S R W₀ V z‖ ≤
      cellSecondDiffConst (hullFactor F.blockSide) (200000 * (F.blockSide : ℝ) ^ 2) ε a *
        ((weightedScaleNorm (cellBall S z 1) p θ 4 0 (fun x i => ‖baseSource W₁ x i - baseSource W₀ x i‖) +
            finsetLpNorm 2 (lowerBonds (cellBall S z 1))
              (fun x => lowerScaleWeight p θ x * ‖upperSource W₁ x - upperSource W₀ x‖) +
            finsetLpNorm 2 (plaquettesOver S {z} 0)
              (fun q => scaleWeight p θ 0 q.1 * ‖covariantCurl (R 0) q (baseSourceDiff W₀ W₁)‖)) *
          (weightedScaleNorm (cellBall S z 1) p (-θ) 4 0 (fun x i => ‖baseSource W₂ x i - baseSource W₀ x i‖) +
            finsetLpNorm 2 (lowerBonds (cellBall S z 1))
              (fun x => lowerScaleWeight p (-θ) x * ‖upperSource W₂ x - upperSource W₀ x‖) +
            finsetLpNorm 2 (plaquettesOver S {z} 0)
              (fun q => scaleWeight p (-θ) 0 q.1 * ‖covariantCurl (R 0) q (baseSourceDiff W₀ W₂)‖))) := by
  have hθ' : |(-θ)| ≤ 1 / 8 := by rwa [abs_neg]
  have hD : (cellBall S z 1).card ≤ 81 := BlockLines.card_cellBall_one_le S z
  set D := cellBall S z 1 with hDd
  set u₁ := weightedScaleNorm D p θ 4 0 (fun x i => ‖baseSource W₁ x i - baseSource W₀ x i‖) with hu₁
  set u₂ := weightedScaleNorm D p (-θ) 4 0 (fun x i => ‖baseSource W₂ x i - baseSource W₀ x i‖) with hu₂
  set A₁ := finsetLpNorm 2 (lowerBonds D)
    (fun x => lowerScaleWeight p θ x * ‖upperSource W₁ x - upperSource W₀ x‖) with hA₁
  set A₂ := finsetLpNorm 2 (lowerBonds D)
    (fun x => lowerScaleWeight p (-θ) x * ‖upperSource W₂ x - upperSource W₀ x‖) with hA₂
  have hu₁0 : 0 ≤ u₁ := finsetLpNorm_nonneg _ _ _
  have hu₂0 : 0 ≤ u₂ := finsetLpNorm_nonneg _ _ _
  have hA₁0 : 0 ≤ A₁ := finsetLpNorm_nonneg _ _ _
  have hA₂0 : 0 ≤ A₂ := finsetLpNorm_nonneg _ _ _
  set T₁ := 2 * (20000 * (2 * u₁) + 284 * (4 * A₁)) with hT₁d
  set T₂ := 2 * (20000 * (2 * u₂) + 284 * (4 * A₂)) with hT₂d
  have hT₁0 : 0 ≤ T₁ := by positivity
  have hT₂0 : 0 ≤ T₂ := by positivity
  have hη : η < 1 := by
    have := h.nine_radius_le_one
    linarith
  have hsm3 : 3 * (2 * (hullBondCount F.blockSide * η) + C₀ * s) < hullBallRadius F.blockSide := by
    have := h.lt_hullBallRadius
    linarith
  have hT₁ : ∀ m, m < F.top → weightedScaleNorm D p θ 4 m (deviationFirstDiff R W₀ W₁ m) ≤ T₁ := fun m hm =>
    weightedScaleNorm_deviationFirstDiff_le hodd h2 hD p hθ h.const_pos h.scale_pos h.near h.ball₀ h.ball₁
      s₀ s₁ h.radius_nonneg hη hB0 h.spread_le hsm3 hfac1 m hm
  have hT₂ : ∀ m, m < F.top → weightedScaleNorm D p (-θ) 4 m (deviationFirstDiff R W₀ W₂ m) ≤ T₂ := fun m hm =>
    weightedScaleNorm_deviationFirstDiff_le hodd h2 hD p hθ' h.const_pos h.scale_pos h.near h.ball₀ h.ball₂
      s₀ s₂ h.radius_nonneg hη hB0 h.spread_le hsm3 hfac1 m hm
  set Hf := hullFactor F.blockSide with hHf
  have hHf0 : 0 ≤ Hf := hullFactor_nonneg _
  set K := 200000 * (F.blockSide : ℝ) ^ 2 with hKd
  have hK0 : 0 ≤ K := by positivity
  set T₁₂ := 2 * (142 * (8256 * (u₁ * u₂)) + 284 * (128 * K * ((Hf * T₁) * (Hf * T₂)) + 6 * 8256 * (A₁ * A₂) +
      4 * (A₁ * (Hf * T₂)) + 4 * (A₂ * (Hf * T₁)))) with hT₁₂d
  have hT₁₂0 : 0 ≤ T₁₂ := by positivity
  have hT₁₂ : ∀ m, m < F.top → weightedScaleNorm D p 0 2 m (deviationSecondDiff R W₀ W₁ W₂ W₃ m) ≤ T₁₂ :=
    fun m hm => weightedScaleNorm_deviationSecondDiff_le h hodd h2 s₀ s₁ s₂ s₃ par hθ p hT₁0 hT₂0 hT₁ hT₂
      hfac2 m hm
  have htop := norm_sum_complexBondTerm_second_diff_top_le h hamb hodd V hθ p hT₁₂0 hT₁0 hT₂0 hε0 hε hK htε
    hT₁ hT₂ hT₁₂
  have hTb0 : 0 ≤ 4 * (240 * (Hf * T₁₂) + 30720 / ε * ((Hf * T₁) * (Hf * T₂))) := by positivity
  have hsum := norm_complexCellTerms_second_diff_le hamb hodd a S z R V W₀ W₁ W₂ W₃ hTb0 htop
  refine hsum.trans ?_
  have e₁ : baseSource W₁ = baseSource W₀ + baseSourceDiff W₀ W₁ := by
    simp only [baseSourceDiff]
    abel
  have e₂ : baseSource W₂ = baseSource W₀ + baseSourceDiff W₀ W₂ := by
    simp only [baseSourceDiff]
    abel
  have e₃ : baseSource W₃ = baseSource W₀ + baseSourceDiff W₀ W₁ + baseSourceDiff W₀ W₂ := by
    funext x i
    simp only [Pi.add_apply, baseSourceDiff, Pi.sub_apply, par.base x i]
    abel
  have hplaq := sum_norm_complexPlaquetteTerm_second_diff_le (S := S) (z := z) hamb hodd (R 0)
    (ξ := baseSource W₀) (e₁ := baseSourceDiff W₀ W₁) (e₂ := baseSourceDiff W₀ W₂) hσ₀ hcurv p hθ hsmq
  have hpe : ∀ q, complexPlaquetteTerm (complexChartField R W₃ 0) q - complexPlaquetteTerm (complexChartField R W₁ 0) q -
      complexPlaquetteTerm (complexChartField R W₂ 0) q + complexPlaquetteTerm (complexChartField R W₀ 0) q =
      complexPlaquetteTerm (expField (R 0) (baseSource W₀ + baseSourceDiff W₀ W₁ + baseSourceDiff W₀ W₂)) q -
      complexPlaquetteTerm (expField (R 0) (baseSource W₀ + baseSourceDiff W₀ W₁)) q -
      complexPlaquetteTerm (expField (R 0) (baseSource W₀ + baseSourceDiff W₀ W₂)) q +
      complexPlaquetteTerm (expField (R 0) (baseSource W₀)) q := by
    intro q
    rw [complexChartField_zero, complexChartField_zero, complexChartField_zero, complexChartField_zero,
      ← e₃, ← e₁, ← e₂]
  simp only [hpe]
  have eu₁ : weightedScaleNorm D p θ 4 0 (fun x i => ‖baseSourceDiff W₀ W₁ x i‖) = u₁ := rfl
  have eu₂ : weightedScaleNorm D p (-θ) 4 0 (fun x i => ‖baseSourceDiff W₀ W₂ x i‖) = u₂ := rfl
  rw [eu₁, eu₂] at hplaq
  have hss : ∀ x ∈ lowerBonds D, ‖upperSource W₀ x‖ ≤ 1 / 8000 ∧ ‖upperSource W₁ x‖ ≤ 1 / 8000 ∧
      ‖upperSource W₂ x‖ ≤ 1 / 8000 :=
    fun x hx => ⟨s₀.upper_le x hx, s₁.upper_le x hx, s₂.upper_le x hx⟩
  have hmid := sum_norm_complexBondTerm_second_diff_le h hodd V hθ p hT₁0 hT₂0 hT₁₂0 hA₁0 hA₂0
    (finsetLpNorm_nonneg 2 (lowerBonds D) (lowerBondSize R W₀ W₁ W₂)) hT₁ hT₂ hT₁₂
    (fun x => ‖upperSource W₁ x - upperSource W₀ x‖) (fun x => ‖upperSource W₂ x - upperSource W₀ x‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (fun x hx => norm_unitExp_sub_le (((hss x hx).1).trans (by norm_num)) (((hss x hx).2.1).trans (by norm_num)))
    (fun x hx => norm_unitExp_sub_le (((hss x hx).1).trans (by norm_num)) (((hss x hx).2.2).trans (by norm_num)))
    (fun x hx => norm_unitExp_parallelogram_le (par.upper x) (hss x hx).1 (hss x hx).2.1 (hss x hx).2.2)
    (lowerBondSize R W₀ W₁ W₂) (fun _ _ => rfl) hy1 le_rfl le_rfl le_rfl
  set Y := finsetLpNorm 2 (lowerBonds D) (lowerBondSize R W₀ W₁ W₂) with hYd
  have hY0 : 0 ≤ Y := finsetLpNorm_nonneg _ _ _
  set C₁ := finsetLpNorm 2 (plaquettesOver S {z} 0)
    (fun q => scaleWeight p θ 0 q.1 * ‖covariantCurl (R 0) q (baseSourceDiff W₀ W₁)‖) with hC₁
  set C₂ := finsetLpNorm 2 (plaquettesOver S {z} 0)
    (fun q => scaleWeight p (-θ) 0 q.1 * ‖covariantCurl (R 0) q (baseSourceDiff W₀ W₂)‖) with hC₂
  set Ts := finsetLpNorm 4 (plaquettesOver S {z} 0) (fun q => 12 * 173 *
      (3 * (plaquetteSourceNorm q (baseSource W₀) + plaquetteSourceNorm q (baseSourceDiff W₀ W₁) +
        plaquetteSourceNorm q (baseSourceDiff W₀ W₂)) + σ₀)) with hTsd
  set Ys := finsetLpNorm 2 (plaquettesOver S {z} 0) (fun q => ‖plaquetteGap (R 0) q (baseSource W₀)‖ +
      ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₁)‖ +
      ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₂)‖ +
      ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₁ + baseSourceDiff W₀ W₂)‖) with hYsd
  have harith := cellSecondDiff_le_const (a := a) (Y := Y) (Ts := Ts) (Ys := Ys) (C₁ := C₁) (C₂ := C₂)
    hu₁0 hu₂0 hA₁0 hA₂0 (finsetLpNorm_nonneg _ _ _) (finsetLpNorm_nonneg _ _ _)
    hHf0 hK0 hε0 hY0 hY (finsetLpNorm_nonneg _ _ _) hTs (finsetLpNorm_nonneg _ _ _) hYs hT₁d hT₂d hT₁₂d
  have habs := mul_le_mul_of_nonneg_left (add_le_add hmid (le_refl (4 * (240 * (Hf * T₁₂) +
    30720 / ε * ((Hf * T₁) * (Hf * T₂)))))) (abs_nonneg a)
  refine le_trans (add_le_add hplaq habs) ?_
  exact harith
end Main
end YangMills.Construction.CellBounds
end
