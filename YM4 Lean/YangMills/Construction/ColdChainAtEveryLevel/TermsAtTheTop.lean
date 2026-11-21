import YangMills.Construction.ColdChainAtEveryLevel.TermsOfTheLevelsBelowTheTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.TopLevelTerms
variable {F : BlockAverages.BlockFrame} {j : ℕ}
theorem depth_lt_top (F : BlockAverages.BlockFrame) : F.depth < F.top := Nat.lt_succ_self _
theorem depth_succ_le_top (F : BlockAverages.BlockFrame) : F.depth + 1 ≤ F.top := le_rfl
theorem blockSide_pow_top_sub_depth_succ (F : BlockAverages.BlockFrame) :
    (F.blockSide : ℝ) ^ (F.top - (F.depth + 1)) = 1 := by
  have : F.top - (F.depth + 1) = 0 := Nat.sub_self _
  rw [this, pow_zero]
theorem linearPart_depth_succ (R : F.FieldChain) (W : BlockAverages.ChainChart F) (y : F.Site (F.depth + 1))
    (d : Fin 4) :
    BlockAverages.linearPart R W (F.depth + 1) y d =
      BlockAverages.parallelAverage (R F.depth) (BlockAverages.linearPart R W F.depth) (y, d) := by
  have h : ¬ F.depth + 1 < F.top := lt_irrefl _
  simp only [BlockAverages.linearPart]
  rw [if_neg h, add_zero]
theorem norm_parallelAverage_le_lineBlockAverage (hodd : Odd F.blockSide) (R : F.GaugeField j)
    (f : F.Site j → Fin 4 → ℍ[ℝ]) (c : F.Site (j + 1) × Fin 4) :
    ‖BlockAverages.parallelAverage R f c‖ ≤ BlockAverages.lineBlockAverage (fun x d => ‖f x d‖) c := by apply _root_.YangMills.Construction.BlockAverages.FirstVariation.norm_parallelAverage_le_lineBlockAverage <;> assumption
theorem weightedScaleNorm_linearPart_top_le (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide)
    {D : Finset F.Cell} (hD : D.card ≤ 81) (p : F.Site 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {W : BlockAverages.ChainChart F} {Bd : ℝ} (hBd : 0 ≤ Bd)
    (h0 : LevelRecursion.weightedScaleNorm D p θ 4 0 (fun x i => ‖(W.fine x i : ℍ[ℝ])‖) ≤ Bd)
    (h1 : ∀ m, m + 1 < F.top →
      LevelRecursion.weightedScaleNorm D p θ 2 (m + 1) (fun y d => ‖(W.coarse m y d : ℍ[ℝ])‖) ≤ Bd) :
    LevelRecursion.weightedScaleNorm D p θ 2 (F.depth + 1)
        (fun y d => ‖BlockAverages.linearPart R W (F.depth + 1) y d‖) ≤
      5 * (HullBounds.hullFactor F.blockSide * (20284 * Bd)) := by
  set a : (m : ℕ) → F.Site m → Fin 4 → ℝ := fun m x d => ‖BlockAverages.linearPart R W m x d‖ with ha
  set sf : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ := fun m y d => ‖(W.coarse m y d : ℍ[ℝ])‖ with hsf
  have ha0 : ∀ m x d, 0 ≤ a m x d := fun _ _ _ => norm_nonneg _
  have hs0 : ∀ m y d, 0 ≤ sf m y d := fun _ _ _ => norm_nonneg _
  have hrec : ∀ m, m + 1 < F.top → ∀ c ∈ BlockAverages.innerBonds D (m + 1),
      a (m + 1) c.1 c.2 ≤ BlockAverages.lineBlockAverage (a m) c + sf m c.1 c.2 := by
    intro m hm c _
    simp only [ha, hsf, BlockAverages.linearPart]
    rw [if_pos hm]
    exact (norm_add_le _ _).trans (add_le_add_left (norm_parallelAverage_le_lineBlockAverage hodd _ _ _) _)
  have hw := (LevelRecursion.weightedScaleNorm_le_of_recursion hodd h2 D p hθ a sf ha0 hs0 hrec F.depth
    (fun i hi => h1 i (lt_of_le_of_lt hi (depth_lt_top F))) hBd (depth_lt_top F)).1
  have hY : LevelRecursion.weightedScaleNorm D p θ 4 F.depth (a F.depth) ≤ 20284 * Bd := by
    have : LevelRecursion.weightedScaleNorm D p θ 4 0 (a 0) ≤ Bd := h0
    linarith
  have hpt : LevelRecursion.weightedScaleNorm D p θ 2 (F.depth + 1)
        (fun y d => ‖BlockAverages.linearPart R W (F.depth + 1) y d‖) ≤
      1 * LevelRecursion.weightedScaleNorm D p θ 2 (F.depth + 1)
        (fun y d => ComplexRemainders.bondHullSum (y, d) (a F.depth)) := by
    refine RealDirections.weightedScaleNorm_le_mul hodd p θ (by norm_num) (F.depth + 1) (by norm_num)
      (fun c _ => ?_) (fun c _ => ComplexRemainders.bondHullSum_nonneg _ (ha0 _))
    rw [abs_of_nonneg (norm_nonneg _), one_mul, linearPart_depth_succ]
    exact (norm_parallelAverage_le_lineBlockAverage hodd _ _ _).trans
      (ComplexDifferences.lineBlockAverage_le_bondHullSum hodd (ha0 _) _)
  have hh := LowerLevelTerms.weightedScaleNorm_two_bondHullSum_le hodd hD p hθ (m := F.depth) (depth_lt_top F)
    (g := a F.depth) (ha0 _) hY
  rw [blockSide_pow_top_sub_depth_succ, mul_one] at hh
  linarith
theorem weightedScaleNorm_unit_sub_linearPart_top_le (hodd : Odd F.blockSide) {D : Finset F.Cell}
    (hD : D.card ≤ 81) (p : F.Site 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {W : BlockAverages.ChainChart F} {C₀ s T Y A : ℝ}
    (hC : 0 ≤ C₀) (hs : 0 ≤ s) (hnear : ComplexLevels.ContoursNearUnit R D C₀ s) (hσ : C₀ * s ≤ 1 / 64)
    (hT0 : 0 ≤ T) (hT2 : 8 * (F.blockSide : ℝ) * T ≤ 1 / 1024)
    (hN : ∀ c ∈ BlockAverages.innerBonds D (F.depth + 1),
      ComplexRemainders.bondHullNorm c
        (ComplexLevels.levelDeviation R (BlockAverages.realChart W) F.depth) ≤ T)
    (hY : LevelRecursion.weightedScaleNorm D p θ 4 F.depth
      (fun z d => ‖ComplexLevels.levelDeviation R (BlockAverages.realChart W) F.depth z d‖) ≤ Y)
    (hA : LevelRecursion.weightedScaleNorm D p θ 2 F.depth
      (fun x d => ‖ComplexLevels.levelDeviation R (BlockAverages.realChart W) F.depth x d -
        ComplexifiedQuaternions.ofQuat (BlockAverages.linearPart R W F.depth x d)‖) ≤ A) :
    LevelRecursion.weightedScaleNorm D p θ 2 (F.depth + 1)
        (fun y d => ‖((BlockAverages.bondAverageGap R W F.depth (y, d) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) -
          1 - BlockAverages.linearPart R W (F.depth + 1) y d‖) ≤
      HullBounds.hullFactor F.blockSide * A + 200000 * (F.blockSide : ℝ) ^ 2 * (T + C₀ * s) *
        (5 * (HullBounds.hullFactor F.blockSide * Y)) := by
  have hθ0 := LowerLevelTerms.hullFactor_nonneg (F := F) hodd
  set K := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set a : F.Site F.depth → Fin 4 → ℝ := fun x d =>
    ‖ComplexLevels.levelDeviation R (BlockAverages.realChart W) F.depth x d -
      ComplexifiedQuaternions.ofQuat (BlockAverages.linearPart R W F.depth x d)‖ with ha
  have ha0 : ∀ x d, 0 ≤ a x d := fun _ _ => norm_nonneg _
  set n : F.Site (F.depth + 1) → Fin 4 → ℝ :=
    LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W) F.depth) with hn
  have hG : 0 ≤ K * (T + C₀ * s) := by positivity
  have hpt : LevelRecursion.weightedScaleNorm D p θ 2 (F.depth + 1)
      (fun y d => ‖((BlockAverages.bondAverageGap R W F.depth (y, d) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) -
        1 - BlockAverages.linearPart R W (F.depth + 1) y d‖) ≤
      1 * LevelRecursion.weightedScaleNorm D p θ 2 (F.depth + 1)
        (fun y d => ComplexRemainders.bondHullSum (y, d) a + K * (T + C₀ * s) * n y d) := by
    refine RealDirections.weightedScaleNorm_le_mul hodd p θ (by norm_num) (F.depth + 1) (by norm_num)
      (fun c hc => ?_)
      (fun c _ => add_nonneg (ComplexRemainders.bondHullSum_nonneg _ ha0)
        (mul_nonneg hG (LowerLevelTerms.bondHullField_nonneg _ _ _)))
    rw [abs_of_nonneg (norm_nonneg _), one_mul, linearPart_depth_succ]
    have hNc := hN c hc
    have hN0 : 0 ≤ ComplexRemainders.bondHullNorm c
        (ComplexLevels.levelDeviation R (BlockAverages.realChart W) F.depth) :=
      RealDirections.bondHullNorm_nonneg' _ _
    have hsp : ComplexDifferences.contourSpread F C₀ s F.depth ≤ C₀ * s :=
      ComplexDifferences.contourSpread_le hodd hC hs F.depth
    have key := LinearLevels.norm_linearizedUnit_sub_linearPart_le hodd R W (j := F.depth) (c := c)
      (σ := ComplexDifferences.contourSpread F C₀ s F.depth) (depth_succ_le_top F)
      (hsp.trans hσ) (hnear F.depth (depth_succ_le_top F) c hc) (by nlinarith)
    rw [RealChartTerms.linearizedUnit_realChart hodd (depth_succ_le_top F)] at key
    have e : BlockAverages.ofUnit (BlockAverages.bondAverageGap R W F.depth c) - 1 -
        ComplexifiedQuaternions.ofQuat
          (BlockAverages.parallelAverage (R F.depth) (BlockAverages.linearPart R W F.depth) c) =
        ComplexifiedQuaternions.ofQuat
          (((BlockAverages.bondAverageGap R W F.depth c : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 -
            BlockAverages.parallelAverage (R F.depth) (BlockAverages.linearPart R W F.depth) c) := by
      simp only [BlockAverages.ofUnit, PlaquetteSecondDifference.ofQuat_sub_eq,
        ComplexifiedQuaternions.ofQuat_one]
    rw [e, ComplexifiedQuaternions.norm_ofQuat] at key
    refine key.trans (add_le_add (ComplexDifferences.lineBlockAverage_le_bondHullSum hodd ha0 c) ?_)
    have b1 : ComplexRemainders.bondHullNorm c
          (ComplexLevels.levelDeviation R (BlockAverages.realChart W) F.depth) ^ 2 +
        ComplexDifferences.contourSpread F C₀ s F.depth *
          ComplexRemainders.bondHullNorm c
            (ComplexLevels.levelDeviation R (BlockAverages.realChart W) F.depth) ≤
        (T + C₀ * s) * ComplexRemainders.bondHullNorm c
          (ComplexLevels.levelDeviation R (BlockAverages.realChart W) F.depth) := by nlinarith
    have := mul_le_mul_of_nonneg_left b1 hK0
    have e2 : n c.1 c.2 = ComplexRemainders.bondHullNorm c
        (ComplexLevels.levelDeviation R (BlockAverages.realChart W) F.depth) := rfl
    rw [e2]
    nlinarith
  have hadd := RealDirections.weightedScaleNorm_add_le D p θ (P := 2) (by norm_num) (F.depth + 1)
    (fun y d => ComplexRemainders.bondHullSum (y, d) a) (fun y d => K * (T + C₀ * s) * n y d)
  have h1 : LevelRecursion.weightedScaleNorm D p θ 2 (F.depth + 1)
      (fun y d => ComplexRemainders.bondHullSum (y, d) a) ≤ HullBounds.hullFactor F.blockSide * A :=
    (HullBounds.weightedScaleNorm_bondHullSum_le hodd hθ (depth_lt_top F) p 2 (by norm_num) ha0).trans
      (mul_le_mul_of_nonneg_left hA hθ0)
  have hnl : LevelRecursion.weightedScaleNorm D p θ 2 (F.depth + 1) n ≤
      5 * (HullBounds.hullFactor F.blockSide * Y) := by
    have hh := LowerLevelTerms.weightedScaleNorm_two_bondHullSum_le hodd hD p hθ (m := F.depth) (depth_lt_top F)
      (g := fun z d => ‖ComplexLevels.levelDeviation R (BlockAverages.realChart W) F.depth z d‖)
      (fun _ _ => norm_nonneg _) hY
    rw [blockSide_pow_top_sub_depth_succ, mul_one] at hh
    exact hh
  have h3 : LevelRecursion.weightedScaleNorm D p θ 2 (F.depth + 1) (fun y d => K * (T + C₀ * s) * n y d) ≤
      K * (T + C₀ * s) * (5 * (HullBounds.hullFactor F.blockSide * Y)) := by
    refine le_trans (RealDirections.weightedScaleNorm_le_mul hodd p θ (by norm_num) (F.depth + 1)
      (κ := K * (T + C₀ * s)) hG (fun c _ => ?_) (fun c _ => LowerLevelTerms.bondHullField_nonneg _ _ _))
      (mul_le_mul_of_nonneg_left hnl hG)
    rw [abs_of_nonneg (mul_nonneg hG (LowerLevelTerms.bondHullField_nonneg _ _ _))]
  linarith
def topMainBound (κ K ν₁ ν₂ g₁ g₂ n₁ n₂ n₁₃ n₂₃ nΔ : ℝ) : ℝ :=
  κ * (ν₁ * ν₂) + (4 * κ + κ ^ 2 / 2) * nΔ + (128 * K * κ + 32 * K * κ ^ 2) * (n₁ * n₂) + 4 * (g₁ * n₂) +
    2 * (ν₁ * g₂) + 2 * κ * (n₁ * n₁₃) + 2 * κ * (n₂₃ * n₂)
theorem topMainBound_nonneg {κ K ν₁ ν₂ g₁ g₂ n₁ n₂ n₁₃ n₂₃ nΔ : ℝ} (hκ : 0 ≤ κ) (hK : 0 ≤ K) (h1 : 0 ≤ ν₁)
    (h2 : 0 ≤ ν₂) (h3 : 0 ≤ g₁) (h4 : 0 ≤ g₂) (h5 : 0 ≤ n₁) (h6 : 0 ≤ n₂) (h7 : 0 ≤ n₁₃) (h8 : 0 ≤ n₂₃)
    (h9 : 0 ≤ nΔ) :
    0 ≤ topMainBound κ K ν₁ ν₂ g₁ g₂ n₁ n₂ n₁₃ n₂₃ nΔ := by
  unfold topMainBound
  positivity
set_option maxHeartbeats 1000000 in
theorem le_topMainBound_add_cube {a q κ Lp nΔ K n₁ n₂ n₁₃ n₂₃ ν₁ ν₂ g₁ g₂ R₃ T Dd E D₃ : ℝ} (ha0 : 0 ≤ a)
    (hq0 : 0 ≤ q) (hκ : 0 ≤ κ)
    (ha : a ≤ κ) (hq : q ≤ κ) (hκ1 : κ ≤ 1 / 2) (hLp0 : 0 ≤ Lp) (hLp : Lp ≤ 1) (hnΔ : 0 ≤ nΔ) (hK : 0 ≤ K)
    (hn₁0 : 0 ≤ n₁) (hn₂0 : 0 ≤ n₂) (hn₁₃0 : 0 ≤ n₁₃) (hn₂₃0 : 0 ≤ n₂₃) (hν₁0 : 0 ≤ ν₁) (hν₂0 : 0 ≤ ν₂)
    (hg₁0 : 0 ≤ g₁) (hg₂0 : 0 ≤ g₂) (hn₁ : n₁ ≤ T) (hn₂ : n₂ ≤ T) (hn₁₃ : n₁₃ ≤ T) (hn₂₃ : n₂₃ ≤ T)
    (hν₁ : ν₁ ≤ T) (hν₂ : ν₂ ≤ T) (hR₃0 : 0 ≤ R₃) (hR₃ : R₃ ≤ 6 * K * T) (hR₃' : R₃ ≤ 1 / 2) (hT1 : T ≤ 1)
    (hD : Dd = 2 * nΔ + 64 * K * n₁ * n₂) (hD₃ : Dd ≤ D₃ * T ^ 2)
    (hE : E = Dd * q + (2 * n₁ + 2 * n₂) * Dd + Dd ^ 2 / 2 + g₁ * (2 * n₂) + ν₁ * g₂) :
    (a + R₃) * (ν₁ * ν₂ + E) + E + q ^ 2 / 2 * (Lp * nΔ + 64 * K * n₁ * n₂) +
        Lp * n₁₃ * ((2 * n₁) ^ 2 / 2 + 2 * n₁ * q) + Lp * n₂₃ * ((2 * n₂) ^ 2 / 2 + 2 * n₂ * q) ≤
      topMainBound κ K ν₁ ν₂ g₁ g₂ n₁ n₂ n₁₃ n₂₃ nΔ + (6 * K + 8 * D₃ + D₃ ^ 2 + 4) * T ^ 3 := by
  have hT0 : 0 ≤ T := hn₁0.trans hn₁
  have hDd0 : 0 ≤ Dd := by rw [hD]; positivity
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hνν : 0 ≤ ν₁ * ν₂ := by positivity
  have s1 : (a + R₃) * (ν₁ * ν₂ + E) + E ≤ a * (ν₁ * ν₂) + R₃ * (ν₁ * ν₂) + 2 * E := by
    have : (a + R₃) * E ≤ 1 * E := mul_le_mul_of_nonneg_right (by linarith) hE0
    linarith
  have s2 : a * (ν₁ * ν₂) ≤ κ * (ν₁ * ν₂) := mul_le_mul_of_nonneg_right ha hνν
  have s3 : R₃ * (ν₁ * ν₂) ≤ 6 * K * T ^ 3 := by
    have h : ν₁ * ν₂ ≤ T * T := mul_le_mul hν₁ hν₂ hν₂0 hT0
    calc R₃ * (ν₁ * ν₂) ≤ (6 * K * T) * (T * T) := mul_le_mul hR₃ h hνν (by positivity)
      _ = _ := by ring
  have s4 : Dd * q ≤ Dd * κ := mul_le_mul_of_nonneg_left hq hDd0
  have s5 : (2 * n₁ + 2 * n₂) * Dd ≤ 4 * D₃ * T ^ 3 := by
    calc (2 * n₁ + 2 * n₂) * Dd ≤ (4 * T) * (D₃ * T ^ 2) := mul_le_mul (by linarith) hD₃ hDd0 (by positivity)
      _ = _ := by ring
  have s6 : Dd ^ 2 / 2 ≤ D₃ ^ 2 / 2 * T ^ 3 := by
    have h1 := pow_le_pow_left₀ hDd0 hD₃ 2
    have h2 : (D₃ * T ^ 2) ^ 2 = D₃ ^ 2 * T ^ 4 := by ring
    have h3 : T ^ 4 ≤ T ^ 3 := by
      have := mul_le_mul_of_nonneg_left hT1 (by positivity : 0 ≤ T ^ 3)
      nlinarith
    have h4 : D₃ ^ 2 * T ^ 4 ≤ D₃ ^ 2 * T ^ 3 := mul_le_mul_of_nonneg_left h3 (by positivity)
    rw [h2] at h1
    linarith
  have hq2 : q ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ hq0 hq 2
  have s7 : q ^ 2 / 2 * (Lp * nΔ + 64 * K * n₁ * n₂) ≤ κ ^ 2 / 2 * (nΔ + 64 * K * (n₁ * n₂)) := by
    have h3 : Lp * nΔ + 64 * K * n₁ * n₂ ≤ nΔ + 64 * K * (n₁ * n₂) := by
      have := mul_le_mul_of_nonneg_right hLp hnΔ
      nlinarith
    exact mul_le_mul (by linarith) h3 (by positivity) (by positivity)
  have b3 : ∀ {n m : ℝ}, 0 ≤ n → 0 ≤ m → n ≤ T → m ≤ T →
      Lp * n * ((2 * m) ^ 2 / 2 + 2 * m * q) ≤ 2 * T ^ 3 + 2 * κ * (m * n) := by
    intro n m h0 h1 h2 h3
    have c1 : Lp * n * ((2 * m) ^ 2 / 2 + 2 * m * q) ≤ n * ((2 * m) ^ 2 / 2 + 2 * m * q) := by
      have := mul_le_mul_of_nonneg_right hLp (mul_nonneg h0 (by positivity : 0 ≤ (2 * m) ^ 2 / 2 + 2 * m * q))
      linarith
    have c2 : n * (m ^ 2) ≤ T * T ^ 2 := by
      have := pow_le_pow_left₀ h1 h3 2
      exact mul_le_mul h2 this (by positivity) hT0
    have c3 : n * (m * q) ≤ κ * (m * n) := by
      have := mul_le_mul_of_nonneg_left hq (mul_nonneg h0 h1)
      linarith
    linarith
  have s8 := b3 hn₁₃0 hn₁0 hn₁₃ hn₁
  have s9 := b3 hn₂₃0 hn₂0 hn₂₃ hn₂
  have e9 : 2 * κ * (n₂ * n₂₃) = 2 * κ * (n₂₃ * n₂) := by ring
  rw [e9] at s9
  have hDk : Dd * κ = 2 * κ * nΔ + 64 * K * κ * (n₁ * n₂) := by
    rw [hD]
    ring
  unfold topMainBound
  have e7 : κ ^ 2 / 2 * (nΔ + 64 * K * (n₁ * n₂)) = κ ^ 2 / 2 * nΔ + 32 * K * κ ^ 2 * (n₁ * n₂) := by ring
  rw [e7] at s7
  have e3 : (6 * K + 8 * D₃ + D₃ ^ 2 + 4) * T ^ 3 =
      6 * K * T ^ 3 + 2 * (4 * D₃ * T ^ 3) + 2 * (D₃ ^ 2 / 2 * T ^ 3) + 2 * T ^ 3 + 2 * T ^ 3 := by ring
  rw [e3]
  linarith
def topSecondConst (L : ℕ) : ℝ :=
  2 * (HullBounds.hullFactor L * LowerLevelTerms.levelSecondConst L) + 64 * (200000 * (L : ℝ) ^ 2)
def topCubicConst (L : ℕ) : ℝ := 6 * (200000 * (L : ℝ) ^ 2) + 8 * topSecondConst L + topSecondConst L ^ 2 + 4
def topUnitDefect (R : F.FieldChain) (W : BlockAverages.ChainChart F) : F.Site (F.depth + 1) → Fin 4 → ℝ :=
  fun y d => ‖((BlockAverages.bondAverageGap R W F.depth (y, d) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 -
    BlockAverages.linearPart R W (F.depth + 1) y d‖
def topLinearSize (R : F.FieldChain) (W : BlockAverages.ChainChart F) : F.Site (F.depth + 1) → Fin 4 → ℝ :=
  fun y d => ‖BlockAverages.linearPart R W (F.depth + 1) y d‖
structure TopDirectionBounds (D : Finset F.Cell) (p : F.Site 0) (θ : ℝ) (R : F.FieldChain)
    (W₁ W₂ : BlockAverages.ChainChart F) (T B₁ B₂ G₁ G₂ : ℝ) : Prop where
  B₁_le : B₁ ≤ T
  B₂_le : B₂ ≤ T
  sup₁ : ∀ c ∈ BlockAverages.innerBonds D (F.depth + 1), topLinearSize R W₁ c.1 c.2 ≤ T
  sup₂ : ∀ c ∈ BlockAverages.innerBonds D (F.depth + 1), topLinearSize R W₂ c.1 c.2 ≤ T
  nu₁ : LevelRecursion.weightedScaleNorm D p θ 2 (F.depth + 1) (topLinearSize R W₁) ≤
    5 * (HullBounds.hullFactor F.blockSide * (20284 * B₁))
  nu₂ : LevelRecursion.weightedScaleNorm D p (-θ) 2 (F.depth + 1) (topLinearSize R W₂) ≤
    5 * (HullBounds.hullFactor F.blockSide * (20284 * B₂))
  lin₁ : LevelRecursion.weightedScaleNorm D p θ 2 (F.depth + 1) (topUnitDefect R W₁) ≤ G₁
  lin₂ : LevelRecursion.weightedScaleNorm D p (-θ) 2 (F.depth + 1) (topUnitDefect R W₂) ≤ G₂
theorem mul_sq_add_mul_le_two_mul {K n T σ : ℝ} (hK : 0 ≤ K) (hn0 : 0 ≤ n) (hn : n ≤ T) (hT : T ≤ 1)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1) :
    K * (n ^ 2 + σ * n) ≤ 2 * K * T := by
  have b1 : n ^ 2 ≤ T := by nlinarith
  have b2 : σ * n ≤ T := by nlinarith
  have := mul_le_mul_of_nonneg_left (add_le_add b1 b2) hK
  linarith
theorem mul_le_sq_of_le {a b T : ℝ} (hb : 0 ≤ b) (hT : 0 ≤ T) (ha : a ≤ T) (hb' : b ≤ T) : a * b ≤ T ^ 2 := by
  have := mul_le_mul ha hb' hb hT
  rwa [← sq] at this
theorem bondHullField_second_diff_le (hodd : Odd F.blockSide) {D : Finset F.Cell} {p : F.Site 0} {θ : ℝ}
    {R : F.FieldChain} {W₁ W₂ W₃ : BlockAverages.ChainChart F} {C₀ s T B₁ B₂ : ℝ}
    (dir : LowerLevelTerms.SmallDirectionTriple D p θ R W₁ W₂ W₃ C₀ s T B₁ B₂)
    {c : F.Site (F.depth + 1) × Fin 4} (hc : c ∈ BlockAverages.innerBonds D (F.depth + 1)) :
    LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
        (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth +
          ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth)) c.1 c.2 ≤
      HullBounds.hullFactor F.blockSide * LowerLevelTerms.levelSecondConst F.blockSide * (B₁ * B₂) := by
  have hF0 := LowerLevelTerms.hullFactor_nonneg (F := F) hodd
  have h0 : |(0 : ℝ)| ≤ 1 / 8 := by norm_num
  have a := RealDirections.abs_le_finsetLpNorm (P := 2) (by norm_num) (BlockAverages.innerBonds D (F.depth + 1))
    (fun b => LevelRecursion.scaleWeight p 0 (F.depth + 1) b.1 *
      LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
        (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth +
          ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth)) b.1 b.2) hc
  simp only [RealDirections.scaleWeight_zero_angle, one_mul] at a
  rw [abs_of_nonneg (LowerLevelTerms.bondHullField_nonneg _ _ _)] at a
  refine a.trans ?_
  have e : LevelRecursion.finsetLpNorm 2 (BlockAverages.innerBonds D (F.depth + 1)) (fun b =>
      LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
        (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth +
          ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth)) b.1 b.2) =
      LevelRecursion.weightedScaleNorm D p 0 2 (F.depth + 1)
        (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
          (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth +
            ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth))) := by
    unfold LevelRecursion.weightedScaleNorm
    simp only [RealDirections.scaleWeight_zero_angle, one_mul]
  rw [e]
  refine (HullBounds.weightedScaleNorm_bondHullSum_le hodd h0 (depth_lt_top F) p 2 (by norm_num) (g := fun z d =>
    ‖(ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
      (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth +
        ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth)) z d‖)
    (fun _ _ => norm_nonneg _)).trans ?_
  have := mul_le_mul_of_nonneg_left (dir.second F.depth (depth_lt_top F)) hF0
  rw [mul_assoc (HullBounds.hullFactor F.blockSide)]
  exact this
set_option maxHeartbeats 2000000 in
theorem abs_bondEnergy_second_diff_top_le (hodd : Odd F.blockSide) {D : Finset F.Cell} {p : F.Site 0} {θ : ℝ}
    {R : F.FieldChain} {W₁ W₂ W₃ : BlockAverages.ChainChart F} {C₀ s T B₁ B₂ G₁ G₂ : ℝ}
    (V : F.GaugeField F.top) (hV : R F.top = V)
    (ref : LowerLevelTerms.ReferenceNear D R C₀ s)
    (dir : LowerLevelTerms.SmallDirectionTriple D p θ R W₁ W₂ W₃ C₀ s T B₁ B₂)
    (top : TopDirectionBounds D p θ R W₁ W₂ T B₁ B₂ G₁ G₂) {c : F.Site (F.depth + 1) × Fin 4}
    (hc : c ∈ BlockAverages.innerBonds D (F.depth + 1)) :
    |BondSecondDifference.bondEnergy R W₃ V F.depth c - BondSecondDifference.bondEnergy R W₁ V F.depth c -
        BondSecondDifference.bondEnergy R W₂ V F.depth c +
        BondSecondDifference.bondEnergy R (BlockAverages.zeroChart F) V F.depth c -
        inner ℝ (BlockAverages.linearPart R W₁ (F.depth + 1) c.1 c.2)
          (BlockAverages.linearPart R W₂ (F.depth + 1) c.1 c.2)| ≤
      topMainBound (C₀ * s) (200000 * (F.blockSide : ℝ) ^ 2) (topLinearSize R W₁ c.1 c.2)
        (topLinearSize R W₂ c.1 c.2) (topUnitDefect R W₁ c.1 c.2) (topUnitDefect R W₂ c.1 c.2)
        (LowerLevelTerms.bondHullField
          (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth) c.1 c.2)
        (LowerLevelTerms.bondHullField
          (ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth) c.1 c.2)
        (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
          ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth) c.1 c.2)
        (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
          ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth) c.1 c.2)
        (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
          (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth +
            ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth)) c.1 c.2) +
      topCubicConst F.blockSide * T ^ 3 := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hC := dir.C₀_pos
  have hs := dir.s_pos
  have hT0 := dir.T_nonneg
  have hT4 := dir.T_le
  have hT1 : T ≤ 1 := by linarith
  have hc64 := dir.spread_le
  have hB₂ := dir.B₂_nonneg
  set K := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hc00 : 0 ≤ C₀ * s := by positivity
  have hσ0 : 0 < ComplexDifferences.contourSpread F C₀ s F.depth := by
    have : 0 < (1 / (F.blockSide : ℝ)) ^ (F.top - (F.depth + 1)) := by positivity
    simp only [ComplexDifferences.contourSpread]
    positivity
  have hσc : ComplexDifferences.contourSpread F C₀ s F.depth ≤ C₀ * s :=
    ComplexDifferences.contourSpread_le hodd hC.le hs.le F.depth
  have hσ64 : ComplexDifferences.contourSpread F C₀ s F.depth ≤ 1 / 64 := hσc.trans hc64
  have hrad : 24 * (2 * T + ComplexDifferences.contourSpread F C₀ s F.depth) <
      ComplexDifferences.hullBallRadius F.blockSide := by
    have := dir.radius
    linarith
  have hLp1 : 12 * K * (2 * T + ComplexDifferences.contourSpread F C₀ s F.depth) ≤ 1 := by
    refine le_trans ?_ dir.lip
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hmn := depth_lt_top F
  have a1 := dir.hull₁ F.depth hmn c hc
  have a2 := dir.hull₂ F.depth hmn c hc
  have a3 := dir.hull₃ F.depth hmn c hc
  have a13 := dir.hull₁₃ F.depth hmn c hc
  have a23 := dir.hull₂₃ F.depth hmn c hc
  have hlen : |‖BlockAverages.contourAverage (R F.depth) c‖ - 1| ≤ C₀ * s := by
    have := ref.length F.depth hmn c hc
    have e : (1 / (F.blockSide : ℝ)) ^ (F.top - (F.depth + 1)) = 1 := by
      have : F.top - (F.depth + 1) = 0 := Nat.sub_self _
      rw [this, pow_zero]
    rw [e] at this
    simpa using this
  have hmis := ref.defect_top c hc
  have h0a : 0 ≤ K * (C₀ * s) := by positivity
  have h0b : 0 ≤ K * T := by positivity
  have hlip0 := dir.lip
  have hKN : ∀ n : ℝ, n ≤ T → K * (n + ComplexDifferences.contourSpread F C₀ s F.depth) ≤ 1 := by
    intro n hn
    have : K * (n + ComplexDifferences.contourSpread F C₀ s F.depth) ≤ K * (T + C₀ * s) :=
      mul_le_mul_of_nonneg_left (by linarith) hK0
    linarith
  have n₃0 : 0 ≤ ComplexRemainders.bondHullNorm c
      (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth) :=
    RealDirections.bondHullNorm_nonneg' _ _
  have hR2 : K * (ComplexRemainders.bondHullNorm c
        (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth) ^ 2 +
      ComplexDifferences.contourSpread F C₀ s F.depth * ComplexRemainders.bondHullNorm c
        (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth)) ≤ 2 * K * T :=
    mul_sq_add_mul_le_two_mul hK0 n₃0 a3 hT1 hσ0.le (by linarith)
  have hΔ := bondHullField_second_diff_le hodd dir hc
  set nΔ := LowerLevelTerms.bondHullField
    (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
      (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth +
        ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth)) c.1 c.2 with hnΔ
  have hnΔ0 : 0 ≤ nΔ := LowerLevelTerms.bondHullField_nonneg _ _ _
  set n₁ := LowerLevelTerms.bondHullField
    (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth) c.1 c.2 with hn₁
  set n₂ := LowerLevelTerms.bondHullField
    (ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth) c.1 c.2 with hn₂
  have n₁0 : 0 ≤ n₁ := LowerLevelTerms.bondHullField_nonneg _ _ _
  have n₂0 : 0 ≤ n₂ := LowerLevelTerms.bondHullField_nonneg _ _ _
  have hplain : BlockAverages.lineBlockAverage (fun x d =>
      ‖(ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
        (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth +
          ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth)) x d‖) c ≤ nΔ :=
    ComplexDifferences.lineBlockAverage_le_bondHullSum hodd (fun _ _ => norm_nonneg _) c
  have hLpΔ : 12 * K * (2 * T + ComplexDifferences.contourSpread F C₀ s F.depth) * nΔ ≤ nΔ := by
    have := mul_le_mul_of_nonneg_right hLp1 hnΔ0
    linarith
  have hDd : BlockAverages.lineBlockAverage (fun x d =>
      ‖(ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
        (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth +
          ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth)) x d‖) c +
      (12 * K * (2 * T + ComplexDifferences.contourSpread F C₀ s F.depth) * nΔ + 64 * K * n₁ * n₂) ≤
      2 * nΔ + 64 * K * n₁ * n₂ := by
    linarith
  have key := BondSecondDifference.abs_bondEnergy_secondDifference_sub_inner_le_top hodd (W₁ := W₁) (W₂ := W₂)
    (W₃ := W₃) (c := c) (σ := ComplexDifferences.contourSpread F C₀ s F.depth) (t := T) V hV rfl hσ0
    hσ64 (ref.contours F.depth (depth_succ_le_top F) c hc) hT0 hrad a1 a2 (by linarith) (hKN _ a1) (hKN _ a2)
    hDd le_rfl
  refine key.trans ?_
  have hmis0 := norm_nonneg
    (((BlockAverages.referenceDefect R F.depth c : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1)
  have hLp0 : 0 ≤ 12 * K * (2 * T + ComplexDifferences.contourSpread F C₀ s F.depth) :=
    mul_nonneg (mul_nonneg (by norm_num) hK0) (add_nonneg (mul_nonneg (by norm_num) hT0) hσ0.le)
  have hR0 : 0 ≤ K * (ComplexRemainders.bondHullNorm c
        (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth) ^ 2 +
      ComplexDifferences.contourSpread F C₀ s F.depth * ComplexRemainders.bondHullNorm c
        (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth)) :=
    mul_nonneg hK0 (add_nonneg (sq_nonneg _) (mul_nonneg hσ0.le n₃0))
  have hR6 : K * (ComplexRemainders.bondHullNorm c
        (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth) ^ 2 +
      ComplexDifferences.contourSpread F C₀ s F.depth * ComplexRemainders.bondHullNorm c
        (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth)) ≤ 6 * K * T := by
    linarith
  have hD₃ : 2 * nΔ + 64 * K * n₁ * n₂ ≤ topSecondConst F.blockSide * T ^ 2 := by
    have b0 : B₁ * B₂ ≤ T ^ 2 := mul_le_sq_of_le hB₂ hT0 top.B₁_le top.B₂_le
    have hcoef : 0 ≤ HullBounds.hullFactor F.blockSide * LowerLevelTerms.levelSecondConst F.blockSide := by
      have h1 := LowerLevelTerms.hullFactor_nonneg (F := F) hodd
      have h2 : 0 ≤ LowerLevelTerms.levelSecondConst F.blockSide := by
        unfold LowerLevelTerms.levelSecondConst RealDirections.secondSourceConst
        positivity
      positivity
    have b1 : nΔ ≤ HullBounds.hullFactor F.blockSide * LowerLevelTerms.levelSecondConst F.blockSide * T ^ 2 :=
      hΔ.trans (mul_le_mul_of_nonneg_left b0 hcoef)
    have b2 : n₁ * n₂ ≤ T ^ 2 := mul_le_sq_of_le n₂0 hT0 a1 a2
    have b3 : 64 * K * n₁ * n₂ ≤ 64 * K * T ^ 2 := by
      have := mul_le_mul_of_nonneg_left b2 hK0
      linarith
    simp only [topSecondConst]
    linarith
  have hk12 : C₀ * s ≤ 1 / 2 := by linarith
  exact le_topMainBound_add_cube (abs_nonneg _) hmis0 hc00 hlen hmis hk12 hLp0 hLp1 hnΔ0 hK0 n₁0 n₂0
    (LowerLevelTerms.bondHullField_nonneg _ _ _) (LowerLevelTerms.bondHullField_nonneg _ _ _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    a1 a2 a13 a23 (top.sup₁ c hc) (top.sup₂ c hc) hR0 hR6 (by linarith) hT1 rfl hD₃ rfl
theorem weighted_sum_le_of_products {κ K S₁ S₂ S₃ S₄ S₅ S₆ S₇ B₁ B₂ G Hh C₄ G₁ G₂ : ℝ} (hκ : 0 ≤ κ)
    (hκ1 : κ ≤ 1) (hK : 0 ≤ K)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hG : 0 ≤ G) (hHh : 0 ≤ Hh) (hC₄ : 0 ≤ C₄)
    (h1 : S₁ ≤ (C₄ * B₁) * (C₄ * B₂)) (h2 : S₂ ≤ 25 * (Hh * (B₁ * B₂)))
    (h3 : S₃ ≤ (5 * G * B₁) * (5 * G * B₂))
    (h4 : S₄ ≤ G₁ * (5 * G * B₂)) (h5 : S₅ ≤ (C₄ * B₁) * G₂) (h6 : S₆ ≤ (5 * G * B₁) * (5 * G * B₂))
    (h7 : S₇ ≤ (5 * G * B₁) * (5 * G * B₂)) :
    κ * S₁ + (4 * κ + κ ^ 2 / 2) * S₂ + (128 * K * κ + 32 * K * κ ^ 2) * S₃ + 4 * S₄ + 2 * S₅ + 2 * κ * S₆ +
        2 * κ * S₇ ≤
      κ * ((C₄ ^ 2 + 125 * Hh + 4000 * K * G ^ 2 + 100 * G ^ 2) * (B₁ * B₂)) + 20 * G * (G₁ * B₂) +
        2 * C₄ * (B₁ * G₂) := by
  set x := B₁ * B₂ with hx
  have hk2 : κ ^ 2 ≤ κ := by nlinarith
  have a1 : κ * S₁ ≤ κ * (C₄ ^ 2 * x) := by
    have e : (C₄ * B₁) * (C₄ * B₂) = C₄ ^ 2 * x := by rw [hx]; ring
    rw [e] at h1
    exact mul_le_mul_of_nonneg_left h1 hκ
  have hc2 : 4 * κ + κ ^ 2 / 2 ≤ 5 * κ := by linarith
  have hy0 : 0 ≤ 25 * (Hh * x) := by positivity
  have a2 : (4 * κ + κ ^ 2 / 2) * S₂ ≤ κ * (125 * Hh * x) := by
    have s1 : (4 * κ + κ ^ 2 / 2) * S₂ ≤ (4 * κ + κ ^ 2 / 2) * (25 * (Hh * x)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have s2 := mul_le_mul_of_nonneg_right hc2 hy0
    linarith
  have e3 : (5 * G * B₁) * (5 * G * B₂) = 25 * G ^ 2 * x := by rw [hx]; ring
  rw [e3] at h3 h6 h7
  have hz0 : 0 ≤ 25 * G ^ 2 * x := by positivity
  have hc3 : 128 * K * κ + 32 * K * κ ^ 2 ≤ 160 * K * κ := by
    have := mul_le_mul_of_nonneg_left hk2 hK
    linarith
  have a3 : (128 * K * κ + 32 * K * κ ^ 2) * S₃ ≤ κ * (4000 * K * G ^ 2 * x) := by
    have s1 : (128 * K * κ + 32 * K * κ ^ 2) * S₃ ≤ (128 * K * κ + 32 * K * κ ^ 2) * (25 * G ^ 2 * x) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have s2 := mul_le_mul_of_nonneg_right hc3 hz0
    linarith
  have a6 : 2 * κ * S₆ ≤ κ * (50 * G ^ 2 * x) := by
    have := mul_le_mul_of_nonneg_left h6 (by positivity : 0 ≤ 2 * κ)
    linarith
  have a7 : 2 * κ * S₇ ≤ κ * (50 * G ^ 2 * x) := by
    have := mul_le_mul_of_nonneg_left h7 (by positivity : 0 ≤ 2 * κ)
    linarith
  have e : κ * ((C₄ ^ 2 + 125 * Hh + 4000 * K * G ^ 2 + 100 * G ^ 2) * x) = κ * (C₄ ^ 2 * x) +
      κ * (125 * Hh * x) + κ * (4000 * K * G ^ 2 * x) + κ * (50 * G ^ 2 * x) + κ * (50 * G ^ 2 * x) := by ring
  rw [e]
  linarith
def topLinearConst (L : ℕ) : ℝ := 5 * (HullBounds.hullFactor L * 20284)
def topMainConst (L : ℕ) : ℝ :=
  topLinearConst L ^ 2 + 125 * (HullBounds.hullFactor L * LowerLevelTerms.levelSecondConst L) +
    4000 * (200000 * (L : ℝ) ^ 2) * (HullBounds.hullFactor L * 82272) ^ 2 +
    100 * (HullBounds.hullFactor L * 82272) ^ 2
set_option maxHeartbeats 2000000 in
theorem sum_topMainBound_le (hodd : Odd F.blockSide) {D : Finset F.Cell} (hD : D.card ≤ 81) {p : F.Site 0}
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {W₁ W₂ W₃ : BlockAverages.ChainChart F}
    {C₀ s T B₁ B₂ G₁ G₂ : ℝ}
    (dir : LowerLevelTerms.SmallDirectionTriple D p θ R W₁ W₂ W₃ C₀ s T B₁ B₂)
    (top : TopDirectionBounds D p θ R W₁ W₂ T B₁ B₂ G₁ G₂) :
    ∑ c ∈ BlockAverages.innerBonds D (F.depth + 1), topMainBound (C₀ * s) (200000 * (F.blockSide : ℝ) ^ 2)
        (topLinearSize R W₁ c.1 c.2) (topLinearSize R W₂ c.1 c.2)
        (topUnitDefect R W₁ c.1 c.2) (topUnitDefect R W₂ c.1 c.2)
        (LowerLevelTerms.bondHullField
          (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth) c.1 c.2)
        (LowerLevelTerms.bondHullField
          (ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth) c.1 c.2)
        (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
          ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth) c.1 c.2)
        (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
          ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth) c.1 c.2)
        (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
          (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth +
            ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth)) c.1 c.2) ≤
      C₀ * s * (topMainConst F.blockSide * (B₁ * B₂)) +
        20 * (HullBounds.hullFactor F.blockSide * 82272) * (G₁ * B₂) +
        2 * topLinearConst F.blockSide * (B₁ * G₂) := by
  have hθ' : |(-θ)| ≤ 1 / 8 := by rwa [abs_neg]
  have hC := dir.C₀_pos
  have hs := dir.s_pos
  have hB₁ := dir.B₁_nonneg
  have hB₂ := dir.B₂_nonneg
  have hc64 := dir.spread_le
  have hF0 := LowerLevelTerms.hullFactor_nonneg (F := F) hodd
  have hK0 : 0 ≤ 200000 * (F.blockSide : ℝ) ^ 2 := by positivity
  have hc00 : 0 ≤ C₀ * s := by positivity
  have hmn := depth_lt_top F
  have hl4 : 0 ≤ topLinearConst F.blockSide := by
    unfold topLinearConst
    positivity
  have en : ∀ B : ℝ, 5 * (HullBounds.hullFactor F.blockSide * (20284 * B)) = topLinearConst F.blockSide * B := by
    intro B
    unfold topLinearConst
    ring
  have hn1 : LevelRecursion.weightedScaleNorm D p θ 2 (F.depth + 1) (LowerLevelTerms.bondHullField
      (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth)) ≤
      5 * (HullBounds.hullFactor F.blockSide * 82272) * B₁ := by
    have := LowerLevelTerms.weightedScaleNorm_two_bondHullSum_le hodd hD p hθ hmn
      (g := fun z d => ‖ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth z d‖)
      (fun _ _ => norm_nonneg _) (dir.dev₁ F.depth hmn)
    rw [blockSide_pow_top_sub_depth_succ] at this
    refine this.trans (le_of_eq ?_)
    ring
  have hn2 : LevelRecursion.weightedScaleNorm D p (-θ) 2 (F.depth + 1) (LowerLevelTerms.bondHullField
      (ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth)) ≤
      5 * (HullBounds.hullFactor F.blockSide * 82272) * B₂ := by
    have := LowerLevelTerms.weightedScaleNorm_two_bondHullSum_le hodd hD p hθ' hmn
      (g := fun z d => ‖ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth z d‖)
      (fun _ _ => norm_nonneg _) (dir.dev₂ F.depth hmn)
    rw [blockSide_pow_top_sub_depth_succ] at this
    refine this.trans (le_of_eq ?_)
    ring
  have hn13 : LevelRecursion.weightedScaleNorm D p (-θ) 2 (F.depth + 1) (LowerLevelTerms.bondHullField
      (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
        ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth)) ≤
      5 * (HullBounds.hullFactor F.blockSide * 82272) * B₂ := by
    have := LowerLevelTerms.weightedScaleNorm_two_bondHullSum_le hodd hD p hθ' hmn
      (g := fun z d => ‖(ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
        ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth) z d‖)
      (fun _ _ => norm_nonneg _) (dir.dev₁₃ F.depth hmn)
    rw [blockSide_pow_top_sub_depth_succ] at this
    refine this.trans (le_of_eq ?_)
    ring
  have hn23 : LevelRecursion.weightedScaleNorm D p θ 2 (F.depth + 1) (LowerLevelTerms.bondHullField
      (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
        ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth)) ≤
      5 * (HullBounds.hullFactor F.blockSide * 82272) * B₁ := by
    have := LowerLevelTerms.weightedScaleNorm_two_bondHullSum_le hodd hD p hθ hmn
      (g := fun z d => ‖(ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
        ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth) z d‖)
      (fun _ _ => norm_nonneg _) (dir.dev₂₃ F.depth hmn)
    rw [blockSide_pow_top_sub_depth_succ] at this
    refine this.trans (le_of_eq ?_)
    ring
  have hG1 : 0 ≤ 5 * (HullBounds.hullFactor F.blockSide * 82272) * B₁ := by positivity
  have hnu₁ : LevelRecursion.weightedScaleNorm D p θ 2 (F.depth + 1) (topLinearSize R W₁) ≤
      topLinearConst F.blockSide * B₁ := by
    rw [← en]
    exact top.nu₁
  have hnu₂ : LevelRecursion.weightedScaleNorm D p (-θ) 2 (F.depth + 1) (topLinearSize R W₂) ≤
      topLinearConst F.blockSide * B₂ := by
    rw [← en]
    exact top.nu₂
  have S1 := (RealDirections.sum_mul_le_weightedScaleNorm hodd D p θ (F.depth + 1) (topLinearSize R W₁)
    (topLinearSize R W₂)).trans
    (mul_le_mul hnu₁ hnu₂ (RealDirections.weightedScaleNorm_nonneg' _ _ _ _ _ _) (by positivity))
  have S3 := (RealDirections.sum_mul_le_weightedScaleNorm hodd D p θ (F.depth + 1)
    (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth))
    (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth))).trans
    (mul_le_mul hn1 hn2 (RealDirections.weightedScaleNorm_nonneg' _ _ _ _ _ _) hG1)
  have hG₁0 : 0 ≤ G₁ := (RealDirections.weightedScaleNorm_nonneg' _ _ _ _ _ _).trans top.lin₁
  have S4 := (RealDirections.sum_mul_le_weightedScaleNorm hodd D p θ (F.depth + 1) (topUnitDefect R W₁)
    (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth))).trans
    (mul_le_mul top.lin₁ hn2 (RealDirections.weightedScaleNorm_nonneg' _ _ _ _ _ _) hG₁0)
  have S5 := (RealDirections.sum_mul_le_weightedScaleNorm hodd D p θ (F.depth + 1) (topLinearSize R W₁)
    (topUnitDefect R W₂)).trans
    (mul_le_mul hnu₁ top.lin₂ (RealDirections.weightedScaleNorm_nonneg' _ _ _ _ _ _) (by positivity))
  have S6 := (RealDirections.sum_mul_le_weightedScaleNorm hodd D p θ (F.depth + 1)
    (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth))
    (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
      ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth))).trans
      (mul_le_mul hn1 hn13 (RealDirections.weightedScaleNorm_nonneg' _ _ _ _ _ _) hG1)
  have S7 := (RealDirections.sum_mul_le_weightedScaleNorm hodd D p θ (F.depth + 1)
    (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
      ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth))
    (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth))).trans
    (mul_le_mul hn23 hn2 (RealDirections.weightedScaleNorm_nonneg' _ _ _ _ _ _) hG1)
  have S2 : ∑ c ∈ BlockAverages.innerBonds D (F.depth + 1),
      LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
        (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth +
          ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth)) c.1 c.2 ≤
      25 * (HullBounds.hullFactor F.blockSide * LowerLevelTerms.levelSecondConst F.blockSide * (B₁ * B₂)) := by
    have a := LowerLevelTerms.sum_le_weightedScaleNorm_zero hodd hD p (F.depth + 1)
      (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
        (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth +
          ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth)))
    rw [blockSide_pow_top_sub_depth_succ, one_pow, mul_one] at a
    refine a.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    have h0 : |(0 : ℝ)| ≤ 1 / 8 := by norm_num
    refine (HullBounds.weightedScaleNorm_bondHullSum_le hodd h0 hmn p 2 (by norm_num) (g := fun z d =>
      ‖(ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
        (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth +
          ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth)) z d‖)
      (fun _ _ => norm_nonneg _)).trans ?_
    have := mul_le_mul_of_nonneg_left (dir.second F.depth hmn) hF0
    rw [mul_assoc (HullBounds.hullFactor F.blockSide)]
    exact this
  have hsl : 0 ≤ LowerLevelTerms.levelSecondConst F.blockSide := by
    unfold LowerLevelTerms.levelSecondConst RealDirections.secondSourceConst
    positivity
  have fin := weighted_sum_le_of_products (κ := C₀ * s) (K := 200000 * (F.blockSide : ℝ) ^ 2)
    (G := HullBounds.hullFactor F.blockSide * 82272)
    (Hh := HullBounds.hullFactor F.blockSide * LowerLevelTerms.levelSecondConst F.blockSide)
    (C₄ := topLinearConst F.blockSide) hc00 (by linarith) hK0 hB₁ hB₂
    (by positivity) (by positivity) hl4 S1 S2 S3 S4 S5 S6 S7
  have e : ∑ c ∈ BlockAverages.innerBonds D (F.depth + 1),
        topMainBound (C₀ * s) (200000 * (F.blockSide : ℝ) ^ 2)
        (topLinearSize R W₁ c.1 c.2) (topLinearSize R W₂ c.1 c.2)
        (topUnitDefect R W₁ c.1 c.2) (topUnitDefect R W₂ c.1 c.2)
        (LowerLevelTerms.bondHullField
          (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth) c.1 c.2)
        (LowerLevelTerms.bondHullField
          (ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth) c.1 c.2)
        (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
          ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth) c.1 c.2)
        (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
          ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth) c.1 c.2)
        (LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
          (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth +
            ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth)) c.1 c.2) =
      C₀ * s * ∑ c ∈ BlockAverages.innerBonds D (F.depth + 1),
          topLinearSize R W₁ c.1 c.2 * topLinearSize R W₂ c.1 c.2 +
      (4 * (C₀ * s) + (C₀ * s) ^ 2 / 2) * ∑ c ∈ BlockAverages.innerBonds D (F.depth + 1),
        LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
          (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth +
            ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth)) c.1 c.2 +
      (128 * (200000 * (F.blockSide : ℝ) ^ 2) * (C₀ * s) + 32 * (200000 * (F.blockSide : ℝ) ^ 2) * (C₀ * s) ^ 2) *
        ∑ c ∈ BlockAverages.innerBonds D (F.depth + 1), LowerLevelTerms.bondHullField
          (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth) c.1 c.2 *
          LowerLevelTerms.bondHullField
            (ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth) c.1 c.2 +
      4 * ∑ c ∈ BlockAverages.innerBonds D (F.depth + 1), topUnitDefect R W₁ c.1 c.2 *
        LowerLevelTerms.bondHullField
          (ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth) c.1 c.2 +
      2 * ∑ c ∈ BlockAverages.innerBonds D (F.depth + 1), topLinearSize R W₁ c.1 c.2 * topUnitDefect R W₂ c.1 c.2 +
      2 * (C₀ * s) * ∑ c ∈ BlockAverages.innerBonds D (F.depth + 1), LowerLevelTerms.bondHullField
          (ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth) c.1 c.2 *
        LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
          ComplexLevels.levelDeviation R (BlockAverages.realChart W₁) F.depth) c.1 c.2 +
      2 * (C₀ * s) * ∑ c ∈ BlockAverages.innerBonds D (F.depth + 1),
        LowerLevelTerms.bondHullField (ComplexLevels.levelDeviation R (BlockAverages.realChart W₃) F.depth -
          ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth) c.1 c.2 *
          LowerLevelTerms.bondHullField
            (ComplexLevels.levelDeviation R (BlockAverages.realChart W₂) F.depth) c.1 c.2 := by
    simp only [topMainBound, Finset.sum_add_distrib, Finset.mul_sum]
  rw [e]
  refine fin.trans (le_of_eq ?_)
  simp only [topMainConst]
theorem sum_abs_bondEnergy_second_diff_top_le (hodd : Odd F.blockSide) {D : Finset F.Cell} (hD : D.card ≤ 81)
    {p : F.Site 0} {θ : ℝ}
    (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {W₁ W₂ W₃ : BlockAverages.ChainChart F} {C₀ s T B₁ B₂ G₁ G₂ : ℝ}
    (V : F.GaugeField F.top)
    (hV : R F.top = V) (ref : LowerLevelTerms.ReferenceNear D R C₀ s)
    (dir : LowerLevelTerms.SmallDirectionTriple D p θ R W₁ W₂ W₃ C₀ s T B₁ B₂)
    (top : TopDirectionBounds D p θ R W₁ W₂ T B₁ B₂ G₁ G₂) {Bj : Finset (F.Site (F.depth + 1) × Fin 4)}
    (hBj : Bj ⊆ BlockAverages.innerBonds D (F.depth + 1)) :
    ∑ c ∈ Bj, |BondSecondDifference.bondEnergy R W₃ V F.depth c - BondSecondDifference.bondEnergy R W₁ V F.depth c -
        BondSecondDifference.bondEnergy R W₂ V F.depth c +
        BondSecondDifference.bondEnergy R (BlockAverages.zeroChart F) V F.depth c -
        inner ℝ (BlockAverages.linearPart R W₁ (F.depth + 1) c.1 c.2)
          (BlockAverages.linearPart R W₂ (F.depth + 1) c.1 c.2)| ≤
      C₀ * s * (topMainConst F.blockSide * (B₁ * B₂)) +
        20 * (HullBounds.hullFactor F.blockSide * 82272) * (G₁ * B₂) +
        2 * topLinearConst F.blockSide * (B₁ * G₂) + (Bj.card : ℝ) * (topCubicConst F.blockSide * T ^ 3) := by
  have hC := dir.C₀_pos
  have hs := dir.s_pos
  have hκ0 : 0 ≤ C₀ * s := by positivity
  have hK0 : (0 : ℝ) ≤ 200000 * (F.blockSide : ℝ) ^ 2 := by positivity
  refine (Finset.sum_le_sum fun c hc => abs_bondEnergy_second_diff_top_le hodd V hV ref dir top (hBj hc)).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  refine add_le_add_left (le_trans (Finset.sum_le_sum_of_subset_of_nonneg hBj fun c _ _ => ?_)
    (sum_topMainBound_le hodd hD hθ dir top)) _
  exact topMainBound_nonneg hκ0 hK0 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (LowerLevelTerms.bondHullField_nonneg _ _ _) (LowerLevelTerms.bondHullField_nonneg _ _ _)
    (LowerLevelTerms.bondHullField_nonneg _ _ _) (LowerLevelTerms.bondHullField_nonneg _ _ _)
    (LowerLevelTerms.bondHullField_nonneg _ _ _)
end YangMills.Construction.TopLevelTerms
end
