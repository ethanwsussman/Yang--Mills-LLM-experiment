import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfASplitCriticalPoint
import YangMills.Construction.ColdChainAtEveryLevel.CarriedFormsOfTheLevels
import YangMills.Construction.ColdChainAtEveryLevel.ColdnessOfTheFieldBelowTheTop
import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.LastMisfitNearACell
import YangMills.Construction.ColdChainAtEveryLevel.LocalBoundsOfASmallChain
import YangMills.Construction.ColdChainAtEveryLevel.MisfitsDownTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace SplitCriticalPointBounds
open BlockLines BlockWeights
variable {F : BlockFrame}
theorem weightedNorm_congr {S : Finset F.Cell} {R : F.FieldChain} {U U' : ChainChart F} (h : ChartEqOnBonds S U U')
    (w : F.SiteWeights) : weightedNorm S R U w = weightedNorm S R U' w := by
  classical
  have hB : ∀ B : Finset F.Cell, localNormSq S B R U w = localNormSq S B R U' w := by
    intro B
    unfold localNormSq
    congr 1
    · congr 1
      · congr 1
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [h.1 b (Finset.mem_filter.1 hb).1]
      · refine Finset.sum_congr rfl fun q hq => ?_
        have hq1 := (Finset.mem_filter.1 hq).1
        have hc := (Finset.mem_filter.1 hq1).2.2
        have c1 : q.1 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
        have c2 : q.1 + unitStep 0 q.2.1 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
        have c3 : q.1 + unitStep 0 q.2.2 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
        have c4 : q.1 + unitStep 0 q.2.1 + unitStep 0 q.2.2 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
        have e1 := h.1 (q.1, q.2.1) (ChartCoordinates.mem_innerBonds c1 c2)
        have e2 := h.1 (q.1 + unitStep 0 q.2.1, q.2.2) (ChartCoordinates.mem_innerBonds c2 c4)
        have e3 := h.1 (q.1 + unitStep 0 q.2.2, q.2.1) (ChartCoordinates.mem_innerBonds c3 (by rwa [add_right_comm]))
        have e4 := h.1 (q.1, q.2.2) (ChartCoordinates.mem_innerBonds c1 c3)
        simp only at e1 e2 e3 e4
        have : linearizedCurl (R 0) U.fine q = linearizedCurl (R 0) U'.fine q := by
          unfold linearizedCurl
          simp only [e1, e2, e3, e4]
        rw [this]
    · refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c hc => ?_
      have hj' : j + 1 < F.top := by
        have := Finset.mem_range.1 hj
        have hn : 0 < F.top := Nat.succ_pos _
        omega
      rw [h.2 j hj' c (Finset.mem_filter.1 hc).1]
  unfold weightedNorm localNorm
  simp only [hB]
theorem add_pow_four_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have h1 : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
  have h2 : (x ^ 2 + y ^ 2) ^ 2 ≤ 2 * (x ^ 4 + y ^ 4) := by nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
  have h3 := pow_le_pow_left₀ (by positivity) h1 2
  nlinarith
theorem add_sq_le_two_mul {x y : ℝ} : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
theorem linearizedCurl_add (R0 : F.GaugeField 0) (u v : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (q : F.Site 0 × Fin 4 × Fin 4) :
    linearizedCurl R0 (fun x i => u x i + (1 : ℝ) • v x i) q = linearizedCurl R0 u q + linearizedCurl R0 v q := by
  unfold linearizedCurl
  simp only [one_smul, Submodule.coe_add, adjointAction_add]
  abel
theorem localNormSq_chartSum_le (S B : Finset F.Cell) (R : F.FieldChain) (A A' : ChainChart F) (w : F.SiteWeights)
    (hw : ∀ (j : ℕ) (x : F.Site j), 0 ≤ w j x) :
    localNormSq S B R (chartSum A A') w ≤ 3 * (localNormSq S B R A w + localNormSq S B R A' w) := by
  unfold localNormSq
  set a1 := ∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4 with ha1
  set a2 := ∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖A'.fine b.1 b.2‖) ^ 4 with ha2
  have ha10 : 0 ≤ a1 := Finset.sum_nonneg fun b _ => by have := hw 0 b.1; positivity
  have ha20 : 0 ≤ a2 := Finset.sum_nonneg fun b _ => by have := hw 0 b.1; positivity
  have h1 : Real.sqrt (∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖(chartSum A A').fine b.1 b.2‖) ^ 4) ≤
      3 * (Real.sqrt a1 + Real.sqrt a2) := by
    have h2 : ∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖(chartSum A A').fine b.1 b.2‖) ^ 4 ≤ 8 * (a1 + a2) := by
      rw [ha1, ha2, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_le_sum fun b _ => ?_
      have hw0 := hw 0 b.1
      have e : (chartSum A A').fine b.1 b.2 = A.fine b.1 b.2 + (1 : ℝ) • A'.fine b.1 b.2 := rfl
      have h3 : w 0 b.1 * ‖(chartSum A A').fine b.1 b.2‖ ≤ w 0 b.1 * ‖A.fine b.1 b.2‖ + w 0 b.1 * ‖A'.fine b.1 b.2‖ := by
        rw [e, one_smul, ← mul_add]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hw0
      have h4 := pow_le_pow_left₀ (by positivity) h3 4
      exact h4.trans (add_pow_four_le (by positivity) (by positivity))
    have h5 := Real.sqrt_le_sqrt h2
    refine h5.trans ?_
    have h6 : Real.sqrt (8 * (a1 + a2)) ≤ 3 * Real.sqrt (a1 + a2) := by
      rw [Real.sqrt_mul (by norm_num)]
      refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      exact Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    have h7 : Real.sqrt (a1 + a2) ≤ Real.sqrt a1 + Real.sqrt a2 := by
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      nlinarith [Real.sq_sqrt ha10, Real.sq_sqrt ha20, mul_nonneg (Real.sqrt_nonneg a1) (Real.sqrt_nonneg a2)]
    linarith
  have h2 : ∑ q ∈ plaquettesOver S B 0, (w 0 q.1 * ‖linearizedCurl (R 0) (chartSum A A').fine q‖) ^ 2 ≤
      2 * (∑ q ∈ plaquettesOver S B 0, (w 0 q.1 * ‖linearizedCurl (R 0) A.fine q‖) ^ 2 +
        ∑ q ∈ plaquettesOver S B 0, (w 0 q.1 * ‖linearizedCurl (R 0) A'.fine q‖) ^ 2) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    have hw0 := hw 0 q.1
    have e : linearizedCurl (R 0) (chartSum A A').fine q = linearizedCurl (R 0) A.fine q + linearizedCurl (R 0) A'.fine q :=
      linearizedCurl_add (R 0) A.fine A'.fine q
    have h3 : w 0 q.1 * ‖linearizedCurl (R 0) (chartSum A A').fine q‖ ≤
        w 0 q.1 * ‖linearizedCurl (R 0) A.fine q‖ + w 0 q.1 * ‖linearizedCurl (R 0) A'.fine q‖ := by
      rw [e, ← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hw0
    have h4 := pow_le_pow_left₀ (by positivity) h3 2
    exact h4.trans add_sq_le_two_mul
  have h3 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1),
      (w (j + 1) c.1 * ‖(chartSum A A').coarse j c.1 c.2‖) ^ 2 ≤
      2 * (∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1), (w (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2 +
        ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1), (w (j + 1) c.1 * ‖A'.coarse j c.1 c.2‖) ^ 2) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have hw0 := hw (j + 1) c.1
    have e : (chartSum A A').coarse j c.1 c.2 = A.coarse j c.1 c.2 + (1 : ℝ) • A'.coarse j c.1 c.2 := rfl
    have h3 : w (j + 1) c.1 * ‖(chartSum A A').coarse j c.1 c.2‖ ≤
        w (j + 1) c.1 * ‖A.coarse j c.1 c.2‖ + w (j + 1) c.1 * ‖A'.coarse j c.1 c.2‖ := by
      rw [e, one_smul, ← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hw0
    have h4 := pow_le_pow_left₀ (by positivity) h3 2
    exact h4.trans add_sq_le_two_mul
  have p1 : 0 ≤ ∑ q ∈ plaquettesOver S B 0, (w 0 q.1 * ‖linearizedCurl (R 0) A.fine q‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have p2 : 0 ≤ ∑ q ∈ plaquettesOver S B 0, (w 0 q.1 * ‖linearizedCurl (R 0) A'.fine q‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have p3 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1), (w (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have p4 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1), (w (j + 1) c.1 * ‖A'.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  linarith
theorem weightedNorm_chartSum_le (S : Finset F.Cell) (R : F.FieldChain) (A A' : ChainChart F) (w : F.SiteWeights)
    (hw : ∀ (j : ℕ) (x : F.Site j), 0 ≤ w j x) {a a' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') (h1 : weightedNorm S R A w ≤ a)
    (h2 : weightedNorm S R A' w ≤ a') : weightedNorm S R (chartSum A A') w ≤ 2 * (a + a') := by
  have hnn : ∀ (X : ChainChart F) (z : F.Cell), 0 ≤ localNormSq S (cellBall S z 3) R X w := by
    intro X z
    unfold localNormSq
    have q1 : 0 ≤ ∑ q ∈ plaquettesOver S (cellBall S z 3) 0, (w 0 q.1 * ‖linearizedCurl (R 0) X.fine q‖) ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    have q2 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (w (j + 1) c.1 * ‖X.coarse j c.1 c.2‖) ^ 2 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    have q3 := Real.sqrt_nonneg (∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖X.fine b.1 b.2‖) ^ 4)
    linarith
  have hsq : ∀ (X : ChainChart F) (z : F.Cell), localNorm S R X w z ^ 2 = localNormSq S (cellBall S z 3) R X w :=
    fun X z => Real.sq_sqrt (hnn X z)
  have hS : ∀ X : ChainChart F, weightedNorm S R X w ^ 2 = ∑ z ∈ S, localNormSq S (cellBall S z 3) R X w := by
    intro X
    unfold weightedNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    exact Finset.sum_congr rfl fun z _ => hsq X z
  have h3 : weightedNorm S R (chartSum A A') w ^ 2 ≤ 3 * (weightedNorm S R A w ^ 2 + weightedNorm S R A' w ^ 2) := by
    rw [hS, hS, hS, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun z _ => localNormSq_chartSum_le S _ R A A' w hw
  have b1 : 0 ≤ weightedNorm S R A w := Real.sqrt_nonneg _
  have b2 : 0 ≤ weightedNorm S R A' w := Real.sqrt_nonneg _
  have h4 := pow_le_pow_left₀ b1 h1 2
  have h5 := pow_le_pow_left₀ b2 h2 2
  have h6 : weightedNorm S R (chartSum A A') w ^ 2 ≤ (2 * (a + a')) ^ 2 := by nlinarith [mul_nonneg ha ha']
  exact le_of_not_gt fun hlt => absurd h6 (not_le.2 (pow_lt_pow_left₀ hlt (by positivity) (by norm_num)))
theorem decayWeights_nonneg (hL : 0 < F.blockSide) (del θ : ℝ) (p : F.Site 0) (y0 : F.Cell) (j : ℕ) (x : F.Site j) :
    0 ≤ decayWeights F del θ p y0 j x := by
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  have hp : (0 : ℝ) < (F.blockSide : ℝ) ^ j := by positivity
  unfold decayWeights
  refine mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (div_nonneg ?_ hN.le) _)
  unfold scaleRadius
  exact (lt_min hN (lt_of_lt_of_le hp (le_max_left _ _))).le
theorem one_le_two_mul_decayWeights (hL : 0 < F.blockSide) {θ del : ℝ} (hθ : 0 ≤ θ) (hdel : 0 ≤ del)
    (hdel8 : del ≤ 1 / 8) (p : F.Site 0) (y0 : F.Cell) {j : ℕ} (x : F.Site j)
    (hd : cellSupDist (enclosingCell x) y0 ≤ 3) :
    1 ≤ 2 * decayWeights F del θ p y0 j x := by
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  have hp : (0 : ℝ) < (F.blockSide : ℝ) ^ j := by positivity
  unfold decayWeights
  have h1 : 1 ≤ (scaleRadius F j p x / (F.blockSide : ℝ) ^ F.top) ^ (-θ) := by
    refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos (div_pos ?_ hN) ?_ (by linarith)
    · unfold scaleRadius
      exact lt_min hN (lt_of_lt_of_le hp (le_max_left _ _))
    · rw [div_le_one hN]
      exact min_le_left _ _
  have hdr : (cellSupDist (enclosingCell x) y0 : ℝ) ≤ 3 := by exact_mod_cast hd
  have h2 : 1 / 2 ≤ Real.exp (-del * cellSupDist (enclosingCell x) y0) := by
    have := Real.add_one_le_exp (-del * (cellSupDist (enclosingCell x) y0 : ℝ))
    nlinarith
  have h3 := mul_le_mul h2 h1 zero_le_one (Real.exp_pos _).le
  linarith
theorem localNorm_unit_le_two_mul (hL : 0 < F.blockSide) {θ del : ℝ} (hθ : 0 ≤ θ) (hdel : 0 ≤ del)
    (hdel8 : del ≤ 1 / 8) (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (p : F.Site 0) (z : F.Cell) :
    localNorm S R U (oneSiteWeights F) z ≤ 2 * localNorm S R U (decayWeights F del θ p z) z := by
  classical
  have hw : ∀ {j : ℕ} (x : F.Site j), enclosingCell x ∈ cellBall S z 3 → 1 ≤ 2 * decayWeights F del θ p z j x := by
    intro j x hx
    refine one_le_two_mul_decayWeights hL hθ hdel hdel8 p z x ?_
    have := (Finset.mem_filter.1 hx).2
    rwa [BlockLines.cellSupDist_comm]
  set w := decayWeights F del θ p z with hwdef
  have h1 : Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (oneSiteWeights F 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) ≤
      4 * Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) := by
    have e : (4 : ℝ) = Real.sqrt 16 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [e, ← Real.sqrt_mul (by norm_num)]
    refine Real.sqrt_le_sqrt ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    have h2 := hw b.1 (Finset.mem_filter.1 hb).2
    have h3 : oneSiteWeights F 0 b.1 * ‖U.fine b.1 b.2‖ ≤ 2 * (w 0 b.1 * ‖U.fine b.1 b.2‖) := by
      have h4 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (U.fine b.1 b.2))
      simp only [oneSiteWeights, one_mul]
      linarith
    have h5 := pow_le_pow_left₀ (by simp [oneSiteWeights]) h3 4
    refine h5.trans (le_of_eq ?_)
    ring
  have h2 : ∑ q ∈ plaquettesOver S (cellBall S z 3) 0, (oneSiteWeights F 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 ≤
      4 * ∑ q ∈ plaquettesOver S (cellBall S z 3) 0, (w 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    have h2 := hw q.1 (Finset.mem_filter.1 hq).2
    have h3 : oneSiteWeights F 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖ ≤
        2 * (w 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) := by
      have h4 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (linearizedCurl (R 0) U.fine q))
      simp only [oneSiteWeights, one_mul]
      linarith
    have h5 := pow_le_pow_left₀ (by simp [oneSiteWeights]) h3 2
    refine h5.trans (le_of_eq ?_)
    ring
  have h3 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (oneSiteWeights F (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 ≤
      4 * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have h2 := hw c.1 (Finset.mem_filter.1 hc).2
    have h3 : oneSiteWeights F (j + 1) c.1 * ‖U.coarse j c.1 c.2‖ ≤ 2 * (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) := by
      have h4 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (U.coarse j c.1 c.2))
      simp only [oneSiteWeights, one_mul]
      linarith
    have h5 := pow_le_pow_left₀ (by simp [oneSiteWeights]) h3 2
    refine h5.trans (le_of_eq ?_)
    ring
  have hmain : localNormSq S (cellBall S z 3) R U (oneSiteWeights F) ≤ 4 * localNormSq S (cellBall S z 3) R U w := by
    unfold localNormSq
    linarith
  unfold localNorm
  have e : (2 : ℝ) = Real.sqrt 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [e, ← Real.sqrt_mul (by norm_num)]
  exact Real.sqrt_le_sqrt hmain
theorem exists_blockSide_large {K A θ : ℝ} (hK : 0 < K) (hA : 0 < A) (hθ : 0 < θ) :
    ∃ L₂ : ℕ, ∀ L : ℕ, L₂ ≤ L → 1 ≤ L ∧ K / (L : ℝ) ^ 2 ≤ 1 / 32 ∧ A * (1 / (L : ℝ)) ^ θ ≤ 1 / 32 := by
  refine ⟨⌈max 1 (max (32 * K) ((32 * A) ^ (1 / θ)))⌉₊, fun L hL => ?_⟩
  have h1 : max 1 (max (32 * K) ((32 * A) ^ (1 / θ))) ≤ (L : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hL)
  have h2 : (1 : ℝ) ≤ L := (le_max_left _ _).trans h1
  have h3 : 32 * K ≤ (L : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans h1)
  have h4 : (32 * A) ^ (1 / θ) ≤ (L : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans h1)
  have hLr : (0 : ℝ) < L := by linarith
  refine ⟨by exact_mod_cast h2, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    nlinarith
  · have h5 : (32 * A) ≤ (L : ℝ) ^ θ := by
      have := Real.rpow_le_rpow (by positivity) h4 hθ.le
      rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hθ.ne', Real.rpow_one] at this
    rw [Real.div_rpow (by norm_num) hLr.le, Real.one_rpow, mul_one_div, div_le_iff₀ (by positivity)]
    linarith
theorem lt_eighth_of_le {K Ck E s L2 lam v : ℝ} (hs0 : 0 < s) (hL2 : 0 < L2)
    (h : v ≤ K * s / L2 + K * lam * (E * s) + Ck * (E * s) ^ 2)
    (g2 : K / L2 ≤ 1 / 32) (g3 : K * E * lam ≤ 1 / 32) (g4 : Ck * E ^ 2 * s ≤ 1 / 32) : v < s / 8 := by
  have e1 : K * s / L2 = (K / L2) * s := by ring
  have e2 : K * lam * (E * s) = (K * E * lam) * s := by ring
  have e3 : Ck * (E * s) ^ 2 = (Ck * E ^ 2 * s) * s := by ring
  have h1 := mul_le_mul_of_nonneg_right g2 hs0.le
  have h2 := mul_le_mul_of_nonneg_right g3 hs0.le
  have h3 := mul_le_mul_of_nonneg_right g4 hs0.le
  rw [e1, e2, e3] at h
  linarith
end SplitCriticalPointBounds
open SplitCriticalPointBounds BlockLines BlockWeights
set_option maxHeartbeats 1000000 in
theorem splitCriticalPointBounds (hLoc : smallChartLocalBoundsStatement)
    (hCold : coldFieldBelowTopStatement) (hMis : misfitDecayDownLevelsStatement)
    (hLast : topMisfitNearCellStatement) : splitCriticalPointBoundsStatement := by
  obtain ⟨Cl, hCl, Ll, hLast⟩ := hLast
  intro a θ del Ca ha hθ hθ8 hdel hdel8 hCa
  obtain ⟨Lo, hLoc⟩ := hLoc θ del hθ hθ8 hdel hdel8
  obtain ⟨K, hK, Lk, hCold⟩ := hCold θ del hθ hθ8 hdel hdel8
  obtain ⟨Lm, hMis⟩ := hMis a ha
  obtain ⟨E, hE2, hEdef⟩ : ∃ E : ℝ, 2 ≤ E ∧ E = 2 * Ca + 2 := ⟨_, by linarith, rfl⟩
  have hE0 : 0 < E := by linarith
  obtain ⟨L₂, hL₂⟩ := exists_blockSide_large (K := K) (A := K * E) hK (by positivity) hθ
  refine ⟨max (max Lo Lk) (max (max Lm Ll) L₂), fun L hL hge r C₁ hr hC₁ => ?_⟩
  have hLo : Lo ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hge)
  have hLk : Lk ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hge)
  have hLm : Lm ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hge))
  have hLl : Ll ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hge))
  have hLL : L₂ ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hge)
  obtain ⟨cl, Co, hcl, hCo, hLocL⟩ := hLoc L hL hLo
  obtain ⟨ck, Ck, hck, hCk, hColdL⟩ := hCold L hL hLk
  obtain ⟨cm, Cm, hcm, hCm, hMisL⟩ := hMis L hL hLm
  obtain ⟨c4, hc4, hLastL⟩ := hLast L hL hLl
  obtain ⟨g1, g2, g3⟩ := hL₂ L hLL
  obtain ⟨K1, hK12, hK1⟩ : ∃ K1 : ℝ, 2 ≤ K1 ∧ 3 * Cl ≤ K1 := ⟨2 + 3 * Cl, by linarith, by linarith⟩
  have hK10 : 0 < K1 := by linarith
  obtain ⟨s₂, hs20, hs21, hs22, hs23, hs24, hs25, hs26, hs27⟩ : ∃ s₂ : ℝ, 0 < s₂ ∧ s₂ ≤ 1 ∧ C₁ * s₂ ≤ 1 ∧ E * s₂ ≤ cl ∧
      E * s₂ ≤ ck ∧ K1 * E * s₂ ≤ cm ∧ 2 * E * s₂ ≤ c4 ∧ Ck * E ^ 2 * s₂ ≤ 1 / 32 := by
    have hp : ∀ x : ℝ, 0 < x → 0 < 1 / (1 + x) := fun x hx => by positivity
    have hA1 : 0 < C₁ := hC₁
    have hA2 : 0 < cl / E := by positivity
    have hA3 : 0 < ck / E := by positivity
    have hA4 : 0 < cm / (K1 * E) := by positivity
    have hA5 : 0 < c4 / (2 * E) := by positivity
    have hA6 : 0 < 1 / (32 * (Ck * E ^ 2)) := by positivity
    set y := min (min (min 1 (1 / C₁)) (min (cl / E) (ck / E)))
      (min (min (cm / (K1 * E)) (c4 / (2 * E))) (1 / (32 * (Ck * E ^ 2)))) with hy
    have hy0 : 0 < y :=
      lt_min (lt_min (lt_min one_pos (by positivity)) (lt_min hA2 hA3)) (lt_min (lt_min hA4 hA5) hA6)
    have y1 : y ≤ 1 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
    have y2 : y ≤ 1 / C₁ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    have y3 : y ≤ cl / E := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have y4 : y ≤ ck / E := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have y5 : y ≤ cm / (K1 * E) := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
    have y6 : y ≤ c4 / (2 * E) := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    have y7 : y ≤ 1 / (32 * (Ck * E ^ 2)) := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨y, hy0, y1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := (le_div_iff₀ hC₁).1 y2
      linarith
    · have := (le_div_iff₀ hE0).1 y3
      linarith
    · have := (le_div_iff₀ hE0).1 y4
      linarith
    · have := (le_div_iff₀ (by positivity : 0 < K1 * E)).1 y5
      linarith
    · have := (le_div_iff₀ (by positivity : 0 < 2 * E)).1 y6
      linarith
    · have := (le_div_iff₀ (by positivity : 0 < 32 * (Ck * E ^ 2))).1 y7
      linarith
  obtain ⟨C₂, hC₂0, hC₂1, hC₂2⟩ : ∃ C₂ : ℝ, 0 < C₂ ∧ Co * E ≤ C₂ ∧ Cm * (K1 * E) ≤ C₂ := by
    refine ⟨Co * E + Cm * (K1 * E) + 1, by positivity, ?_, ?_⟩
    · have : 0 ≤ Cm * (K1 * E) := by positivity
      linarith
    · have : 0 ≤ Co * E := by positivity
      linarith
  refine ⟨s₂, C₂, hs20, hC₂0, ?_⟩
  intro F m S hFL hamb hm hreg s V hs0 hss hcold U hU
  subst hFL
  classical
  have hodd : Odd F.blockSide := hL
  have hLpos : 0 < F.blockSide := hodd.pos
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hLpos
  have hsE : s ≤ E * s := by nlinarith
  have hEs1 : E * s ≤ cl := (mul_le_mul_of_nonneg_left hss hE0.le).trans hs23
  have hEs2 : E * s ≤ ck := (mul_le_mul_of_nonneg_left hss hE0.le).trans hs24
  have hEs3 : K1 * E * s ≤ cm := (mul_le_mul_of_nonneg_left hss (by positivity)).trans hs25
  have hEs4 : 2 * E * s ≤ c4 := (mul_le_mul_of_nonneg_left hss (by positivity)).trans hs26
  have hEs5 : Ck * E ^ 2 * s ≤ 1 / 32 := (mul_le_mul_of_nonneg_left hss (by positivity)).trans hs27
  have hCs : C₁ * s ≤ 1 := (mul_le_mul_of_nonneg_left hss hC₁.le).trans hs22
  obtain ⟨Ulin, Urest, hsame, hsz⟩ := hU.split
  have hN : ∀ (p : F.Site 0) (y0 : F.Cell),
      weightedNorm S (referenceFieldChain S V) U (decayWeights F del θ p y0) ≤ E * s := by
    intro p y0
    rw [weightedNorm_congr hsame]
    obtain ⟨a1, a2⟩ := hsz p y0 θ (Or.inl rfl)
    have h1 := weightedNorm_chartSum_le S (referenceFieldChain S V) Ulin Urest (decayWeights F del θ p y0)
      (fun j x => decayWeights_nonneg hLpos del θ p y0 j x) (by positivity) (by positivity) a1 a2
    refine h1.trans ?_
    rw [hEdef]
    have h2 : C₁ * s ^ 2 ≤ s := by nlinarith
    linarith
  have hN0 : ∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤ 2 * (E * s) := by
    intro z hz
    have p0 : F.Site 0 := cellCentre 0 z
    have h1 := localNorm_unit_le_two_mul hLpos hθ.le hdel.le hdel8 S (referenceFieldChain S V) U p0 z
    have h2 := (localNorm_le_weightedNorm S (referenceFieldChain S V) U _ hz).trans (hN p0 z)
    linarith
  have hTop : ∀ b ∈ innerBonds S F.top,
      normSubOne (chartBondMisfit (referenceFieldChain S V) U V F.depth b) ≤ K1 * E * s := by
    intro b hb
    have hz : enclosingCell b.1 ∈ S := enclosingCell_mem hodd (ChartCoordinates.innerBonds_ends hb).1
    have h1 := hLastL F m S rfl hamb hm hreg s V hs0 (by nlinarith) hcold U (enclosingCell b.1) (2 * (E * s)) hz
      (by positivity) (by linarith) (hN0 _ hz) b (Finset.mem_filter.2 ⟨hb, by simp⟩)
    refine h1.trans ?_
    have h2 : Cl * (s + 2 * (E * s)) ≤ Cl * (3 * (E * s)) := mul_le_mul_of_nonneg_left (by linarith) hCl.le
    have h3 : (3 * Cl) * (E * s) ≤ K1 * (E * s) := mul_le_mul_of_nonneg_right hK1 (by positivity)
    nlinarith
  have hLocAll := hLocL F m S rfl hamb hm hreg s V hs0 (hsE.trans hEs1) hcold U (E * s) hsE hEs1 hN
  have hpow : Co * (E * s) ≤ C₂ * s := by
    have := mul_le_mul_of_nonneg_right hC₂1 hs0.le
    linarith
  have hpow0 : 0 ≤ Co * (E * s) := by positivity
  refine ⟨fun q hq => ?_, fun j p r' hj h1 h2 => ?_, fun p r' h1 h2 => ⟨?_, ?_⟩, fun j z hj => ?_⟩
  · have h1 := hColdL F m S rfl hamb hm hreg s V hs0 (hsE.trans hEs2) hcold U (E * s) hsE hEs2 hN q hq
    exact lt_eighth_of_le hs0 (by positivity) h1 g2 g3 hEs5
  · refine (hLocAll.1 j p r' hj h1 h2).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hpow0 hpow 4) (Real.rpow_nonneg (by positivity) _)
  · refine (hLocAll.2 p r' h1 h2).1.trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hpow0 hpow 2) (Real.rpow_nonneg (by positivity) _)
  · refine (hLocAll.2 p r' h1 h2).2.trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hpow0 hpow 2) (Real.rpow_nonneg (by positivity) _)
  · have hb : K1 * E * s = K1 * (E * s) := by ring
    have hN1 : ∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤ K1 * E * s := by
      intro z hz
      refine (hN0 z hz).trans ?_
      rw [hb]
      exact mul_le_mul_of_nonneg_right hK12 (by positivity)
    have hsK : s ≤ K1 * E * s := by
      rw [hb]
      nlinarith
    obtain ⟨m1, m2⟩ := hMisL F m S rfl hamb hm hreg s V V hs0 (hsK.trans hEs3) hcold U (K1 * E * s) hsK hEs3 hN1 hTop
      hU.critical j z hj
    have hcm1 : Cm * (K1 * E * s) ≤ C₂ * s := by
      have := mul_le_mul_of_nonneg_right hC₂2 hs0.le
      rw [hb]
      nlinarith
    have hcm0 : 0 ≤ Cm * (K1 * E * s) := by positivity
    refine ⟨m1.trans (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hcm1 (by positivity)) 4),
      m2.trans (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hcm1 (by positivity)) 2)⟩
end YangMills.Construction.BlockAverages
end
