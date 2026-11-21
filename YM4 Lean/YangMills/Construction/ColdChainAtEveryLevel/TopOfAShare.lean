import YangMills.Construction.ColdChainAtEveryLevel.ChartOnComplexLines
import YangMills.Construction.ColdChainAtEveryLevel.TermsNearACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
open Metric
namespace YangMills.Construction.ComplexTopFit
open BlockAverages ComplexLineChart ComplexifiedQuaternions ComplexLevels ComplexChainStep ComplexContours
  ComplexRemainders ComplexBondTerms ComplexAnalyticity ComplexDifferences ComplexCells NearbyCellTerms Analytic
variable {F : BlockFrame} {ι : Type} [Fintype ι]
def rotatedTopLine (V : F.GaugeField F.top) (b : F.Site (F.depth + 1) × Fin 4) (ε : ι → imaginaryQuaternions)
    (w : ι → ℝ) (ζ : ι → ℂ) : ComplexQuat :=
  unitExp (complexLine 0 ε w ζ) * ofUnit (V b.1 b.2)
def complexTopFit (R : F.FieldChain) (V : F.GaugeField F.top) (b : F.Site (F.depth + 1) × Fin 4) (U : ChainChart F)
    (A : ι → ChainChart F) (w : ι → ℝ) (ε : ι → imaginaryQuaternions) (ζ : ι → ℂ) : ℂ :=
  complexBlockFit (complexGaugedContourAverage (complexChartField R (complexLineChart U A w ζ) F.depth)
    (complexBalancingGauge (complexChartField R (complexLineChart U A w ζ) F.depth) (R F.depth)) b)
    (rotatedTopLine V b ε w ζ)
theorem norm_topBlockFit_zero_le {j : ℕ} (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {R : F.GaugeField j}
    {c : F.Site (j + 1) × Fin 4} {σ : ℝ} (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy R (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage R c))⁻¹) - 1‖ ≤ σ)
    (hm : ‖contourAverage R c‖ ≤ 1) {X : ComplexQuat} (hX : ‖X‖ ≤ 2) :
    ‖topBlockFit R c X 0‖ ≤ 3 := by
  have hN : bondHullNorm c (0 : F.Site j → Fin 4 → ComplexQuat) = 0 := by
    have := bondHullNorm_smul c (0 : ℂ) (0 : F.Site j → Fin 4 → ComplexQuat)
    simpa using this
  have e := topBlockFit_eq hodd hj hσ href (y := 0) (by rw [hN]; norm_num) X
  obtain ⟨u1, r1⟩ := linearizedUnit_zero hodd hj hσ href
  rw [e, u1, r1, add_zero, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have h1 : ‖(1 : ℂ) - (ofUnit (polarUnit (contourAverage R c)) * Matrix.adjugate X).trace / 2‖ ≤ 3 := by
    refine (norm_sub_le _ _).trans ?_
    have h2 := norm_trace_le (ofUnit (polarUnit (contourAverage R c)) * Matrix.adjugate X)
    rw [norm_ofUnit_mul, norm_adjugate] at h2
    rw [norm_div, norm_one]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
    linarith
  calc _ ≤ 1 * 3 := mul_le_mul hm h1 (norm_nonneg _) (by norm_num)
    _ = 3 := by norm_num
def complexTopFitBound (ε₀ : ℝ) : ℝ := 3 + 480 / ε₀ * (ε₀ ^ 2 + ε₀ / 48 * ε₀)
set_option maxHeartbeats 2000000 in
theorem isBoundedHolomorphicExtension_gaugedBlockFit (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {R : F.FieldChain} {V : F.GaugeField F.top} {D : Finset F.Cell}
    {b : F.Site (F.depth + 1) × Fin 4} (hb : b ∈ innerBonds D (F.depth + 1)) {c σ ε₀ : ℝ}
    (hc0 : 0 < c) (hc1 : 2 * c ≤ 1 / 4000) (hc2 : 4 * (F.blockSide : ℝ) * (16 * c) ≤ 1 / 1024) (hc3 : 16 * c < 1)
    (hσ : σ ≤ 1 / 64) (hε0 : 0 < ε₀) (hεr : 3 * (ε₀ + σ) < hullBallRadius F.blockSide)
    (hεK : 200000 * (F.blockSide : ℝ) ^ 2 * (ε₀ + σ) ≤ 1) (hN : hullBondCount F.blockSide * (16 * c) < ε₀)
    (hmean : ‖contourAverage (R F.depth) b‖ ≤ 1)
    (href : ∀ j, j + 1 ≤ F.top → ∀ c ∈ innerBonds D (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy (R j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤ σ)
    (hlev : ∀ W : ComplexChainChart F,
      Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D 0, ‖levelDeviation R W 0 b.1 b.2‖ ^ 4)) ≤ 4 * c →
      (∀ j, j + 1 < F.top → Real.sqrt (∑ c ∈ innerBonds D (j + 1), ‖levelSource W j c.1 c.2 - 1‖ ^ 2) ≤ 4 * c) →
      ∀ j, j < F.top → Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D j, ‖levelDeviation R W j b.1 b.2‖ ^ 4)) ≤ 16 * c)
    (U : ChainChart F) (A : ι → ChainChart F) (e : ι → F.Site F.top → Fin 4 → imaginaryQuaternions)
    (ε : ι → imaginaryQuaternions)
    (hε : ∀ l, ε l = e l b.1 b.2) (w q : ι → ℝ) (hw : ∀ l, 0 ≤ w l) {ρ : ℝ} (hρ : 0 < ρ)
    (hbud : ρ * ∑ l, w l * q l ≤ c)
    (hU4 : finsetLpNorm 4 (innerBonds D 0) (fun b => ‖U.fine b.1 b.2‖) ≤ c)
    (hUm : ∀ j, j + 1 < F.top → finsetLpNorm 2 (innerBonds D (j + 1)) (fun b => ‖U.coarse j b.1 b.2‖) ≤ c)
    (hA4 : ∀ l, finsetLpNorm 4 (innerBonds D 0) (fun b => ‖(A l).fine b.1 b.2‖) ≤ q l)
    (hAm : ∀ l j, j + 1 < F.top → finsetLpNorm 2 (innerBonds D (j + 1)) (fun b => ‖(A l).coarse j b.1 b.2‖) ≤ q l)
    (hεq : ∀ l, ‖ε l‖ ≤ q l) :
    IsBoundedHolomorphicExtension Complex.ofRealCLM (fun t : ι → ℝ =>
      gaugedBlockFit (chartField R (chartShiftAlong U A (fun l => w l * t l)) F.depth)
        (chartGauge R (chartShiftAlong U A (fun l => w l * t l)) (F.depth + 1))
        (rotatedField (topVariationAlong e (fun l => w l * t l)) V) b)
      (complexTopFit R V b U A w ε) ρ (complexTopFitBound ε₀) := by
  classical
  set tt : ℝ := 16 * c with htt
  have ht0 : 0 ≤ tt := by positivity
  have hτ8 : 4 * (F.blockSide : ℝ) * tt ≤ 1 / 1024 := hc2
  have hbudget : ∀ ζ ∈ ball (0 : ι → ℂ) ρ, ∀ x : ι → ℝ, (∀ l, x l ≤ q l) → (∀ l, 0 ≤ x l) →
      ∑ l, ‖ζ l‖ * (w l * x l) ≤ c := by
    intro ζ hζ x hx hx0
    have hz : ‖ζ‖ < ρ := by simpa using hζ
    refine le_trans (Finset.sum_le_sum fun l _ => ?_) ((Finset.mul_sum _ _ _).symm.le.trans hbud)
    have h1 : ‖ζ l‖ ≤ ρ := (norm_le_pi_norm ζ l).trans hz.le
    exact mul_le_mul h1 (mul_le_mul_of_nonneg_left (hx l) (hw l)) (mul_nonneg (hw l) (hx0 l)) hρ.le
  have hpt : ∀ ζ ∈ ball (0 : ι → ℂ) ρ,
      (∀ b' ∈ innerBonds D 0, ‖complexifiedImaginary ((complexLineChart U A w ζ).re.fine b'.1 b'.2)
        ((complexLineChart U A w ζ).im.fine b'.1 b'.2)‖ ≤ 2 * c) ∧
      (∀ j, j + 1 < F.top → ∀ b' ∈ innerBonds D (j + 1), ‖complexifiedImaginary
        ((complexLineChart U A w ζ).re.coarse j b'.1 b'.2)
        ((complexLineChart U A w ζ).im.coarse j b'.1 b'.2)‖ ≤ 2 * c) ∧
      ∀ j, j < F.top → ∀ b' ∈ innerBonds D j, ‖levelDeviation R (complexLineChart U A w ζ) j b'.1 b'.2‖ ≤ tt := by
    intro ζ hζ
    obtain ⟨u1, u2⟩ := complexLine_bounds (innerBonds D 0) (p := 4) (by norm_num) (fun b => U.fine b.1 b.2)
      (fun l b => (A l).fine b.1 b.2) ζ hw hc1 hU4
      (hbudget ζ hζ _ hA4 fun _ => finsetLpNorm_nonneg _ _ _)
    have hm := fun j (hj : j + 1 < F.top) => complexLine_bounds (innerBonds D (j + 1)) (p := 2) (by norm_num)
      (fun b => U.coarse j b.1 b.2) (fun l b => (A l).coarse j b.1 b.2) ζ hw hc1 (hUm j hj)
      (hbudget ζ hζ _ (fun l => hAm l j hj) fun _ => finsetLpNorm_nonneg _ _ _)
    refine ⟨fun b' hb' => ?_, fun j hj b' hb' => ?_, ?_⟩
    · rw [complexifiedImaginary_complexLineChart_fine]
      exact u1 b' hb'
    · rw [complexifiedImaginary_complexLineChart_coarse]
      exact (hm j hj).1 b' hb'
    · have hl := hlev (complexLineChart U A w ζ) (by
        rw [← finsetLpNorm_four]
        simp only [ComplexLineChart.levelDeviation_zero, complexifiedImaginary_complexLineChart_fine]
        exact u2) (fun j hj => by
        rw [← finsetLpNorm_two]
        simp only [levelSource, complexifiedImaginary_complexLineChart_coarse]
        exact (hm j hj).2)
      intro j hj b' hb'
      have h1 := hl j hj
      rw [← finsetLpNorm_four] at h1
      have h2 := abs_le_finsetLpNorm (p := 4) (by norm_num) hb'
        (fun b : F.Site j × Fin 4 => ‖levelDeviation R (complexLineChart U A w ζ) j b.1 b.2‖)
      rw [abs_of_nonneg (norm_nonneg _)] at h2
      exact h2.trans h1
  have hgood : ∀ ζ ∈ ball (0 : ι → ℂ) ρ, ∀ b' ∈ innerBonds D F.depth,
      BondNearReal (complexChartField R (complexLineChart U A w ζ) F.depth) (R F.depth) tt b'.1 b'.2 :=
    fun ζ hζ b' hb' => by
    have h := (hpt ζ hζ).2.2 F.depth (by simp [BlockFrame.top]) b' hb'
    exact ⟨h, det_complexChartField_of_norm_lt_one R _ F.depth _ _ (lt_of_le_of_lt h hc3)⟩
  have hfield : ∀ ζ ∈ ball (0 : ι → ℂ) ρ, ∀ b' ∈ innerBonds D F.depth,
      AnalyticAt ℂ (fun ζ' => complexChartField R (complexLineChart U A w ζ') F.depth b'.1 b'.2) ζ :=
    fun ζ hζ b' hb' =>
    analyticAt_complexChartField hodd R (W := complexLineChart U A w) (z := ζ) ht0 hc3 hσ hc2
      (fun b'' _ => by
        simp only [complexifiedImaginary_complexLineChart_fine]
        exact analyticAt_complexLine _ _ _ _)
      (fun b'' hb'' => ((hpt ζ hζ).1 b'' hb'').trans (by linarith))
      (fun j _ b'' _ => by
        simp only [complexifiedImaginary_complexLineChart_coarse]
        exact analyticAt_complexLine _ _ _ _)
      (fun j hj b'' hb'' => ((hpt ζ hζ).2.1 j hj b'' hb'').trans (by linarith))
      (hpt ζ hζ).2.2 href F.depth (by simp [BlockFrame.top]) b' hb'
  have hline : ∀ ζ ∈ ball (0 : ι → ℂ) ρ, ‖complexLine 0 ε w ζ‖ ≤ c := fun ζ hζ => by
    have h1 := norm_complexLine_le 0 ε hw ζ
    have h2 := hbudget ζ hζ (fun l => ‖ε l‖) hεq fun _ => norm_nonneg _
    simp only [norm_zero, zero_add] at h1
    exact h1.trans h2
  have hjt : F.depth < F.top := by simp [BlockFrame.top]
  have hcg : ∀ ζ ∈ ball (0 : ι → ℂ) ρ,
      ContoursNearReal (complexChartField R (complexLineChart U A w ζ) F.depth) (R F.depth) tt σ b := by
    intro ζ hζ
    have hhull : HoldsOnHull b (fun b' i =>
        BondNearReal (complexChartField R (complexLineChart U A w ζ) F.depth) (R F.depth) tt b' i) :=
      holdsOnHull_of_innerBonds hjt hodd hb (hgood ζ hζ)
    exact ⟨fun h hh π => pathNearReal_axisPath _ hodd.pos (fun v hv k hk => (hhull.1 v hv k hk).1) hh π,
      fun h hh => pathNearReal_replicate _ _ _ fun r hr => hhull.2 h hh r hr,
      fun h hh π => pathNearReal_axisPath _ hodd.pos (fun v hv k hk => (hhull.1 v hv k hk).2) hh π,
      fun h hh π => href F.depth le_rfl b hb h hh π⟩
  have hX2 : ∀ ζ ∈ ball (0 : ι → ℂ) ρ, ‖rotatedTopLine V b ε w ζ‖ ≤ 2 := by
    intro ζ hζ
    unfold rotatedTopLine
    have h1 := norm_unitExp_sub_one_le ((hline ζ hζ).trans (by linarith))
    have h2 := hline ζ hζ
    have h3 : ‖unitExp (complexLine 0 ε w ζ) * ofUnit (V b.1 b.2)‖ = ‖unitExp (complexLine 0 ε w ζ)‖ :=
      norm_mul_ofUnit _ _
    rw [h3]
    have h4 : ‖unitExp (complexLine 0 ε w ζ)‖ ≤ ‖unitExp (complexLine 0 ε w ζ) - 1‖ + ‖(1 : ComplexQuat)‖ := by
      have := norm_add_le (unitExp (complexLine 0 ε w ζ) - 1) 1
      simpa using this
    have h5 : ‖(1 : ComplexQuat)‖ ≤ 1 := by
      have := norm_ofUnit (1 : UnitQuaternion)
      rw [ofUnit_one] at this
      exact this.le
    linarith
  refine ⟨hρ, fun ζ hζ => ?_, fun ζ hζ => ?_, fun t ht => ?_⟩
  · have hX : HoldsOnHull b (fun b' i =>
        AnalyticAt ℂ (fun ζ' => complexChartField R (complexLineChart U A w ζ') F.depth b' i) ζ) :=
      holdsOnHull_of_innerBonds hjt hodd hb (hfield ζ hζ)
    have hM := analyticAt_complexGaugedContourAverage
      (X := fun ζ' => complexChartField R (complexLineChart U A w ζ') F.depth) hodd (R F.depth)
      (by simp [BlockFrame.top]) ht0 hτ8 (hcg ζ hζ) hX
    have hre := (unitPart_and_sqrt_near hodd (by simp [BlockFrame.top]) ht0 hσ hτ8 (hcg ζ hζ)).1
    have hT : AnalyticAt ℂ (fun ζ' => rotatedTopLine V b ε w ζ') ζ :=
      (analyticAt_unitExp (analyticAt_complexLine 0 ε w ζ) ((hline ζ hζ).trans (by linarith))).mul
        analyticAt_const
    exact analyticAt_complexBlockFit hM (Or.inl hre) hT
  · have hhd : HoldsOnHull b (fun b' i => (complexChartField R (complexLineChart U A w ζ) F.depth b' i).det = 1) :=
      holdsOnHull_of_innerBonds hjt hodd hb fun b' hb' => (hgood ζ hζ b' hb').2
    have hmo := complexGaugedContourAverage_eq_liftedBondMean hodd
      (by simp [BlockFrame.top] : F.depth + 1 ≤ F.top) (R := R F.depth) hhd
    have hNy : bondHullNorm b (levelDeviation R (complexLineChart U A w ζ) F.depth) < ε₀ := by
      have hgap : HoldsOnHull b (fun x i => ‖levelDeviation R (complexLineChart U A w ζ) F.depth x i‖ ≤ tt) :=
        holdsOnHull_of_innerBonds hjt hodd hb fun b' hb' => (hpt ζ hζ).2.2 F.depth hjt b' hb'
      exact lt_of_le_of_lt (bondHullSum_le hodd ht0 hgap) hN
    have hq := topBlockFitRemainder_quadraticBound hodd (by simp [BlockFrame.top] : F.depth + 1 ≤ F.top) hσ hε0
      (href F.depth le_rfl b hb) hεr hεK (hX2 ζ hζ)
    have hbd := hq.bound _ hNy
    have hz := norm_topBlockFit_zero_le hodd (by simp [BlockFrame.top] : F.depth + 1 ≤ F.top) hσ
      (href F.depth le_rfl b hb) hmean (hX2 ζ hζ)
    have e : complexTopFit R V b U A w ε ζ =
        topBlockFitRemainder (R F.depth) b (rotatedTopLine V b ε w ζ)
          (levelDeviation R (complexLineChart U A w ζ) F.depth) +
        topBlockFit (R F.depth) b (rotatedTopLine V b ε w ζ) 0 := by
      unfold complexTopFit
      rw [hmo]
      simp only [topBlockFitRemainder]
      show topBlockFit (R F.depth) b (rotatedTopLine V b ε w ζ)
        (levelDeviation R (complexLineChart U A w ζ) F.depth) = _
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have hN0 : 0 ≤ bondHullNorm b (levelDeviation R (complexLineChart U A w ζ) F.depth) :=
      bondHullSum_nonneg b fun _ _ => norm_nonneg _
    have hK0 : 0 ≤ 480 / ε₀ := by positivity
    have h5 : bondHullNorm b (levelDeviation R (complexLineChart U A w ζ) F.depth) ^ 2 ≤ ε₀ ^ 2 :=
      pow_le_pow_left₀ hN0 hNy.le 2
    have h6 : ε₀ / 48 * bondHullNorm b (levelDeviation R (complexLineChart U A w ζ) F.depth) ≤ ε₀ / 48 * ε₀ :=
      mul_le_mul_of_nonneg_left hNy.le (by positivity)
    have h7 := mul_le_mul_of_nonneg_left (add_le_add h5 h6) hK0
    unfold complexTopFitBound
    linarith
  · set ζ : ι → ℂ := complexifyCLM t with hζd
    have hζ : ζ ∈ ball (0 : ι → ℂ) ρ := by
      rw [mem_ball_zero_iff, hζd, norm_complexifyCLM]
      exact ht
    set U' := chartShiftAlong U A (fun l => w l * t l) with hU'
    set v := topVariationAlong e (fun l => w l * t l) with hv
    have hW : complexLineChart U A w ζ = realChart U' := complexLineChart_complexify U A w t
    have hre := (unitPart_and_sqrt_near hodd (by simp [BlockFrame.top]) ht0 hσ hτ8 (hcg ζ hζ)).1
    rw [hW] at hre
    have hT : rotatedTopLine V b ε w ζ = ofUnit (rotatedField v V b.1 b.2) := by
      unfold rotatedTopLine
      have hl : complexLine 0 ε w ζ = complexifiedImaginary (v b.1 b.2) 0 := by
        rw [complexifiedImaginary_zero]
        show _ = imagToComplex _
        simp only [complexLine, imagToComplex_zero, zero_add, hv, topVariationAlong, imagToComplex_sum,
          imagToComplex_smul, hε]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [smul_smul, hζd, complexifyCLM_apply]
        push_cast
        ring_nf
      show _ = ofUnit (expUnit (v b.1 b.2) * V b.1 b.2)
      rw [hl, unitExp_complexifiedImaginary_zero, ofUnit_mul]
    have hm : complexGaugedContourAverage (complexChartField R (realChart U') F.depth)
        (complexBalancingGauge (complexChartField R (realChart U') F.depth) (R F.depth)) b =
        ofQuat (gaugedContourAverage (chartField R U' F.depth) (chartGauge R U' (F.depth + 1)) b) := by
      have : complexBalancingGauge (complexChartField R (realChart U') F.depth) (R F.depth) =
          complexBalancingGauges R (realChart U') (F.depth + 1) := by
        simp only [complexBalancingGauges]
      rw [this, complexChartField_realChart, ComplexChartCoordinates.complexBalancingGauges_realChart,
        complexGaugedContourAverage_complexify]
    have hne : gaugedContourAverage (chartField R U' F.depth) (chartGauge R U' (F.depth + 1)) b ≠ 0 := by
      intro h0
      rw [hm, h0, ofQuat_zero] at hre
      simp at hre
    unfold complexTopFit
    rw [hW, hm, hT, ComplexChartCoordinates.complexBlockFit_ofQuat_ofUnit hne]
    rfl
end YangMills.Construction.ComplexTopFit
end
