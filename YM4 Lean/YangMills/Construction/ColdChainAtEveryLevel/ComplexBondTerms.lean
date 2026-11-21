import YangMills.Construction.ColdChainAtEveryLevel.ComplexPlaquettes
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction
open BlockAverages ComplexifiedQuaternions ComplexRemainders ComplexLevels ComplexDifferences ComplexChainStep
  ComplexContours ComplexPlaquettes LatticePaths LatticeFractionalIntegration FiniteDifferences
namespace ComplexBondTerms
variable {F : BlockFrame} {j : ℕ}
theorem trace_adjugate_eq_trace (a : ComplexQuat) : (Matrix.adjugate a).trace = a.trace := by
  simp [Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  ring
theorem complexBlockFit_mul_unitPart {M E : ComplexQuat} {g : UnitQuaternion} (hM : M.det ≠ 0) (hE : E.det = 1) :
    complexBlockFit M (E * ofUnit g * unitPart M) = principalSqrt M.det * ((E * ofUnit g - 1).det / 2) := by
  have hM0 : M ≠ 0 := by
    intro h0
    rw [h0] at hM
    simp at hM
  have hU : (unitPart M).det = 1 := det_unitPart hM
  have hG : (E * ofUnit g).det = 1 := by
    rw [Matrix.det_mul, hE, det_ofUnit, one_mul]
  have e1 : M * Matrix.adjugate (E * ofUnit g * unitPart M) =
      principalSqrt M.det • Matrix.adjugate (E * ofUnit g) := by
    rw [Matrix.adjugate_mul_distrib, ← mul_assoc]
    nth_rewrite 1 [← principalSqrt_det_smul_unitPart hM0]
    rw [smul_mul_assoc, Matrix.mul_adjugate, hU, one_smul, smul_mul_assoc, one_mul]
  rw [complexBlockFit, e1, Matrix.trace_smul, trace_adjugate_eq_trace, ← one_sub_half_trace_eq_half_det hG,
    smul_eq_mul]
  ring
theorem complexFieldChain_of_ne (R : F.FieldChain) (W : ComplexChainChart F) (V : F.GaugeField F.top) {k : ℕ}
    (h : k ≠ F.top) : complexFieldChain R W V k = complexChartField R W k := by
  unfold complexFieldChain
  exact Function.update_of_ne h _ _
theorem complexBondTerm_of_lt_top (R : F.FieldChain) (W : ComplexChainChart F) (V : F.GaugeField F.top) {m : ℕ}
    (hm : m + 1 < F.top) (c : F.Site (m + 1) × Fin 4)
    (hM : (complexGaugedContourAverage (complexChartField R W m)
      (complexBalancingGauge (complexChartField R W m) (R m)) c).det ≠ 0) :
    complexBondTerm R W V m c = principalSqrt (complexGaugedContourAverage (complexChartField R W m)
        (complexBalancingGauge (complexChartField R W m) (R m)) c).det *
      ((levelSource W m c.1 c.2 * ofUnit (referenceDefect R m c) - 1).det / 2) := by
  have h1 := complexFieldChain_of_ne R W V (k := m) (by omega)
  have h2 := complexFieldChain_of_ne R W V (k := m + 1) (by omega)
  simp only [complexBondTerm, h1, h2, complexBalancingGauges]
  exact complexBlockFit_mul_unitPart hM (det_unitExp _)
section BelowTop
theorem norm_bond_expansion_le {r₀ a b d G g₀ p q : ℂ} {Gb dr n₁ n₂ ε₁ ε₂ y : ℝ} (hr : ‖r₀‖ ≤ 2)
    (ha : ‖a‖ ≤ n₁) (hb : ‖b‖ ≤ n₂)
    (hd : ‖d‖ ≤ dr) (hG : ‖G‖ ≤ Gb) (hg : ‖g₀‖ ≤ y ^ 2 / 2) (hp : ‖p‖ ≤ ε₁ * y) (hq : ‖q‖ ≤ ε₂ * y)
    (hn₁ : n₁ ≤ 1) (hn₂ : n₂ ≤ 1) (hdr : dr ≤ 1) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (hy : ε₁ + ε₂ ≤ y) :
    ‖r₀ * G + d * g₀ + a * q + b * p + (a + b + d) * G + d * (p + q)‖ ≤
      5 * Gb + 2 * dr * y ^ 2 + (n₁ * ε₂ + n₂ * ε₁) * y := by
  have hdr0 : 0 ≤ dr := (norm_nonneg _).trans hd
  have hn₁0 : 0 ≤ n₁ := (norm_nonneg _).trans ha
  have hn₂0 : 0 ≤ n₂ := (norm_nonneg _).trans hb
  have t1 : ‖r₀ * G‖ ≤ 2 * Gb := by
    rw [norm_mul]
    exact mul_le_mul hr hG (norm_nonneg _) (by norm_num)
  have t2 : ‖d * g₀‖ ≤ dr * (y ^ 2 / 2) := by
    rw [norm_mul]
    exact mul_le_mul hd hg (norm_nonneg _) hdr0
  have t3 : ‖a * q‖ ≤ n₁ * (ε₂ * y) := by
    rw [norm_mul]
    exact mul_le_mul ha hq (norm_nonneg _) hn₁0
  have t4 : ‖b * p‖ ≤ n₂ * (ε₁ * y) := by
    rw [norm_mul]
    exact mul_le_mul hb hp (norm_nonneg _) hn₂0
  have t5 : ‖(a + b + d) * G‖ ≤ 3 * Gb := by
    rw [norm_mul]
    have u1 := norm_add_le (a + b) d
    have u2 := norm_add_le a b
    exact mul_le_mul (by linarith) hG (norm_nonneg _) (by norm_num)
  have t6 : ‖d * (p + q)‖ ≤ dr * ((ε₁ + ε₂) * y) := by
    rw [norm_mul]
    have u1 := norm_add_le p q
    exact mul_le_mul hd (by nlinarith) (norm_nonneg _) hdr0
  have h7 : dr * ((ε₁ + ε₂) * y) ≤ dr * y ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ hdr0
    nlinarith
  have s1 := norm_add_le (r₀ * G + d * g₀ + a * q + b * p + (a + b + d) * G) (d * (p + q))
  have s2 := norm_add_le (r₀ * G + d * g₀ + a * q + b * p) ((a + b + d) * G)
  have s3 := norm_add_le (r₀ * G + d * g₀ + a * q) (b * p)
  have s4 := norm_add_le (r₀ * G + d * g₀) (a * q)
  have s5 := norm_add_le (r₀ * G) (d * g₀)
  nlinarith
theorem hullBallRadius_le_one (hodd : Odd F.blockSide) : hullBallRadius F.blockSide ≤ 1 := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  unfold hullBallRadius
  rw [div_le_one (by positivity)]
  linarith
theorem quadratic_small_of_lipschitz {K t σ N : ℝ} (hK : 0 ≤ K) (hN0 : 0 ≤ N) (hN1 : N ≤ 1) (hNt : N ≤ 3 * t)
    (hLip : 12 * K * (3 * t + σ) ≤ 1) (hσ : 0 ≤ σ) : K * (N ^ 2 + σ * N) ≤ 1 / 12 := by
  have u1 : N ^ 2 + σ * N ≤ (3 * t + σ) * N := by nlinarith
  have u3 : 12 * K * (3 * t + σ) * N ≤ 1 * 1 := mul_le_mul hLip hN1 hN0 (by norm_num)
  have u4 := mul_le_mul_of_nonneg_left u1 hK
  linarith
set_option maxHeartbeats 1000000 in
theorem norm_complexBondTerm_second_diff_le (hodd : Odd F.blockSide) {m : ℕ} (hm : m + 1 < F.top)
    (R : F.FieldChain) (W₀ W₁ W₂ W₃ : ComplexChainChart F)
    (V : F.GaugeField F.top) {c : F.Site (m + 1) × Fin 4} {σ t : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy (R m) (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage (R m) c))⁻¹) - 1‖ ≤ σ) (ht : 0 ≤ t)
    (hsm : 24 * (3 * t + σ) < hullBallRadius F.blockSide)
    (hLip : 12 * (200000 * (F.blockSide : ℝ) ^ 2) * (3 * t + σ) ≤ 1)
    (h0 : bondHullNorm c (levelDeviation R W₀ m) ≤ t) (h1 : bondHullNorm c (levelDeviation R W₁ m) ≤ t)
    (h2 : bondHullNorm c (levelDeviation R W₂ m) ≤ t) (h3 : bondHullNorm c (levelDeviation R W₃ m) ≤ t)
    (hn1 : bondHullNorm c (levelDeviation R W₁ m - levelDeviation R W₀ m) ≤ t)
    (hn2 : bondHullNorm c (levelDeviation R W₂ m - levelDeviation R W₀ m) ≤ t)
    (hd0 : HoldsOnHull c (fun b i => (complexChartField R W₀ m b i).det = 1))
    (hd1 : HoldsOnHull c (fun b i => (complexChartField R W₁ m b i).det = 1))
    (hd2 : HoldsOnHull c (fun b i => (complexChartField R W₂ m b i).det = 1))
    (hd3 : HoldsOnHull c (fun b i => (complexChartField R W₃ m b i).det = 1))
    (hdr : 12 * (200000 * (F.blockSide : ℝ) ^ 2) * (3 * t + σ) *
        bondHullNorm c (levelDeviation R W₃ m - levelDeviation R W₁ m - levelDeviation R W₂ m +
          levelDeviation R W₀ m) +
      64 * (200000 * (F.blockSide : ℝ) ^ 2) * bondHullNorm c (levelDeviation R W₁ m - levelDeviation R W₀ m) *
        bondHullNorm c (levelDeviation R W₂ m - levelDeviation R W₀ m) ≤ 1) :
    ‖complexBondTerm R W₃ V m c - complexBondTerm R W₁ V m c - complexBondTerm R W₂ V m c +
        complexBondTerm R W₀ V m c‖ ≤
      5 * (‖levelSource W₁ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ *
            ‖levelSource W₂ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ +
          ‖levelSource W₃ m c.1 c.2 - levelSource W₁ m c.1 c.2 - levelSource W₂ m c.1 c.2 +
              levelSource W₀ m c.1 c.2‖ *
            (‖levelSource W₀ m c.1 c.2 * ofUnit (referenceDefect R m c) - 1‖ +
              ‖levelSource W₁ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ +
              ‖levelSource W₂ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ +
              ‖levelSource W₃ m c.1 c.2 - levelSource W₁ m c.1 c.2 - levelSource W₂ m c.1 c.2 +
                levelSource W₀ m c.1 c.2‖)) +
        2 * (12 * (200000 * (F.blockSide : ℝ) ^ 2) * (3 * t + σ) *
            bondHullNorm c (levelDeviation R W₃ m - levelDeviation R W₁ m - levelDeviation R W₂ m +
              levelDeviation R W₀ m) +
          64 * (200000 * (F.blockSide : ℝ) ^ 2) * bondHullNorm c (levelDeviation R W₁ m - levelDeviation R W₀ m) *
            bondHullNorm c (levelDeviation R W₂ m - levelDeviation R W₀ m)) *
          (‖levelSource W₀ m c.1 c.2 * ofUnit (referenceDefect R m c) - 1‖ +
            ‖levelSource W₁ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ +
            ‖levelSource W₂ m c.1 c.2 - levelSource W₀ m c.1 c.2‖) ^ 2 +
        (bondHullNorm c (levelDeviation R W₁ m - levelDeviation R W₀ m) *
            ‖levelSource W₂ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ +
          bondHullNorm c (levelDeviation R W₂ m - levelDeviation R W₀ m) *
            ‖levelSource W₁ m c.1 c.2 - levelSource W₀ m c.1 c.2‖) *
          (‖levelSource W₀ m c.1 c.2 * ofUnit (referenceDefect R m c) - 1‖ +
            ‖levelSource W₁ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ +
            ‖levelSource W₂ m c.1 c.2 - levelSource W₀ m c.1 c.2‖) := by
  have hj : m + 1 ≤ F.top := by omega
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  set K := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set x₀ := levelDeviation R W₀ m with hx₀
  set x₁ := levelDeviation R W₁ m with hx₁
  set x₂ := levelDeviation R W₂ m with hx₂
  set x₃ := levelDeviation R W₃ m with hx₃
  set E₀ := levelSource W₀ m c.1 c.2 with hE₀
  set E₁ := levelSource W₁ m c.1 c.2 with hE₁
  set E₂ := levelSource W₂ m c.1 c.2 with hE₂
  set E₃ := levelSource W₃ m c.1 c.2 with hE₃
  set μ := referenceDefect R m c with hμ
  set δ₁ := x₁ - x₀ with hδ₁
  set δ₂ := x₂ - x₀ with hδ₂
  set Δ := x₃ - x₁ - x₂ + x₀ with hΔ
  set Lip := 12 * K * (3 * t + σ) with hLipd
  set n₁ := bondHullNorm c δ₁ with hn₁d
  set n₂ := bondHullNorm c δ₂ with hn₂d
  set h := bondHullNorm c Δ with hhd
  have hn₁0 : 0 ≤ n₁ := bondHullSum_nonneg c fun _ _ => norm_nonneg _
  have hn₂0 : 0 ≤ n₂ := bondHullSum_nonneg c fun _ _ => norm_nonneg _
  have hsmN : ∀ {y : F.Site m → Fin 4 → ComplexQuat}, bondHullNorm c y ≤ t →
      8 * (F.blockSide : ℝ) * bondHullNorm c y ≤ 1 / 1024 := by
    intro y hy
    refine eight_mul_le_of_lt_hullBallRadius hodd ?_
    linarith
  have hmean : ∀ {W : ComplexChainChart F}, HoldsOnHull c (fun b i => (complexChartField R W m b i).det = 1) →
      bondHullNorm c (levelDeviation R W m) ≤ t → complexBondTerm R W V m c =
        (((‖contourAverage (R m) c‖ : ℝ) : ℂ) + sqrtRemainder (R m) c (levelDeviation R W m)) *
          ((levelSource W m c.1 c.2 * ofUnit μ - 1).det / 2) := by
    intro W hd hN
    have e1 := complexGaugedContourAverage_eq_liftedBondMean hodd hj (X := complexChartField R W m) (R := R m) hd
    obtain ⟨hre, -, -⟩ := remainder_bounds hodd hj hσ (hsmN hN) href
    have e1' : complexGaugedContourAverage (complexChartField R W m)
        (complexBalancingGauge (complexChartField R W m) (R m)) c =
        liftedBondMean (R m) c (levelDeviation R W m) := e1
    have e2 : (complexGaugedContourAverage (complexChartField R W m)
        (complexBalancingGauge (complexChartField R W m) (R m)) c).det ≠ 0 := by
      intro h0
      rw [e1'] at h0
      rw [h0] at hre
      simp at hre
    rw [complexBondTerm_of_lt_top R W V hm c e2, e1']
    congr 1
    simp only [sqrtRemainder]
    ring
  rw [hmean hd0 h0, hmean hd1 h1, hmean hd2 h2, hmean hd3 h3, ← hx₀, ← hx₁, ← hx₂, ← hx₃, ← hE₀, ← hE₁, ← hE₂,
    ← hE₃]
  set rb : ℂ := ((‖contourAverage (R m) c‖ : ℝ) : ℂ) with hrb
  set ρ₀ := sqrtRemainder (R m) c x₀ with hρ₀
  set ρ₁ := sqrtRemainder (R m) c x₁ with hρ₁
  set ρ₂ := sqrtRemainder (R m) c x₂ with hρ₂
  set ρ₃ := sqrtRemainder (R m) c x₃ with hρ₃
  set Y₀ := E₀ * ofUnit μ - 1 with hY₀
  set A := (E₁ - E₀) * ofUnit μ with hA
  set B := (E₂ - E₀) * ofUnit μ with hB
  set D := (E₃ - E₁ - E₂ + E₀) * ofUnit μ with hD
  have eY₁ : E₁ * ofUnit μ - 1 = Y₀ + A := by rw [hY₀, hA]; noncomm_ring
  have eY₂ : E₂ * ofUnit μ - 1 = Y₀ + B := by rw [hY₀, hB]; noncomm_ring
  have eY₃ : E₃ * ofUnit μ - 1 = Y₀ + A + B + D := by rw [hY₀, hA, hB, hD]; noncomm_ring
  rw [eY₁, eY₂, eY₃]
  set g₀ := Y₀.det / 2 with hg₀
  set g₁ := (Y₀ + A).det / 2 with hg₁
  set g₂ := (Y₀ + B).det / 2 with hg₂
  set g₃ := (Y₀ + A + B + D).det / 2 with hg₃
  set ε₁ := ‖E₁ - E₀‖ with hε₁
  set ε₂ := ‖E₂ - E₀‖ with hε₂
  set Dd := ‖E₃ - E₁ - E₂ + E₀‖ with hDd
  have nA : ‖A‖ = ε₁ := norm_mul_ofUnit _ _
  have nB : ‖B‖ = ε₂ := norm_mul_ofUnit _ _
  have nD : ‖D‖ = Dd := norm_mul_ofUnit _ _
  set y := ‖Y₀‖ + ε₁ + ε₂ with hy
  have hε₁0 : 0 ≤ ε₁ := norm_nonneg _
  have hε₂0 : 0 ≤ ε₂ := norm_nonneg _
  have hY0 : 0 ≤ ‖Y₀‖ := norm_nonneg _
  have hG : ‖g₃ - g₁ - g₂ + g₀‖ ≤ ε₁ * ε₂ + Dd * (y + Dd) := by
    have := norm_half_det_second_diff_le Y₀ A B D
    rw [nA, nB, nD] at this
    exact this
  have hp : ‖g₁ - g₀‖ ≤ ε₁ * y := by
    have := norm_half_det_add_sub_le Y₀ A
    rw [nA] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hε₁0)
    linarith
  have hq : ‖g₂ - g₀‖ ≤ ε₂ * y := by
    have := norm_half_det_add_sub_le Y₀ B
    rw [nB] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hε₂0)
    linarith
  have hg : ‖g₀‖ ≤ y ^ 2 / 2 := by
    rw [hg₀, norm_div, Complex.norm_ofNat]
    have u1 := norm_det_le Y₀
    have u2 : ‖Y₀‖ ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hY0 (by linarith) 2
    linarith
  have hq0 := sqrtRemainder_quadraticBound hodd hj hσ href
  rw [← hK] at hq0
  have hsm3 : 3 * (3 * t + σ) < hullBallRadius F.blockSide := by linarith
  have a1 := hq0.norm_sub_le hK0 hσ0 (t := 3 * t) (by linarith) hsm3 (y := x₀) (y' := x₁) (by linarith)
    (by linarith)
  have a2 := hq0.norm_sub_le hK0 hσ0 (t := 3 * t) (by linarith) hsm3 (y := x₀) (y' := x₂) (by linarith)
    (by linarith)
  set yt := x₀ + δ₁ + δ₂ with hyt
  have hNyt : bondHullNorm c yt ≤ 3 * t := by
    have u1 := bondHullNorm_add_le c (x₀ + δ₁) δ₂
    have u2 := bondHullNorm_add_le c x₀ δ₁
    linarith
  have a3 := hq0.norm_sub_le hK0 hσ0 (t := 3 * t) (by linarith) hsm3 hNyt (y' := x₃) (by linarith)
  have e1 : x₃ - yt = Δ := by
    rw [hyt, hδ₁, hδ₂, hΔ]
    abel
  rw [e1] at a3
  have a4 := hq0.norm_second_diff_le hK0 hσ0 (by linarith) (y := x₀) (e₁ := δ₁) (e₂ := δ₂) ht (by linarith) h0
    hn1 hn2
  have e2 : x₀ + δ₁ = x₁ := by rw [hδ₁]; abel
  have e3 : x₀ + δ₂ = x₂ := by rw [hδ₂]; abel
  have e6 : x₁ + δ₂ = yt := by rw [← e2]
  rw [e2, e3, e6] at a4
  have hdn : ‖ρ₃ - ρ₁ - ρ₂ + ρ₀‖ ≤ Lip * h + 64 * K * n₁ * n₂ := by
    have e4 : ρ₃ - ρ₁ - ρ₂ + ρ₀ = (ρ₃ - sqrtRemainder (R m) c yt) +
        (sqrtRemainder (R m) c yt - ρ₁ - ρ₂ + ρ₀) := by abel
    rw [e4]
    exact (norm_add_le _ _).trans (add_le_add a3 a4)
  have han : ‖ρ₁ - ρ₀‖ ≤ n₁ := a1.trans (by
    have := mul_le_mul_of_nonneg_right hLip hn₁0
    linarith)
  have hbn : ‖ρ₂ - ρ₀‖ ≤ n₂ := a2.trans (by
    have := mul_le_mul_of_nonneg_right hLip hn₂0
    linarith)
  have hr₀ : ‖rb + ρ₀‖ ≤ 2 := by
    have hb1 := abs_norm_contourAverage_sub_one_le hodd href
    have hb2 : ‖rb‖ ≤ 5 / 4 := by
      rw [hrb, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      have := (abs_le.1 hb1).2
      linarith
    obtain ⟨-, -, hρb⟩ := remainder_bounds hodd hj hσ (hsmN h0) href
    rw [← hρ₀, ← hK] at hρb
    set N := bondHullNorm c x₀ with hN
    have hN0 : 0 ≤ N := bondHullSum_nonneg c fun _ _ => norm_nonneg _
    have h9 := hullBallRadius_le_one (F := F) hodd
    have hN1 : N ≤ 1 := by linarith
    have hb3 : K * (N ^ 2 + σ * N) ≤ 1 / 12 :=
      quadratic_small_of_lipschitz hK0 hN0 hN1 (by linarith) hLip hσ0.le
    have := norm_add_le rb ρ₀
    linarith
  have hdr' : Lip * h + 64 * K * n₁ * n₂ ≤ 1 := hdr
  have h9 := hullBallRadius_le_one (F := F) hodd
  have hn₁1 : n₁ ≤ 1 := by linarith
  have hn₂1 : n₂ ≤ 1 := by linarith
  have hmain := norm_bond_expansion_le (r₀ := rb + ρ₀) (a := ρ₁ - ρ₀) (b := ρ₂ - ρ₀) (d := ρ₃ - ρ₁ - ρ₂ + ρ₀)
    (G := g₃ - g₁ - g₂ + g₀) (g₀ := g₀) (p := g₁ - g₀) (q := g₂ - g₀) hr₀ han hbn hdn hG hg hp hq hn₁1 hn₂1 hdr'
    hε₁0 hε₂0 (by linarith)
  have eT : (rb + ρ₃) * g₃ - (rb + ρ₁) * g₁ - (rb + ρ₂) * g₂ + (rb + ρ₀) * g₀ =
      (rb + ρ₀) * (g₃ - g₁ - g₂ + g₀) + (ρ₃ - ρ₁ - ρ₂ + ρ₀) * g₀ + (ρ₁ - ρ₀) * (g₂ - g₀) +
        (ρ₂ - ρ₀) * (g₁ - g₀) +
        ((ρ₁ - ρ₀) + (ρ₂ - ρ₀) + (ρ₃ - ρ₁ - ρ₂ + ρ₀)) * (g₃ - g₁ - g₂ + g₀) +
        (ρ₃ - ρ₁ - ρ₂ + ρ₀) * ((g₁ - g₀) + (g₂ - g₀)) := by ring
  rw [eT]
  refine hmain.trans (le_of_eq ?_)
  rw [hy]
end BelowTop
section TopLevel
def topBlockFit (R : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) (X' : ComplexQuat)
    (y : F.Site j → Fin 4 → ComplexQuat) : ℂ :=
  complexBlockFit (liftedBondMean R c y) X'
def topBlockFitRemainder (R : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) (X' : ComplexQuat)
    (y : F.Site j → Fin 4 → ComplexQuat) : ℂ :=
  topBlockFit R c X' y - topBlockFit R c X' 0
theorem linearizedUnit_zero (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {R : F.GaugeField j}
    {c : F.Site (j + 1) × Fin 4} {σ : ℝ} (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy R (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage R c))⁻¹) - 1‖ ≤ σ) :
    linearizedUnit R c 0 = 1 ∧ sqrtRemainder R c 0 = 0 := by
  have hN : bondHullNorm c (0 : F.Site j → Fin 4 → ComplexQuat) = 0 := by
    have := bondHullNorm_smul c (0 : ℂ) (0 : F.Site j → Fin 4 → ComplexQuat)
    simpa using this
  obtain ⟨-, h1, h2⟩ := remainder_bounds hodd hj hσ (y := 0) (by rw [hN]; norm_num) href
  rw [hN] at h1 h2
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at h1 h2
  have e1 : unitRemainder R c 0 = 0 := norm_le_zero_iff.1 h1
  have e2 : sqrtRemainder R c 0 = 0 := norm_le_zero_iff.1 h2
  refine ⟨?_, e2⟩
  have e3 : transportedAverage R (0 : F.Site j → Fin 4 → ComplexQuat) c = 0 := by
    have := transportedAverage_sub R (0 : F.Site j → Fin 4 → ComplexQuat) 0 c
    have h0 : (0 : F.Site j → Fin 4 → ComplexQuat) = fun _ _ => 0 := rfl
    rw [h0]
    simpa using this
  simp only [linearizedUnit, e1, e3]
  simp [purePart]
theorem topBlockFit_eq (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {R : F.GaugeField j}
    {c : F.Site (j + 1) × Fin 4} {σ : ℝ} (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy R (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage R c))⁻¹) - 1‖ ≤ σ)
    {y : F.Site j → Fin 4 → ComplexQuat}
    (hy : 8 * (F.blockSide : ℝ) * bondHullNorm c y ≤ 1 / 1024) (X' : ComplexQuat) :
    topBlockFit R c X' y = (((‖contourAverage R c‖ : ℝ) : ℂ) + sqrtRemainder R c y) *
      (1 - (linearizedUnit R c y * (ofUnit (polarUnit (contourAverage R c)) * Matrix.adjugate X')).trace / 2) := by
  obtain ⟨hre, -, -⟩ := remainder_bounds hodd hj hσ hy href
  set M := liftedBondMean R c y with hM
  have hne : M.det ≠ 0 := by
    intro h0
    rw [h0] at hre
    simp at hre
  have hM0 : M ≠ 0 := by
    intro h0
    rw [h0] at hne
    simp at hne
  set w := polarUnit (contourAverage R c) with hw
  have e1 : linearizedUnit R c y = unitPart M * ofUnit w⁻¹ := by
    simp only [linearizedUnit, unitRemainder, ← hM, ← hw]
    abel
  have e2 : ((‖contourAverage R c‖ : ℝ) : ℂ) + sqrtRemainder R c y = principalSqrt M.det := by
    simp only [sqrtRemainder, ← hM]
    ring
  rw [e1, e2, topBlockFit, complexBlockFit, ← hM]
  have e3 : M * Matrix.adjugate X' =
      principalSqrt M.det • (unitPart M * ofUnit w⁻¹ * (ofUnit w * Matrix.adjugate X')) := by
    rw [mul_assoc, ofUnit_inv_mul_cancel_left, ← smul_mul_assoc, principalSqrt_det_smul_unitPart hM0]
  rw [e3, Matrix.trace_smul, smul_eq_mul]
  ring
theorem norm_topBlockFitRemainder_le (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {R : F.GaugeField j}
    {c : F.Site (j + 1) × Fin 4} {σ : ℝ} (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy R (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage R c))⁻¹) - 1‖ ≤ σ)
    {y : F.Site j → Fin 4 → ComplexQuat}
    (hy : 3 * (bondHullNorm c y + σ) < hullBallRadius F.blockSide)
    (hK : 200000 * (F.blockSide : ℝ) ^ 2 * (bondHullNorm c y + σ) ≤ 1) {X' : ComplexQuat} (hX : ‖X'‖ ≤ 2) :
    ‖topBlockFitRemainder R c X' y‖ ≤ 10 * bondHullNorm c y := by
  set N := bondHullNorm c y with hN
  have hN0 : 0 ≤ N := bondHullSum_nonneg c fun _ _ => norm_nonneg _
  have hσ0 : 0 ≤ σ := by
    have h0 : (0 : Lattice4) ∈ centredCube F.blockSide := by
      rw [mem_centredCube_iff]
      intro i
      have := hodd.pos
      simp only [Pi.zero_apply]
      omega
    exact (norm_nonneg _).trans (href 0 h0 1)
  have hsm : 8 * (F.blockSide : ℝ) * N ≤ 1 / 1024 := eight_mul_le_of_lt_hullBallRadius hodd (by linarith)
  obtain ⟨-, hq, hρ⟩ := remainder_bounds hodd hj hσ hsm href
  rw [← hN] at hq hρ
  obtain ⟨hU0, hρ0⟩ := linearizedUnit_zero hodd hj hσ href
  have hN0' : bondHullNorm c (0 : F.Site j → Fin 4 → ComplexQuat) = 0 := by
    have := bondHullNorm_smul c (0 : ℂ) (0 : F.Site j → Fin 4 → ComplexQuat)
    simpa using this
  have hf := topBlockFit_eq hodd hj hσ href hsm X'
  have hf0 := topBlockFit_eq hodd hj hσ href (y := 0) (by rw [hN0']; norm_num) X'
  rw [hU0, hρ0, add_zero, one_mul] at hf0
  set K := 200000 * (F.blockSide : ℝ) ^ 2 with hKd
  have hKN : K * (N ^ 2 + σ * N) ≤ N := by
    have e : K * (N ^ 2 + σ * N) = K * (N + σ) * N := by ring
    rw [e]
    exact mul_le_of_le_one_left hN0 hK
  set w := polarUnit (contourAverage R c) with hw
  set Z := ofUnit w * Matrix.adjugate X' with hZ
  have hZn : ‖Z‖ ≤ 2 := by
    rw [hZ, norm_ofUnit_mul, norm_adjugate]
    exact hX
  set U := linearizedUnit R c y with hU
  set ρ := sqrtRemainder R c y with hρd
  set rb : ℂ := ((‖contourAverage R c‖ : ℝ) : ℂ) with hrb
  have hU1 : ‖U - 1‖ ≤ 2 * N := by
    have e : U - 1 = purePart (transportedAverage R y c) + unitRemainder R c y := by
      rw [hU, linearizedUnit]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have a1 : ‖purePart (transportedAverage R y c)‖ ≤ N :=
      (norm_purePart_le _).trans ((norm_transportedAverage_le hodd R _ c).trans
        (lineBlockAverage_le_bondHullSum hodd (fun _ _ => norm_nonneg _) c))
    linarith
  have hρN : ‖ρ‖ ≤ N := hρ.trans hKN
  have hN1 : N ≤ 1 / 2 := by
    have h9 := hullBallRadius_le_one (F := F) hodd
    linarith
  have hUn : ‖U‖ ≤ 2 := by
    have e := norm_add_le (1 : ComplexQuat) (U - 1)
    rw [add_sub_cancel, CStarRing.norm_one] at e
    linarith
  have hb1 := abs_norm_contourAverage_sub_one_le hodd href
  have hrbn : ‖rb‖ ≤ 5 / 4 := by
    rw [hrb, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have := (abs_le.1 hb1).2
    linarith
  have e4 : topBlockFitRemainder R c X' y = ρ * (1 - (U * Z).trace / 2) - rb * (((U - 1) * Z).trace / 2) := by
    rw [topBlockFitRemainder, hf, hf0]
    have e5 : ((U - 1) * Z).trace = (U * Z).trace - Z.trace := by
      rw [sub_mul, one_mul, Matrix.trace_sub]
    rw [e5]
    ring
  rw [e4]
  have t1 : ‖(U * Z).trace / 2‖ ≤ 4 := by
    rw [norm_div, Complex.norm_ofNat]
    have u1 := norm_trace_le (U * Z)
    have u2 := norm_mul_le U Z
    have u3 : ‖U‖ * ‖Z‖ ≤ 2 * 2 := mul_le_mul hUn hZn (norm_nonneg _) (by norm_num)
    linarith
  have t2 : ‖((U - 1) * Z).trace / 2‖ ≤ 4 * N := by
    rw [norm_div, Complex.norm_ofNat]
    have u1 := norm_trace_le ((U - 1) * Z)
    have u2 := norm_mul_le (U - 1) Z
    have u3 : ‖U - 1‖ * ‖Z‖ ≤ 2 * N * 2 := mul_le_mul hU1 hZn (norm_nonneg _) (mul_nonneg (by norm_num) hN0)
    linarith
  have t3 : ‖1 - (U * Z).trace / 2‖ ≤ 5 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one]
    linarith
  have t4 : ‖ρ * (1 - (U * Z).trace / 2)‖ ≤ N * 5 := by
    rw [norm_mul]
    exact mul_le_mul hρN t3 (norm_nonneg _) hN0
  have t5 : ‖rb * (((U - 1) * Z).trace / 2)‖ ≤ 5 / 4 * (4 * N) := by
    rw [norm_mul]
    exact mul_le_mul hrbn t2 (norm_nonneg _) (by norm_num)
  have := norm_sub_le (ρ * (1 - (U * Z).trace / 2)) (rb * (((U - 1) * Z).trace / 2))
  linarith
theorem topBlockFitRemainder_quadraticBound (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {R : F.GaugeField j}
    {c : F.Site (j + 1) × Fin 4} {σ ε : ℝ} (hσ : σ ≤ 1 / 64) (hε0 : 0 < ε)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy R (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage R c))⁻¹) - 1‖ ≤ σ)
    (hε : 3 * (ε + σ) < hullBallRadius F.blockSide) (hK : 200000 * (F.blockSide : ℝ) ^ 2 * (ε + σ) ≤ 1)
    {X' : ComplexQuat} (hX : ‖X'‖ ≤ 2) :
    QuadraticBoundOnBall (bondHullNorm c) (topBlockFitRemainder R c X') (480 / ε) (ε / 48) ε where
  triangle := bondHullNorm_add_le c
  homogeneous := bondHullNorm_smul c
  holomorphic := by
    intro y e z hz
    have hN0 : 0 ≤ bondHullNorm c (y + z • e) := bondHullSum_nonneg c fun _ _ => norm_nonneg _
    have hσ0 : 0 ≤ σ := by
      have h0 : (0 : Lattice4) ∈ centredCube F.blockSide := by
        rw [mem_centredCube_iff]
        intro i
        have := hodd.pos
        simp only [Pi.zero_apply]
        omega
      exact (norm_nonneg _).trans (href 0 h0 1)
    have hsm := eight_mul_le_of_lt_hullBallRadius hodd (N := bondHullNorm c (y + z • e)) (by linarith)
    obtain ⟨hre, -, -⟩ := remainder_bounds hodd hj hσ hsm href
    have hd := differentiableAt_liftedBondMean (z := 0) hodd hj y e hsm href
    simp only [topBlockFitRemainder, topBlockFit, complexBlockFit]
    refine DifferentiableAt.fun_sub ?_ (differentiableAt_const _)
    exact (differentiableAt_principalSqrt_comp (differentiableAt_det_comp hd) (Or.inl hre)).fun_sub
      ((differentiableAt_trace_comp (hd.fun_mul (differentiableAt_const _))).div_const _)
  bound := by
    intro y hy
    have hN0 : 0 ≤ bondHullNorm c y := bondHullSum_nonneg c fun _ _ => norm_nonneg _
    have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
    have hb := norm_topBlockFitRemainder_le hodd hj hσ href (y := y) (by linarith) (by
      have : 200000 * (F.blockSide : ℝ) ^ 2 * (bondHullNorm c y + σ) ≤
          200000 * (F.blockSide : ℝ) ^ 2 * (ε + σ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith) hX
    refine hb.trans ?_
    have e : 480 / ε * (bondHullNorm c y ^ 2 + ε / 48 * bondHullNorm c y) =
        480 / ε * bondHullNorm c y ^ 2 + 10 * bondHullNorm c y := by
      field_simp
      ring
    rw [e]
    have : 0 ≤ 480 / ε * bondHullNorm c y ^ 2 := by positivity
    linarith
end TopLevel
end ComplexBondTerms
end YangMills.Construction
end
