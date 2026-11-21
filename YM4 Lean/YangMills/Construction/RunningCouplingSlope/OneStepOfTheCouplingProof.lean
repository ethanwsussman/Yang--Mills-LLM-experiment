import YangMills.Construction.RunningCouplingSlope.CouplingMovesByTheMoment
import YangMills.Construction.RunningCouplingSlope.KernelOfTheLaplaceTotal
import YangMills.Construction.RunningCouplingSlope.MomentOfTheExpansionAtTheLeastField
import YangMills.Construction.RunningCouplingSlope.MomentOfTheTotalOfAStep
import YangMills.Construction.RunningCouplingSlope.OneStepOfTheCoupling
import YangMills.Construction.RunningCouplingSlope.TheStepsHaveTheSlope
import YangMills.Construction.SummableBoundsOfTheFlow.OneNumberOfOneTotalProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open Filter
namespace YangMills.Construction
open TorusFields TorusLumps StepSettings RenormalizationStepParameters SlopeCoefficient
namespace RunningCouplingSlope.CouplingStep
private theorem norm_quaternionI : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
private theorem clusterRange_le_succ {B x x' : ℝ} (hB : 1 ≤ B) (hx0 : 0 ≤ x) (hx' : (2 * B) ^ 2 ≤ x') (h : x ≤ x' + 2 * B) :
    clusterRange x ≤ clusterRange x' + 1 := by
  have hx'1 : 1 ≤ x' := by nlinarith
  have hx'0 : 0 < x' := by linarith
  set u := x' ^ ((1 : ℝ) / 100) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hx'0 _
  have hu100 : u ^ (100 : ℕ) = x' := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hx'0.le]
    norm_num
  have hu1 : 1 ≤ u := Real.one_le_rpow hx'1 (by norm_num)
  have h50 : 2 * B ≤ u ^ 50 := by
    have h2 : (2 * B) ^ 2 ≤ (u ^ 50) ^ 2 := by
      rw [← pow_mul]
      norm_num only
      rw [hu100]
      exact hx'
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h2
  have h99 : u ^ 50 ≤ u ^ 99 := pow_le_pow_right₀ hu1 (by norm_num)
  have hbern : u ^ 100 + 100 * u ^ 99 ≤ (u + 1) ^ 100 := by
    have hb := one_add_mul_le_pow (a := 1 / u) (by have : 0 < 1 / u := by positivity
                                                   linarith) 100
    have hf : (u + 1) ^ 100 = u ^ 100 * (1 + 1 / u) ^ 100 := by
      rw [← mul_pow]
      congr 1
      field_simp
    have hm := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ u ^ 100)
    have hl : u ^ 100 * (1 + ((100 : ℕ) : ℝ) * (1 / u)) = u ^ 100 + 100 * u ^ 99 := by
      have : u ^ 100 = u ^ 99 * u := by ring
      rw [this]
      field_simp
      push_cast
      ring
    rw [hf, ← hl]
    exact hm
  have hxle : x ≤ (u + 1) ^ (100 : ℕ) := by
    have : x ≤ u ^ 100 + 100 * u ^ 99 := by
      rw [hu100]
      nlinarith
    exact this.trans hbern
  have hr : x ^ ((1 : ℝ) / 100) ≤ u + 1 := by
    have h3 := Real.rpow_le_rpow hx0 hxle (by norm_num : (0 : ℝ) ≤ 1 / 100)
    have h4 : ((u + 1) ^ (100 : ℕ)) ^ ((1 : ℝ) / 100) = u + 1 := by
      have := Real.pow_rpow_inv_natCast (x := u + 1) (n := 100) (by positivity) (by norm_num)
      norm_num at this ⊢
      exact this
    rwa [h4] at h3
  unfold clusterRange
  calc ⌈x ^ ((1 : ℝ) / 100)⌉₊ ≤ ⌈u + 1⌉₊ := Nat.ceil_mono hr
    _ = ⌈u⌉₊ + 1 := Nat.ceil_add_one hu0.le
private theorem eventually_mul_rpow_log_le_rpow {a c A q r : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hr : 0 < r) : ∀ᶠ x : ℝ in atTop, A * (a + c * Real.log x) ^ q ≤ x ^ r := by
  have hK : 0 < a + c + 1 := by linarith
  have hKq : 0 ≤ (a + c + 1) ^ q := Real.rpow_nonneg hK.le q
  set D := A * (a + c + 1) ^ q with hD
  have hD0 : 0 ≤ D := mul_nonneg hA hKq
  have hε : 0 < 1 / (D + 1) := one_div_pos.mpr (by linarith)
  have hlo := (isLittleO_log_rpow_rpow_atTop q hr).def hε
  filter_upwards [hlo, Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_gt_atTop 0]
    with x h hl hx
  have hl0 : 0 ≤ Real.log x := by linarith
  have hxr : 0 ≤ x ^ r := (Real.rpow_pos_of_pos hx r).le
  have hlq : 0 ≤ Real.log x ^ q := Real.rpow_nonneg hl0 q
  rw [Real.norm_of_nonneg hlq, Real.norm_of_nonneg hxr] at h
  have h1 : a + c * Real.log x ≤ (a + c + 1) * Real.log x := by nlinarith
  have h2 : (a + c * Real.log x) ^ q ≤ (a + c + 1) ^ q * Real.log x ^ q := by
    rw [← Real.mul_rpow hK.le hl0]
    exact Real.rpow_le_rpow (add_nonneg ha (mul_nonneg hc hl0)) h1 hq
  have h3 : D * (1 / (D + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by linarith)]
    linarith
  calc A * (a + c * Real.log x) ^ q ≤ A * ((a + c + 1) ^ q * Real.log x ^ q) :=
        mul_le_mul_of_nonneg_left h2 hA
    _ = D * Real.log x ^ q := by rw [hD]; ring
    _ ≤ D * (1 / (D + 1) * x ^ r) := mul_le_mul_of_nonneg_left h hD0
    _ = D * (1 / (D + 1)) * x ^ r := by ring
    _ ≤ 1 * x ^ r := mul_le_mul_of_nonneg_right h3 hxr
    _ = x ^ r := one_mul _
private theorem stepTorusSide_le {n₀ : ℕ} {C₁ x : ℝ} (hC : 0 ≤ C₁) (hx : 1 ≤ x) :
    (stepTorusSide n₀ C₁ x : ℝ) ≤ n₀ + C₁ * Real.log x := by
  have h0 : 0 ≤ C₁ * Real.log x := mul_nonneg hC (Real.log_nonneg hx)
  have h1 := Nat.floor_le h0
  unfold stepTorusSide
  push_cast
  linarith
private theorem exp_neg_mul_stepTorusSide_le {n₀ : ℕ} {c C₁ x : ℝ} (hc : 0 < c) (hcC : 1 / 4 ≤ c * C₁) (hx : 1 ≤ x) :
    Real.exp (-(c * (stepTorusSide n₀ C₁ x : ℝ))) ≤ Real.exp c * x ^ (-(1 / 4) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : C₁ * Real.log x - 1 ≤ (stepTorusSide n₀ C₁ x : ℝ) := by
    have := Nat.lt_floor_add_one (C₁ * Real.log x)
    unfold stepTorusSide
    push_cast
    have hn : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
    linarith
  rw [Real.rpow_def_of_pos hx0, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h2 := mul_le_mul_of_nonneg_left h1 hc.le
  have h3 := mul_le_mul_of_nonneg_right hcC hl
  nlinarith
private theorem eventually_stepTorusSide_bounds {n₀ : ℕ} (hn₀ : 1 ≤ n₀) {C₁ C₂ p lam : ℝ} (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hp : 0 ≤ p) (hlam : 0 < lam) :
    ∀ᶠ x : ℝ in atTop, stepTorusSide n₀ C₁ x ≤ clusterRange x / 2 ^ 11 ∧
      C₂ * (stepTorusSide n₀ C₁ x : ℝ) ^ p * x ^ (-(1 / 2) : ℝ) ≤ min lam 1 ∧
      (stepTorusSide n₀ C₁ x : ℝ) ^ 6 * (C₂ * (stepTorusSide n₀ C₁ x : ℝ) ^ p * x ^ (-(1 / 2) : ℝ)) ≤
        x ^ (-(1 / 4) : ℝ) := by
  have hn₀' : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  have e1 := eventually_mul_rpow_log_le_rpow (a := n₀) (c := C₁) (A := 2 ^ 11) (q := 1) (r := (1 : ℝ) / 100) hn₀' hC₁
    (by norm_num) zero_le_one (by norm_num)
  have e2 := eventually_mul_rpow_log_le_rpow (a := n₀) (c := C₁) (A := C₂) (q := p + 6) (r := (1 : ℝ) / 4) hn₀' hC₁ hC₂
    (by linarith) (by norm_num)
  have e3 : ∀ᶠ x : ℝ in atTop, x ^ (-(1 / 4) : ℝ) ≤ min lam 1 :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_le_const
      (lt_min hlam one_pos)
  filter_upwards [e1, e2, e3, eventually_ge_atTop 1] with x h1 h2 h3 hx
  obtain ⟨n, hn⟩ : ∃ n, n = stepTorusSide n₀ C₁ x := ⟨_, rfl⟩
  rw [← hn]
  have hx0 : 0 < x := by linarith
  have hN : (n : ℝ) ≤ n₀ + C₁ * Real.log x := by rw [hn]; exact stepTorusSide_le hC₁ hx
  have hn1 : 1 ≤ n := by
    rw [hn]
    unfold stepTorusSide
    omega
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < n := by linarith
  have hNp : 0 ≤ (n : ℝ) ^ p := Real.rpow_nonneg hN0.le p
  have hxh : 0 ≤ x ^ (-(1 / 2) : ℝ) := (Real.rpow_pos_of_pos hx0 _).le
  have hthird : (n : ℝ) ^ 6 * (C₂ * (n : ℝ) ^ p * x ^ (-(1 / 2) : ℝ)) ≤ x ^ (-(1 / 4) : ℝ) := by
    have h6 : (n : ℝ) ^ (p + 6) = (n : ℝ) ^ p * (n : ℝ) ^ 6 := by
      rw [Real.rpow_add hN0, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h7 : (n : ℝ) ^ (p + 6) ≤ ((n₀ : ℝ) + C₁ * Real.log x) ^ (p + 6) :=
      Real.rpow_le_rpow hN0.le hN (by linarith)
    have h8 : C₂ * (n : ℝ) ^ (p + 6) ≤ x ^ ((1 : ℝ) / 4) :=
      (mul_le_mul_of_nonneg_left h7 hC₂).trans h2
    have h9 : x ^ ((1 : ℝ) / 4) * x ^ (-(1 / 2) : ℝ) = x ^ (-(1 / 4) : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
    calc (n : ℝ) ^ 6 * (C₂ * (n : ℝ) ^ p * x ^ (-(1 / 2) : ℝ))
        = C₂ * (n : ℝ) ^ (p + 6) * x ^ (-(1 / 2) : ℝ) := by rw [h6]; ring
      _ ≤ x ^ ((1 : ℝ) / 4) * x ^ (-(1 / 2) : ℝ) := mul_le_mul_of_nonneg_right h8 hxh
      _ = x ^ (-(1 / 4) : ℝ) := h9
  refine ⟨?_, ?_, hthird⟩
  · rw [Nat.le_div_iff_mul_le (by positivity)]
    rw [Real.rpow_one] at h1
    have h5 : (n : ℝ) * 2 ^ 11 ≤ (clusterRange x : ℝ) := by
      have h6 : x ^ ((1 : ℝ) / 100) ≤ (clusterRange x : ℝ) := Nat.le_ceil _
      nlinarith
    exact_mod_cast h5
  · have hq : 0 ≤ C₂ * (n : ℝ) ^ p * x ^ (-(1 / 2) : ℝ) :=
      mul_nonneg (mul_nonneg hC₂ hNp) hxh
    have h6 : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ hN1
    have h7 : C₂ * (n : ℝ) ^ p * x ^ (-(1 / 2) : ℝ) ≤
        (n : ℝ) ^ 6 * (C₂ * (n : ℝ) ^ p * x ^ (-(1 / 2) : ℝ)) := le_mul_of_one_le_left hq h6
    exact (h7.trans hthird).trans h3
private theorem kernelSecondMoment_sub {n : ℕ} [NeZero n] (K K₁ K₂ : TorusBond n → TorusBond n → ℝ) :
    kernelSecondMoment K - kernelSecondMoment K₁ - kernelSecondMoment K₂ =
      kernelSecondMoment fun c c' => K c c' - K₁ c c' - K₂ c c' := by
  unfold kernelSecondMoment
  rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · ring
  · ring
private theorem firstCoordDiff_sq_le {n : ℕ} [NeZero n] (y : TorusSite n) :
    ((firstCoordDiff 0 y : ℤ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
  have h1 : (firstCoordDiff 0 y).natAbs ≤ n := by
    unfold firstCoordDiff
    exact (ZMod.natAbs_valMinAbs_le _).trans (Nat.div_le_self _ _)
  have h2 : ((firstCoordDiff 0 y).natAbs : ℝ) ≤ n := by exact_mod_cast h1
  have h3 : ((firstCoordDiff 0 y : ℤ) : ℝ) ^ 2 = ((firstCoordDiff 0 y).natAbs : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rw [h3]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) h2 2
private theorem abs_kernelSecondMoment_le {n : ℕ} [NeZero n] (K : TorusBond n → TorusBond n → ℝ) {E : ℝ} (hE : 0 ≤ E)
    (h : ∀ c c', |K c c'| ≤ E) : |kernelSecondMoment K| ≤ (n : ℝ) ^ 6 * E := by
  have hn2 : 0 ≤ (n : ℝ) ^ 2 * E := by positivity
  have hn6 : 0 ≤ (n : ℝ) ^ 6 * E := by positivity
  have hterm : ∀ y : TorusSite n,
      |if supDist 0 y ≤ 2 * momentCutoff n then
        ((firstCoordDiff 0 y : ℤ) : ℝ) ^ 2 * K (0, secondAxis) (y, secondAxis) else 0| ≤
        (n : ℝ) ^ 2 * E := by
    intro y
    split_ifs
    · rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (firstCoordDiff_sq_le y) (h _ _) (abs_nonneg _) (by positivity)
    · simpa using hn2
  have hcard : Fintype.card (TorusSite n) = n ^ 4 := by simp [ZMod.card]
  have hsum : |∑ y : TorusSite n, if supDist 0 y ≤ 2 * momentCutoff n then
      ((firstCoordDiff 0 y : ℤ) : ℝ) ^ 2 * K (0, secondAxis) (y, secondAxis) else 0| ≤
      (n : ℝ) ^ 6 * E := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _y : TorusSite n, (n : ℝ) ^ 2 * E := Finset.sum_le_sum fun y _ => hterm y
      _ = (n : ℝ) ^ 6 * E := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
        push_cast
        ring
  unfold kernelSecondMoment
  rw [abs_mul, show |(-(1 / 2) : ℝ)| = 1 / 2 by norm_num [abs_of_neg]]
  linarith [abs_nonneg (∑ y : TorusSite n, if supDist 0 y ≤ 2 * momentCutoff n then
      ((firstCoordDiff 0 y : ℤ) : ℝ) ^ 2 * K (0, secondAxis) (y, secondAxis) else 0)]
theorem couplingStepBound (hMove : CouplingShiftEqualsGaugeMoment) (hKer : LaplaceRemainderHessianClose)
    (hTot : GaugeTotalMomentNearStepCoefficient) (hRow : MinimizerDensityMomentDecay)
    (hSl : StepCoefficientsHaveSlope) : SlopeCoefficient.CouplingStepBound := by
  obtain ⟨r₁, hr₁, hMove⟩ := hMove
  obtain ⟨r₂, hr₂, hKer⟩ := hKer
  obtain ⟨r₃, C₃f, c₃f, hr₃, hC₃f, hc₃f, hTot⟩ := hTot
  obtain ⟨r₄, hr₄, hRow⟩ := hRow
  refine ⟨fun c => min (min (r₁ c) (r₂ c)) (min (r₃ c) (r₄ c)),
    fun c => lt_min (lt_min (hr₁ c) (hr₂ c)) (lt_min (hr₃ c) (hr₄ c)), fun T hT hrt => ?_⟩
  have hrt₁ := hrt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrt₂ := hrt.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrt₃ := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrt₄ := hrt.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C₀, hC₀, hMove⟩ := hMove T hT hrt₁
  obtain ⟨C₂, p, hC₂, hp, hKer⟩ := hKer T hT hrt₂
  have hTot := hTot T hT hrt₃
  obtain ⟨C₄, c₄, hC₄, hc₄, hRow⟩ := hRow T hT hrt₄
  obtain ⟨C₃, hC₃def⟩ : ∃ C₃, C₃ = C₃f T.toChainParameters := ⟨_, rfl⟩
  obtain ⟨c₃, hc₃def⟩ : ∃ c₃, c₃ = c₃f T.toChainParameters := ⟨_, rfl⟩
  have hC₃ : 0 < C₃ := hC₃def ▸ hC₃f _
  have hc₃ : 0 < c₃ := hc₃def ▸ hc₃f _
  rw [← hC₃def, ← hc₃def] at hTot
  obtain ⟨C₁, hC₁def⟩ : ∃ C₁, C₁ = max C₀ (max (1 / (4 * c₃)) (1 / (4 * c₄))) := ⟨_, rfl⟩
  have hC₁₀ : C₀ ≤ C₁ := hC₁def ▸ le_max_left _ _
  have hC₁pos : 0 < C₁ := lt_of_lt_of_le hC₀ hC₁₀
  have hcC₃ : 1 / 4 ≤ c₃ * C₁ := by
    have h : 1 / (4 * c₃) ≤ C₁ := hC₁def ▸ (le_max_left _ _).trans (le_max_right _ _)
    have h2 := mul_le_mul_of_nonneg_left h hc₃.le
    have h3 : c₃ * (1 / (4 * c₃)) = 1 / 4 := by field_simp
    linarith
  have hcC₄ : 1 / 4 ≤ c₄ * C₁ := by
    have h : 1 / (4 * c₄) ≤ C₁ := hC₁def ▸ (le_max_right _ _).trans (le_max_right _ _)
    have h2 := mul_le_mul_of_nonneg_left h hc₄.le
    have h3 : c₄ * (1 / (4 * c₄)) = 1 / 4 := by field_simp
    linarith
  obtain ⟨C, ys₁, hC, hMove⟩ := hMove C₁ hC₁₀
  obtain ⟨b, -, -, hb, -, -⟩ := hSl T.coupling T.side ⟨T, hT, rfl, rfl⟩
  obtain ⟨_, _, hlam, _⟩ := hT.chain
  have hn₀4096 : 4096 ≤ T.n₀ := hT.n₀_ge
  obtain ⟨ys₂, hfl⟩ := Filter.eventually_atTop.mp
    (eventually_stepTorusSide_bounds (n₀ := T.n₀) (by omega) hC₁pos.le hC₂.le hp (half_pos hlam))
  have hB0 : 1 ≤ T.B := hT.B_ge
  refine ⟨b, C + 1 + C₃ * Real.exp c₃ + C₄ * Real.exp c₄,
    max (max ys₁ ys₂) (max 1 (max (202 * T.B) (16 * T.B ^ 2))), hb, by positivity, ?_⟩
  intro y hy hret t x D hx hDrow x' hD'
  have hyx : y ≤ x := (le_max_left _ _).trans hx
  have hys : max (max ys₁ ys₂) (max 1 (max (202 * T.B) (16 * T.B ^ 2))) ≤ x :=
    (le_max_right _ _).trans hx
  have hys₁ : ys₁ ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hys
  have hys₂ : ys₂ ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hys
  have hx1 : 1 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hys
  have hxB : 202 * T.B ≤ x :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hys
  have hxB2 : 16 * T.B ^ 2 ≤ x :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hys
  have hx0 : 0 < x := by linarith
  obtain ⟨harr, f, hcold, Λ, Dq, Φ, φ, hhull⟩ := hDrow
  have hDrow' : HasExpansion (T.stepParameters y) t x D := ⟨harr, f, hcold, Λ, Dq, Φ, φ, hhull⟩
  obtain ⟨-, f', hcold', -⟩ := id hD'
  obtain ⟨x₀, ⟨-, hmove⟩, huniq⟩ := hret t x D hyx hDrow'
  have hx₀ : x' = x₀ := huniq x' f' hcold'
  subst hx₀
  have hmove' := abs_le.mp hmove
  have hlow : x' - x ≥ -(2 * T.B) := hmove'.1
  have hx101 : x ≤ 1.01 * x' := by nlinarith
  have hr' : clusterRange x ≤ clusterRange x' + 1 :=
    clusterRange_le_succ hB0 hx0.le (by nlinarith) (by linarith)
  let R : StepSetup := ⟨T.stepParameters y, t, x, x', D, f, Λ, Dq, Φ, φ, T.ρA, T.cutoff⟩
  have hOn : R.OnParameters T y := ⟨rfl, rfl, rfl, hyx, ⟨⟨hcold, hhull⟩, hx101, hr'⟩⟩
  have hArr : R.IsSymmetricWeight := harr
  obtain ⟨hside, hsmall, hsize⟩ := hfl x hys₂
  obtain ⟨n, hn⟩ : ∃ n, n = stepTorusSide T.n₀ C₁ x := ⟨_, rfl⟩
  rw [← hn] at hside hsmall hsize
  have hn₀ : T.n₀ ≤ n := by
    rw [hn]
    unfold stepTorusSide
    omega
  have hn64 : 64 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  have hm₀ : n ≤ 4 * R.frameReach + 5 := by
    have h : n ≤ R.frameReach := hside
    omega
  have e₁ := hMove y R x' f' hy hOn hArr hys₁ hmove hcold' n quaternionI hn norm_quaternionI
  have e₂ := (hKer y R hy hOn hArr n hn₀ hm₀ hsmall).2
  have e₃ := hTot t (b t) (hb t) n quaternionI hn64 norm_quaternionI
  have e₄ := hRow y R hy hOn hArr n quaternionI hn₀ norm_quaternionI
  obtain ⟨ML, hML⟩ : ∃ ML, ML = gaugeTotalMoment (laplaceRemainder R) n quaternionI := ⟨_, rfl⟩
  obtain ⟨MS, hMS⟩ : ∃ MS, MS = gaugeTotalMoment (stepGaugeTotal T.coupling T.ρA T.side t) n quaternionI := ⟨_, rfl⟩
  obtain ⟨MR, hMR⟩ : ∃ MR, MR = gaugeTotalMoment (densityAtMinimizer R) n quaternionI := ⟨_, rfl⟩
  have hE0 : 0 ≤ C₂ * (n : ℝ) ^ p * x ^ (-(1 / 2) : ℝ) := by
    have hN0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have := Real.rpow_nonneg hN0 p
    have := Real.rpow_pos_of_pos hx0 (-(1 / 2) : ℝ)
    positivity
  have e₅ : |ML - MS - MR| ≤ x ^ (-(1 / 4) : ℝ) := by
    rw [hML, hMS, hMR]
    unfold gaugeTotalMoment
    rw [kernelSecondMoment_sub]
    exact (abs_kernelSecondMoment_le _ hE0 fun c c' => e₂ c c' quaternionI quaternionI norm_quaternionI norm_quaternionI).trans
      hsize
  rw [← hML] at e₁
  rw [← hMS] at e₃
  rw [← hMR] at e₄
  have hu : 0 < x ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hx0 _
  have e₁' : |x - x' - ML| ≤ C * x ^ (-(1 / 4) : ℝ) := by
    refine e₁.trans ?_
    have hinv : x⁻¹ ≤ x ^ (-(1 / 4) : ℝ) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hc := mul_le_mul_of_nonneg_left hinv hC.le
    exact hc
  have e₃' : |MS - b t| ≤ C₃ * Real.exp c₃ * x ^ (-(1 / 4) : ℝ) := by
    have h := exp_neg_mul_stepTorusSide_le (n₀ := T.n₀) hc₃ hcC₃ hx1
    rw [← hn] at h
    have h2 := mul_le_mul_of_nonneg_left h hC₃.le
    calc _ ≤ _ := e₃
      _ ≤ _ := h2
      _ = _ := by ring
  have e₄' : |MR| ≤ C₄ * Real.exp c₄ * x ^ (-(1 / 4) : ℝ) := by
    have h := exp_neg_mul_stepTorusSide_le (n₀ := T.n₀) hc₄ hcC₄ hx1
    rw [← hn] at h
    have h2 := mul_le_mul_of_nonneg_left h hC₄.le
    calc _ ≤ _ := e₄
      _ ≤ _ := h2
      _ = _ := by ring
  have key : x - x' - b t = (x - x' - ML) + (ML - MS - MR) + (MS - b t) + MR := by ring
  rw [key]
  have a₁ := abs_add_le ((x - x' - ML) + (ML - MS - MR) + (MS - b t)) MR
  have a₂ := abs_add_le ((x - x' - ML) + (ML - MS - MR)) (MS - b t)
  have a₃ := abs_add_le (x - x' - ML) (ML - MS - MR)
  have hsum : (C + 1 + C₃ * Real.exp c₃ + C₄ * Real.exp c₄) * x ^ (-(1 / 4) : ℝ) =
      C * x ^ (-(1 / 4) : ℝ) + x ^ (-(1 / 4) : ℝ) + C₃ * Real.exp c₃ * x ^ (-(1 / 4) : ℝ) +
        C₄ * Real.exp c₄ * x ^ (-(1 / 4) : ℝ) := by ring
  rw [hsum]
  linarith
end RunningCouplingSlope.CouplingStep
end YangMills.Construction
end
