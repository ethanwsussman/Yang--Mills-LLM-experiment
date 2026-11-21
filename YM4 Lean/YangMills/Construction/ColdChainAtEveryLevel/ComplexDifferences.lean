import YangMills.Construction.ColdChainAtEveryLevel.ComplexLevels
import YangMills.Construction.ColdChainAtEveryLevel.HullsOfTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.ComplexDifferences
open ComplexifiedQuaternions BlockAverages ComplexContours ComplexRemainders ComplexLevels LevelRecursion HullBounds
  ComplexChainStep LatticePaths LatticeFractionalIntegration FiniteDifferences
variable {F : BlockFrame} {j : ℕ}
def hullBallRadius (L : ℕ) : ℝ := 1 / (8192 * (L : ℝ))
theorem eight_mul_le_of_lt_hullBallRadius (hodd : Odd F.blockSide) {N : ℝ} (hN : N < hullBallRadius F.blockSide) :
    8 * (F.blockSide : ℝ) * N ≤ 1 / 1024 := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  unfold hullBallRadius at hN
  rw [lt_div_iff₀ (by positivity)] at hN
  nlinarith
theorem differentiableAt_transportedAverage_line (R : F.GaugeField j) (y e : F.Site j → Fin 4 → ComplexQuat)
    (c : F.Site (j + 1) × Fin 4) (z : ℂ) :
    DifferentiableAt ℂ (fun w => transportedAverage R (y + w • e) c) z := by
  simp only [transportedAverage, blockContourMean]
  have hs : DifferentiableAt ℂ (fun w => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      ∑ r ∈ Finset.range F.blockSide,
      conjByUnit (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
        ((y + w • e) (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2)) z := by
    refine DifferentiableAt.fun_sum fun h _ => DifferentiableAt.fun_sum fun π _ =>
      DifferentiableAt.fun_sum fun r _ => ?_
    exact differentiableAt_conjByUnit_comp _ (differentiableAt_fieldLine y e z _ _)
  exact hs.const_smul (contourWeight F)
theorem unitRemainder_quadraticBound (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {R : F.GaugeField j}
    {c : F.Site (j + 1) × Fin 4} {σ : ℝ} (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy R (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage R c))⁻¹) - 1‖ ≤ σ) :
    QuadraticBoundOnBall (bondHullNorm c) (unitRemainder R c) (200000 * (F.blockSide : ℝ) ^ 2) σ
      (hullBallRadius F.blockSide) where
  triangle := bondHullNorm_add_le c
  homogeneous := bondHullNorm_smul c
  holomorphic := by
    intro y e z hz
    have hsm := eight_mul_le_of_lt_hullBallRadius hodd hz
    obtain ⟨hre, -, -⟩ := remainder_bounds hodd hj hσ hsm href
    have hd := differentiableAt_liftedBondMean (z := 0) hodd hj y e hsm href
    have hne : (liftedBondMean R c (y + z • e)).det ≠ 0 := by
      intro h0
      rw [h0] at hre
      simp at hre
    have hne2 : liftedBondMean R c (y + z • e) ≠ 0 := by
      intro h0
      rw [h0] at hne
      simp at hne
    have hu := differentiableAt_unitPart_comp hd hne2 (Or.inl hre)
    simp only [unitRemainder]
    exact ((hu.fun_mul (differentiableAt_const _)).fun_sub (differentiableAt_const _)).fun_sub
      (differentiableAt_purePart_comp (differentiableAt_transportedAverage_line R y e c z))
  bound := fun y hy => (remainder_bounds hodd hj hσ (eight_mul_le_of_lt_hullBallRadius hodd hy) href).2.1
theorem sqrtRemainder_quadraticBound (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {R : F.GaugeField j}
    {c : F.Site (j + 1) × Fin 4} {σ : ℝ} (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy R (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage R c))⁻¹) - 1‖ ≤ σ) :
    QuadraticBoundOnBall (bondHullNorm c) (sqrtRemainder R c) (200000 * (F.blockSide : ℝ) ^ 2) σ
      (hullBallRadius F.blockSide) where
  triangle := bondHullNorm_add_le c
  homogeneous := bondHullNorm_smul c
  holomorphic := by
    intro y e z hz
    have hsm := eight_mul_le_of_lt_hullBallRadius hodd hz
    obtain ⟨hre, -, -⟩ := remainder_bounds hodd hj hσ hsm href
    have hd := differentiableAt_liftedBondMean (z := 0) hodd hj y e hsm href
    simp only [sqrtRemainder]
    exact (differentiableAt_principalSqrt_comp (differentiableAt_det_comp hd) (Or.inl hre)).fun_sub
      (differentiableAt_const _)
  bound := fun y hy => (remainder_bounds hodd hj hσ (eight_mul_le_of_lt_hullBallRadius hodd hy) href).2.2
section
theorem two_pow_succ_le_factorial_add_two (n : ℕ) : 2 ^ (n + 1) ≤ (n + 2).factorial := by
  induction n with
  | zero => simp [Nat.factorial]
  | succ n ih =>
    rw [Nat.factorial_succ (n + 2), pow_succ]
    nlinarith
theorem norm_exp_sub_one_sub_le {x : ComplexQuat} (hx : ‖x‖ ≤ 1) : ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 := by
  have hs : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • x ^ n) (NormedSpace.exp x) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x
  have h2 : HasSum (fun n : ℕ => (((n + 2).factorial : ℂ)⁻¹) • x ^ (n + 2)) (NormedSpace.exp x - 1 - x) := by
    have := (hasSum_nat_add_iff' 2).2 hs
    simpa [Finset.sum_range_succ, sub_sub] using this
  have hg : HasSum (fun n : ℕ => ‖x‖ ^ 2 * (1 / 2 : ℝ) ^ (n + 1)) (‖x‖ ^ 2) := by
    have h3 := hasSum_geometric_two.mul_left ((1 / 2 : ℝ))
    have h4 := h3.mul_left (‖x‖ ^ 2)
    have e : ‖x‖ ^ 2 * (1 / 2 * 2) = ‖x‖ ^ 2 := by ring
    rw [e] at h4
    have e2 : (fun n : ℕ => ‖x‖ ^ 2 * (1 / 2 : ℝ) ^ (n + 1)) =
        fun n : ℕ => ‖x‖ ^ 2 * (1 / 2 * (1 / 2 : ℝ) ^ n) := by
      funext n
      rw [pow_succ]
      ring
    rw [e2]
    exact h4
  have hb : ∀ n : ℕ, ‖((((n + 2).factorial : ℂ)⁻¹) • x ^ (n + 2))‖ ≤ ‖x‖ ^ 2 * (1 / 2) ^ (n + 1) := by
    intro n
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    have h3 : ((2 : ℝ) ^ (n + 1)) ≤ ((n + 2).factorial : ℝ) := by
      exact_mod_cast two_pow_succ_le_factorial_add_two n
    have h4 : ‖x ^ (n + 2)‖ ≤ ‖x‖ ^ 2 := by
      refine (norm_pow_le _ _).trans ?_
      rw [pow_add, mul_comm]
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) hx)
    have h5 : (((n + 2).factorial : ℝ))⁻¹ ≤ (1 / 2 : ℝ) ^ (n + 1) := by
      rw [one_div, inv_pow]
      exact inv_anti₀ (by positivity) h3
    calc _ ≤ (1 / 2 : ℝ) ^ (n + 1) * ‖x‖ ^ 2 := mul_le_mul h5 h4 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  rw [← h2.tsum_eq]
  exact tsum_of_norm_bounded hg hb
end
section
theorem unitExp_zero : unitExp 0 = 1 := by
  rw [unitExp, NormedSpace.exp_zero]
  exact unitPart_of_det_eq_one (by simp)
theorem norm_unitExp_sub_one_sub_purePart_le {y : ComplexQuat} (hy : ‖y‖ ≤ 1 / 16) :
    ‖unitExp y - 1 - purePart y‖ ≤ 129 * ‖y‖ ^ 2 := by
  have hy0 := norm_nonneg y
  have h1 := norm_exp_sub_one_sub_le (x := y) (by linarith)
  set f := NormedSpace.exp y - 1 with hf
  have hf1 : ‖f‖ ≤ 2 * ‖y‖ := by
    have e : f = (NormedSpace.exp y - 1 - y) + y := by
      rw [hf]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    nlinarith
  have e1 : NormedSpace.exp y = 1 + f := by
    rw [hf]
    abel
  have h2 := norm_unitPart_one_add_sub_le (e := f) (by linarith)
  have h3 : purePart f - purePart y = purePart (f - y) := (purePart_sub _ _).symm
  have h4 : ‖purePart f - purePart y‖ ≤ ‖y‖ ^ 2 := by
    rw [h3]
    refine (norm_purePart_le _).trans ?_
    have e2 : f - y = NormedSpace.exp y - 1 - y := by rw [hf]
    rw [e2]
    exact h1
  have h5 : unitExp y - 1 - purePart y = (unitPart (1 + f) - 1 - purePart f) + (purePart f - purePart y) := by
    rw [unitExp, e1]
    abel
  rw [h5]
  refine (norm_add_le _ _).trans ?_
  have h6 : ‖f‖ ^ 2 ≤ (2 * ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hf1 2
  nlinarith
theorem differentiableAt_unitExp_comp {f : ℂ → ComplexQuat} {z : ℂ} (hf : DifferentiableAt ℂ f z)
    (h : ‖f z‖ ≤ 1 / 16) : DifferentiableAt ℂ (fun w => unitExp (f w)) z := by
  have hy0 := norm_nonneg (f z)
  have h1 := norm_exp_sub_one_sub_le (x := f z) (by linarith)
  have hf1 : ‖NormedSpace.exp (f z) - 1‖ ≤ 1 / 8 := by
    have e : NormedSpace.exp (f z) - 1 = (NormedSpace.exp (f z) - 1 - f z) + f z := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    nlinarith
  obtain ⟨h2, h3⟩ := one_add_ne_zero_and_det_mem_slitPlane hf1
  rw [add_sub_cancel] at h2 h3
  have hexp : DifferentiableAt ℂ (fun w => NormedSpace.exp (f w)) z := by
    have ha := NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℂ) (f z) (by
      rw [NormedSpace.expSeries_radius_eq_top ℂ ComplexQuat]
      exact edist_lt_top _ _)
    exact ha.differentiableAt.comp z hf
  exact differentiableAt_unitPart_comp hexp h2 h3
theorem unitExp_quadraticBound {σ : ℝ} (hσ : 0 ≤ σ) :
    QuadraticBoundOnBall (fun e : ComplexQuat => ‖e‖) (fun e => unitExp e - 1 - purePart e) 129 σ (1 / 16) where
  triangle := norm_add_le
  homogeneous := fun z a => norm_smul z a
  holomorphic := by
    intro y e z hz
    have hl : DifferentiableAt ℂ (fun w : ℂ => y + w • e) z :=
      (differentiableAt_const _).fun_add (differentiableAt_id.fun_smul (differentiableAt_const _))
    exact ((differentiableAt_unitExp_comp hl hz.le).fun_sub (differentiableAt_const _)).fun_sub
      (differentiableAt_purePart_comp hl)
  bound := by
    intro y hy
    have := norm_unitExp_sub_one_sub_purePart_le hy.le
    have : 0 ≤ σ * ‖y‖ := by positivity
    nlinarith
theorem norm_unitExp_sub_le {y y' : ComplexQuat} (hy : ‖y‖ ≤ 1 / 4000) (hy' : ‖y'‖ ≤ 1 / 4000) :
    ‖unitExp y' - unitExp y‖ ≤ 2 * ‖y' - y‖ := by
  have h := (unitExp_quadraticBound (σ := 1 / 4000) (by norm_num)).norm_sub_le (by norm_num) (by norm_num)
    (t := 1 / 4000) (by norm_num) (by norm_num) hy hy'
  have e : unitExp y' - unitExp y =
      ((unitExp y' - 1 - purePart y') - (unitExp y - 1 - purePart y)) + purePart (y' - y) := by
    rw [purePart_sub]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h2 := norm_purePart_le (y' - y)
  have h3 := norm_nonneg (y' - y)
  nlinarith
theorem norm_unitExp_sub_one_le {y : ComplexQuat} (hy : ‖y‖ ≤ 1 / 4000) : ‖unitExp y - 1‖ ≤ 2 * ‖y‖ := by
  have h := norm_unitExp_sub_le (y := 0) (y' := y) (by simp) hy
  rwa [unitExp_zero, sub_zero] at h
theorem norm_unitExp_second_diff_le {y e₁ e₂ : ComplexQuat} (hy : ‖y‖ ≤ 1 / 4000) (h1 : ‖e₁‖ ≤ 1 / 4000)
    (h2 : ‖e₂‖ ≤ 1 / 4000) :
    ‖unitExp (y + e₁ + e₂) - unitExp (y + e₁) - unitExp (y + e₂) + unitExp y‖ ≤ 8256 * ‖e₁‖ * ‖e₂‖ := by
  have h := (unitExp_quadraticBound (σ := 1 / 4000) (by norm_num)).norm_second_diff_le (by norm_num) (by norm_num)
    (by norm_num) (y := y) (e₁ := e₁) (e₂ := e₂) (t := 1 / 4000) (by norm_num) (by norm_num) hy h1 h2
  have e : unitExp (y + e₁ + e₂) - unitExp (y + e₁) - unitExp (y + e₂) + unitExp y =
      (unitExp (y + e₁ + e₂) - 1 - purePart (y + e₁ + e₂)) - (unitExp (y + e₁) - 1 - purePart (y + e₁)) -
        (unitExp (y + e₂) - 1 - purePart (y + e₂)) + (unitExp y - 1 - purePart y) := by
    simp only [purePart_add]
    abel
  rw [e]
  linarith
end
section
theorem lineBlockAverage_le_bondHullSum (hodd : Odd F.blockSide) {f : F.Site j → Fin 4 → ℝ}
    (hf : ∀ x d, 0 ≤ f x d) (c : F.Site (j + 1) × Fin 4) : lineBlockAverage f c ≤ bondHullSum c f := by
  have hL : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have h0 : 0 ≤ ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
      f (BlockLines.lineBond c h r).1 (BlockLines.lineBond c h r).2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hf _ _
  have h1 : 0 ≤ ∑ h ∈ centredCube F.blockSide, ∑ k : Fin 4, if h + Pi.single k 1 ∈ centredCube F.blockSide then
      f (refineSite c.1 + siteOfCoords j h) k +
        f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k else 0 := by
    refine Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun k _ => ?_
    split_ifs
    · exact add_nonneg (hf _ _) (hf _ _)
    · exact le_rfl
  have e : lineBlockAverage f c = 1 / (F.blockSide : ℝ) ^ 4 *
      ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
        f (BlockLines.lineBond c h r).1 (BlockLines.lineBond c h r).2 := rfl
  rw [e]
  have h2 : 1 / (F.blockSide : ℝ) ^ 4 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ hL
  unfold bondHullSum
  nlinarith
def linearizedUnit (R : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) (y : F.Site j → Fin 4 → ComplexQuat) :
    ComplexQuat :=
  1 + purePart (transportedAverage R y c) + unitRemainder R c y
theorem norm_linearizedUnit_sub_le (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {R : F.GaugeField j}
    {c : F.Site (j + 1) × Fin 4} {σ t : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy R (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage R c))⁻¹) - 1‖ ≤ σ) (ht : 0 ≤ t)
    (hsm : 3 * (t + σ) < hullBallRadius F.blockSide)
    {y y' : F.Site j → Fin 4 → ComplexQuat} (hy : bondHullNorm c y ≤ t) (hy' : bondHullNorm c y' ≤ t) :
    ‖linearizedUnit R c y' - linearizedUnit R c y‖ ≤ lineBlockAverage (fun x d => ‖(y' - y) x d‖) c +
      12 * (200000 * (F.blockSide : ℝ) ^ 2) * (t + σ) * bondHullNorm c (y' - y) := by
  have hq := (unitRemainder_quadraticBound hodd hj hσ href).norm_sub_le (by positivity) hσ0 ht hsm hy hy'
  have e : linearizedUnit R c y' - linearizedUnit R c y =
      purePart (transportedAverage R (fun x d => (y' - y) x d) c) + (unitRemainder R c y' - unitRemainder R c y) := by
    have e1 : (fun x d => (y' - y) x d) = fun x d => y' x d - y x d := rfl
    rw [e1, transportedAverage_sub, purePart_sub]
    simp only [linearizedUnit]
    abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ hq)
  exact (norm_purePart_le _).trans (norm_transportedAverage_le hodd R _ c)
theorem norm_linearizedUnit_le_two (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {R : F.GaugeField j}
    {c : F.Site (j + 1) × Fin 4} {σ : ℝ} (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy R (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage R c))⁻¹) - 1‖ ≤ σ)
    {y : F.Site j → Fin 4 → ComplexQuat} (hy : 3 * (bondHullNorm c y + σ) < hullBallRadius F.blockSide) :
    ‖linearizedUnit R c y‖ ≤ 2 := by
  have hL : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hNN : 0 ≤ bondHullNorm c y := bondHullSum_nonneg c fun _ _ => norm_nonneg _
  have hσ0 : 0 ≤ σ := by
    have h0 : (0 : Lattice4) ∈ centredCube F.blockSide := by
      rw [mem_centredCube_iff]
      intro i
      have := hodd.pos
      simp only [Pi.zero_apply]
      omega
    exact (norm_nonneg _).trans (href 0 h0 1)
  have hsm := eight_mul_le_of_lt_hullBallRadius hodd (N := bondHullNorm c y) (by linarith)
  obtain ⟨-, hq, -⟩ := remainder_bounds hodd hj hσ hsm href
  set N := bondHullNorm c y with hN
  have h1 : ‖purePart (transportedAverage R y c)‖ ≤ N :=
    (norm_purePart_le _).trans ((norm_transportedAverage_le hodd R _ c).trans
      (lineBlockAverage_le_bondHullSum hodd (fun _ _ => norm_nonneg _) c))
  have hLN : (F.blockSide : ℝ) * (N + σ) ≤ 1 / 8192 := by
    have h9 : (N + σ) ≤ hullBallRadius F.blockSide := by linarith
    unfold hullBallRadius at h9
    rw [le_div_iff₀ (by positivity)] at h9
    nlinarith
  have hLN0 : 0 ≤ (F.blockSide : ℝ) * (N + σ) := by positivity
  have hq2 : ‖unitRemainder R c y‖ ≤ 1 / 4 := by
    refine hq.trans ?_
    have e : 200000 * (F.blockSide : ℝ) ^ 2 * (N + σ) ^ 2 = 200000 * ((F.blockSide : ℝ) * (N + σ)) ^ 2 := by ring
    have h2 : ((F.blockSide : ℝ) * (N + σ)) ^ 2 ≤ (1 / 8192) ^ 2 := pow_le_pow_left₀ hLN0 hLN 2
    have h5 : N ^ 2 + σ * N ≤ (N + σ) ^ 2 := by nlinarith
    have h6 : 200000 * (F.blockSide : ℝ) ^ 2 * (N ^ 2 + σ * N) ≤ 200000 * (F.blockSide : ℝ) ^ 2 * (N + σ) ^ 2 :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    rw [e] at h6
    linarith
  have h3 : N ≤ 1 / 8192 := by nlinarith
  simp only [linearizedUnit]
  have := norm_add_le (1 + purePart (transportedAverage R y c)) (unitRemainder R c y)
  have h4 := norm_add_le (1 : ComplexQuat) (purePart (transportedAverage R y c))
  rw [CStarRing.norm_one] at h4
  linarith
end
section
theorem transportedAverage_add (R : F.GaugeField j) (f g : F.Site j → Fin 4 → ComplexQuat)
    (c : F.Site (j + 1) × Fin 4) :
    transportedAverage R (fun x i => f x i + g x i) c = transportedAverage R f c + transportedAverage R g c := by
  simp only [transportedAverage, ← blockContourMean_add, ← Finset.sum_add_distrib, conjByUnit_add]
theorem second_diff_bound_arith {ε₀ a b D n₁ n₂ h Qd Lip Gn K₆ : ℝ} (hK₆ : 0 ≤ K₆) (hτ : ε₀ + a + b + D ≤ 1)
    (hε₀ : 0 ≤ ε₀) (ha : 0 ≤ a) (hb : 0 ≤ b) (hD : 0 ≤ D) (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂) (hn₁' : n₁ ≤ 1)
    (hn₂' : n₂ ≤ 1) (hh : 0 ≤ h) (hQ : 0 ≤ Qd) (hQh : Qd ≤ h) (hLip : 0 ≤ Lip) (hGn : 0 ≤ Gn)
    (hG : Gn ≤ Qd + Lip * h + 64 * K₆ * n₁ * n₂) :
    (1 + ε₀) * Gn + D * 2 + a * (2 * n₂) + b * (2 * n₁) + (a + b + D) * Gn + D * (2 * n₁ + 2 * n₂) ≤
      Qd + ((128 * K₆ * n₁ * n₂ + 6 * D + 2 * a * n₂ + 2 * b * n₁) + (ε₀ + a + b + D + 2 * Lip) * h) := by
  set τ := ε₀ + a + b + D with hτd
  have hτ0 : 0 ≤ τ := by positivity
  have h1 : (1 + τ) * Gn ≤ (1 + τ) * (Qd + Lip * h + 64 * K₆ * n₁ * n₂) :=
    mul_le_mul_of_nonneg_left hG (by positivity)
  have h2 : τ * Qd ≤ τ * h := mul_le_mul_of_nonneg_left hQh hτ0
  have h3 : τ * (Lip * h) ≤ 1 * (Lip * h) := mul_le_mul_of_nonneg_right hτ (by positivity)
  have hX : 0 ≤ 64 * K₆ * n₁ * n₂ := by positivity
  have h4 : τ * (64 * K₆ * n₁ * n₂) ≤ 1 * (64 * K₆ * n₁ * n₂) := mul_le_mul_of_nonneg_right hτ hX
  have h5 : D * (2 * n₁ + 2 * n₂) ≤ D * 4 := mul_le_mul_of_nonneg_left (by linarith) hD
  have e3 : (τ + 2 * Lip) * h = τ * h + 2 * (Lip * h) := by ring
  rw [e3]
  have e4 : 128 * K₆ * n₁ * n₂ = 2 * (64 * K₆ * n₁ * n₂) := by ring
  rw [e4]
  linarith
theorem levelDeviation_succ_eq (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) (R : F.FieldChain)
    (W : ComplexChainChart F) {c : F.Site (j + 1) × Fin 4}
    (h : HoldsOnHull c (fun b i => (complexChartField R W j b i).det = 1)) :
    levelDeviation R W (j + 1) c.1 c.2 = levelSource W j c.1 c.2 *
      conjByUnit (referenceDefect R j c) (linearizedUnit (R j) c (levelDeviation R W j)) - 1 := by apply _root_.YangMills.Construction.ComplexLevels.levelDeviation_succ <;> assumption
theorem norm_levelDeviation_succ_sub_le (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) (R : F.FieldChain)
    (W W' : ComplexChainChart F) {c : F.Site (j + 1) × Fin 4} {σ t : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy (R j) (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤ σ) (ht : 0 ≤ t)
    (hsm : 3 * (t + σ) < hullBallRadius F.blockSide)
    (hy : bondHullNorm c (levelDeviation R W j) ≤ t) (hy' : bondHullNorm c (levelDeviation R W' j) ≤ t)
    (hd : HoldsOnHull c (fun b i => (complexChartField R W j b i).det = 1))
    (hd' : HoldsOnHull c (fun b i => (complexChartField R W' j b i).det = 1))
    (hE : ‖levelSource W j c.1 c.2 - 1‖ ≤ 1) :
    ‖levelDeviation R W' (j + 1) c.1 c.2 - levelDeviation R W (j + 1) c.1 c.2‖ ≤
      lineBlockAverage (fun z d => ‖(levelDeviation R W' j - levelDeviation R W j) z d‖) c +
        (2 * ‖levelSource W' j c.1 c.2 - levelSource W j c.1 c.2‖ +
          (‖levelSource W j c.1 c.2 - 1‖ + 24 * (200000 * (F.blockSide : ℝ) ^ 2) * (t + σ)) *
            bondHullNorm c (levelDeviation R W' j - levelDeviation R W j)) := by
  set x := levelDeviation R W j with hx
  set x' := levelDeviation R W' j with hx'
  set E := levelSource W j c.1 c.2 with hEd
  set E' := levelSource W' j c.1 c.2 with hE'd
  set μ := referenceDefect R j c with hμ
  set U := linearizedUnit (R j) c x with hU
  set U' := linearizedUnit (R j) c x' with hU'
  set Q := lineBlockAverage (fun z d => ‖(x' - x) z d‖) c with hQ
  set h := bondHullNorm c (x' - x) with hh
  set K := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hQh : Q ≤ h := lineBlockAverage_le_bondHullSum hodd (fun _ _ => norm_nonneg _) c
  have hh0 : 0 ≤ h := bondHullSum_nonneg c fun _ _ => norm_nonneg _
  have hUU := norm_linearizedUnit_sub_le hodd hj hσ0 hσ href ht hsm hy hy'
  rw [← hU, ← hU', ← hQ, ← hh, ← hK] at hUU
  have hU'2 : ‖U'‖ ≤ 2 := norm_linearizedUnit_le_two hodd hj hσ href (by
    have : bondHullNorm c x' + σ ≤ t + σ := by linarith
    linarith)
  have e1 : levelDeviation R W' (j + 1) c.1 c.2 - levelDeviation R W (j + 1) c.1 c.2 =
      (E' - E) * conjByUnit μ U' + E * conjByUnit μ (U' - U) := by
    rw [levelDeviation_succ_eq hodd hj R W' hd', levelDeviation_succ_eq hodd hj R W hd, conjByUnit_sub]
    noncomm_ring
  rw [e1]
  have h1 : ‖(E' - E) * conjByUnit μ U'‖ ≤ ‖E' - E‖ * 2 := by
    refine (norm_mul_le _ _).trans ?_
    rw [norm_conjByUnit]
    exact mul_le_mul_of_nonneg_left hU'2 (norm_nonneg _)
  have hEn : ‖E‖ ≤ 1 + ‖E - 1‖ := by
    have := norm_add_le (1 : ComplexQuat) (E - 1)
    rw [add_sub_cancel, CStarRing.norm_one] at this
    exact this
  set ε := ‖E - 1‖ with hε
  have hε0 : 0 ≤ ε := norm_nonneg _
  set Lip := 12 * K * (t + σ) with hLip
  have h2 : ‖E * conjByUnit μ (U' - U)‖ ≤ (1 + ε) * (Q + Lip * h) := by
    refine (norm_mul_le _ _).trans ?_
    rw [norm_conjByUnit]
    exact mul_le_mul hEn hUU (norm_nonneg _) (by positivity)
  have h3 : (1 + ε) * (Q + Lip * h) ≤ Q + (ε + 2 * Lip) * h := by
    have a1 : ε * Q ≤ ε * h := mul_le_mul_of_nonneg_left hQh hε0
    have a2 : ε * (Lip * h) ≤ 1 * (Lip * h) := mul_le_mul_of_nonneg_right hE (by positivity)
    nlinarith
  have e2 : 24 * K * (t + σ) = 2 * Lip := by
    rw [hLip]
    ring
  rw [e2]
  have h4 := norm_add_le ((E' - E) * conjByUnit μ U') (E * conjByUnit μ (U' - U))
  linarith
theorem norm_levelDeviation_succ_second_diff_le (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) (R : F.FieldChain)
    (W₀ W₁ W₂ W₃ : ComplexChainChart F) {c : F.Site (j + 1) × Fin 4} {σ t : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy (R j) (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤ σ) (ht : 0 ≤ t)
    (hsm : 24 * (3 * t + σ) < hullBallRadius F.blockSide)
    (hLip : 12 * (200000 * (F.blockSide : ℝ) ^ 2) * (3 * t + σ) ≤ 1)
    (h0 : bondHullNorm c (levelDeviation R W₀ j) ≤ t) (h1 : bondHullNorm c (levelDeviation R W₁ j) ≤ t)
    (h2 : bondHullNorm c (levelDeviation R W₂ j) ≤ t) (h3 : bondHullNorm c (levelDeviation R W₃ j) ≤ t)
    (hn1 : bondHullNorm c (levelDeviation R W₁ j - levelDeviation R W₀ j) ≤ t)
    (hn2 : bondHullNorm c (levelDeviation R W₂ j - levelDeviation R W₀ j) ≤ t)
    (hn1' : bondHullNorm c (levelDeviation R W₁ j - levelDeviation R W₀ j) ≤ 1)
    (hn2' : bondHullNorm c (levelDeviation R W₂ j - levelDeviation R W₀ j) ≤ 1)
    (hd0 : HoldsOnHull c (fun b i => (complexChartField R W₀ j b i).det = 1))
    (hd1 : HoldsOnHull c (fun b i => (complexChartField R W₁ j b i).det = 1))
    (hd2 : HoldsOnHull c (fun b i => (complexChartField R W₂ j b i).det = 1))
    (hd3 : HoldsOnHull c (fun b i => (complexChartField R W₃ j b i).det = 1))
    (hτ : ‖levelSource W₀ j c.1 c.2 - 1‖ + ‖levelSource W₁ j c.1 c.2 - levelSource W₀ j c.1 c.2‖ +
      ‖levelSource W₂ j c.1 c.2 - levelSource W₀ j c.1 c.2‖ +
      ‖levelSource W₃ j c.1 c.2 - levelSource W₁ j c.1 c.2 - levelSource W₂ j c.1 c.2 +
        levelSource W₀ j c.1 c.2‖ ≤ 1) :
    ‖levelDeviation R W₃ (j + 1) c.1 c.2 - levelDeviation R W₁ (j + 1) c.1 c.2 -
        levelDeviation R W₂ (j + 1) c.1 c.2 + levelDeviation R W₀ (j + 1) c.1 c.2‖ ≤
      lineBlockAverage (fun z d => ‖(levelDeviation R W₃ j - levelDeviation R W₁ j - levelDeviation R W₂ j +
        levelDeviation R W₀ j) z d‖) c +
      ((128 * (200000 * (F.blockSide : ℝ) ^ 2) * bondHullNorm c (levelDeviation R W₁ j - levelDeviation R W₀ j) *
            bondHullNorm c (levelDeviation R W₂ j - levelDeviation R W₀ j) +
          6 * ‖levelSource W₃ j c.1 c.2 - levelSource W₁ j c.1 c.2 - levelSource W₂ j c.1 c.2 +
            levelSource W₀ j c.1 c.2‖ +
          2 * ‖levelSource W₁ j c.1 c.2 - levelSource W₀ j c.1 c.2‖ *
            bondHullNorm c (levelDeviation R W₂ j - levelDeviation R W₀ j) +
          2 * ‖levelSource W₂ j c.1 c.2 - levelSource W₀ j c.1 c.2‖ *
            bondHullNorm c (levelDeviation R W₁ j - levelDeviation R W₀ j)) +
        (‖levelSource W₀ j c.1 c.2 - 1‖ + ‖levelSource W₁ j c.1 c.2 - levelSource W₀ j c.1 c.2‖ +
          ‖levelSource W₂ j c.1 c.2 - levelSource W₀ j c.1 c.2‖ +
          ‖levelSource W₃ j c.1 c.2 - levelSource W₁ j c.1 c.2 - levelSource W₂ j c.1 c.2 +
            levelSource W₀ j c.1 c.2‖ +
          2 * (12 * (200000 * (F.blockSide : ℝ) ^ 2) * (3 * t + σ))) *
          bondHullNorm c (levelDeviation R W₃ j - levelDeviation R W₁ j - levelDeviation R W₂ j +
            levelDeviation R W₀ j)) := by
  set x₀ := levelDeviation R W₀ j with hx₀
  set x₁ := levelDeviation R W₁ j with hx₁
  set x₂ := levelDeviation R W₂ j with hx₂
  set x₃ := levelDeviation R W₃ j with hx₃
  set E₀ := levelSource W₀ j c.1 c.2
  set E₁ := levelSource W₁ j c.1 c.2
  set E₂ := levelSource W₂ j c.1 c.2
  set E₃ := levelSource W₃ j c.1 c.2
  set μ := referenceDefect R j c with hμ
  set δ₁ := x₁ - x₀ with hδ₁
  set δ₂ := x₂ - x₀ with hδ₂
  set Δ := x₃ - x₁ - x₂ + x₀ with hΔ
  set K := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set Lip := 12 * K * (3 * t + σ) with hLipd
  have hLip0 : 0 ≤ Lip := by positivity
  set n₁ := bondHullNorm c δ₁ with hn₁d
  set n₂ := bondHullNorm c δ₂ with hn₂d
  set h := bondHullNorm c Δ with hhd
  set Qd := lineBlockAverage (fun z d => ‖Δ z d‖) c with hQd
  have hn₁0 : 0 ≤ n₁ := bondHullSum_nonneg c fun _ _ => norm_nonneg _
  have hn₂0 : 0 ≤ n₂ := bondHullSum_nonneg c fun _ _ => norm_nonneg _
  have hh0 : 0 ≤ h := bondHullSum_nonneg c fun _ _ => norm_nonneg _
  have hQ0 : 0 ≤ Qd := _root_.YangMills.Construction.LevelRecursion.lineBlockAverage_nonneg (fun _ _ => norm_nonneg _) c
  have hQh : Qd ≤ h := lineBlockAverage_le_bondHullSum hodd (fun _ _ => norm_nonneg _) c
  set U₀ := linearizedUnit (R j) c x₀ with hU₀
  set U₁ := linearizedUnit (R j) c x₁ with hU₁
  set U₂ := linearizedUnit (R j) c x₂ with hU₂
  set U₃ := linearizedUnit (R j) c x₃ with hU₃
  have hsm3 : 3 * (3 * t + σ) < hullBallRadius F.blockSide := by linarith
  have hU0n : ‖U₀‖ ≤ 2 := norm_linearizedUnit_le_two hodd hj hσ href (by
    have : bondHullNorm c x₀ + σ ≤ t + σ := by linarith
    linarith)
  have hP : ‖U₁ - U₀‖ ≤ 2 * n₁ := by
    have a := norm_linearizedUnit_sub_le hodd hj hσ0 hσ href (t := 3 * t) (by positivity) hsm3 (by linarith)
      (by linarith) (y := x₀) (y' := x₁)
    have b : lineBlockAverage (fun z d => ‖(x₁ - x₀) z d‖) c ≤ n₁ :=
      lineBlockAverage_le_bondHullSum hodd (fun _ _ => norm_nonneg _) c
    have c1 : Lip * n₁ ≤ 1 * n₁ := mul_le_mul_of_nonneg_right hLip hn₁0
    refine a.trans ?_
    have e0 : 12 * (200000 * (F.blockSide : ℝ) ^ 2) * (3 * t + σ) * bondHullNorm c (x₁ - x₀) = Lip * n₁ := rfl
    rw [e0]
    linarith
  have hQ : ‖U₂ - U₀‖ ≤ 2 * n₂ := by
    have a := norm_linearizedUnit_sub_le hodd hj hσ0 hσ href (t := 3 * t) (by positivity) hsm3 (by linarith)
      (by linarith) (y := x₀) (y' := x₂)
    have b : lineBlockAverage (fun z d => ‖(x₂ - x₀) z d‖) c ≤ n₂ :=
      lineBlockAverage_le_bondHullSum hodd (fun _ _ => norm_nonneg _) c
    have c1 : Lip * n₂ ≤ 1 * n₂ := mul_le_mul_of_nonneg_right hLip hn₂0
    refine a.trans ?_
    have e0 : 12 * (200000 * (F.blockSide : ℝ) ^ 2) * (3 * t + σ) * bondHullNorm c (x₂ - x₀) = Lip * n₂ := rfl
    rw [e0]
    linarith
  have hΔfun : transportedAverage (R j) Δ c = transportedAverage (R j) x₃ c - transportedAverage (R j) x₁ c -
      transportedAverage (R j) x₂ c + transportedAverage (R j) x₀ c := by
    have e : Δ = fun z d =>
        (fun z' d' => (fun z'' d'' => x₃ z'' d'' - x₁ z'' d'') z' d' - x₂ z' d') z d + x₀ z d := rfl
    rw [e, transportedAverage_add, transportedAverage_sub (f := fun z' d' => x₃ z' d' - x₁ z' d'),
      transportedAverage_sub]
  set yt := x₀ + δ₁ + δ₂ with hyt
  have hNyt : bondHullNorm c yt ≤ 3 * t := by
    have a := bondHullNorm_add_le c (x₀ + δ₁) δ₂
    have b := bondHullNorm_add_le c x₀ δ₁
    linarith
  have hN3 : bondHullNorm c x₃ ≤ 3 * t := by linarith
  have hq1 := (unitRemainder_quadraticBound hodd hj hσ href).norm_sub_le (by positivity) hσ0
    (t := 3 * t) (by positivity) (by linarith) hNyt hN3
  have e1 : x₃ - yt = Δ := by
    rw [hyt, hδ₁, hδ₂, hΔ]
    abel
  rw [e1, ← hK] at hq1
  have hq2 := (unitRemainder_quadraticBound hodd hj hσ href).norm_second_diff_le (by positivity) hσ0 (by linarith)
    (y := x₀) (e₁ := δ₁) (e₂ := δ₂) ht (by linarith) h0 hn1 hn2
  rw [← hK] at hq2
  have e2 : x₀ + δ₁ = x₁ := by rw [hδ₁]; abel
  have e3 : x₀ + δ₂ = x₂ := by rw [hδ₂]; abel
  have e6 : x₁ + δ₂ = yt := by rw [← e2]
  rw [e2, e3, e6] at hq2
  have hG : ‖U₃ - U₁ - U₂ + U₀‖ ≤ Qd + Lip * h + 64 * K * n₁ * n₂ := by
    have e4 : U₃ - U₁ - U₂ + U₀ = purePart (transportedAverage (R j) Δ c) +
        (unitRemainder (R j) c x₃ - unitRemainder (R j) c yt) +
        (unitRemainder (R j) c yt - unitRemainder (R j) c x₁ - unitRemainder (R j) c x₂ +
          unitRemainder (R j) c x₀) := by
      rw [hΔfun]
      simp only [hU₀, hU₁, hU₂, hU₃, linearizedUnit, purePart_add, purePart_sub]
      abel
    rw [e4]
    have a1 : ‖purePart (transportedAverage (R j) Δ c)‖ ≤ Qd :=
      (norm_purePart_le _).trans (norm_transportedAverage_le hodd _ _ c)
    have a2 := norm_add_le (purePart (transportedAverage (R j) Δ c) +
        (unitRemainder (R j) c x₃ - unitRemainder (R j) c yt))
      (unitRemainder (R j) c yt - unitRemainder (R j) c x₁ - unitRemainder (R j) c x₂ + unitRemainder (R j) c x₀)
    have a3 := norm_add_le (purePart (transportedAverage (R j) Δ c))
      (unitRemainder (R j) c x₃ - unitRemainder (R j) c yt)
    have e5 : 12 * K * (3 * t + σ) = Lip := rfl
    rw [e5] at hq1
    linarith
  have hgap : levelDeviation R W₃ (j + 1) c.1 c.2 - levelDeviation R W₁ (j + 1) c.1 c.2 -
      levelDeviation R W₂ (j + 1) c.1 c.2 + levelDeviation R W₀ (j + 1) c.1 c.2 =
        E₀ * conjByUnit μ (U₃ - U₁ - U₂ + U₀) + (E₃ - E₁ - E₂ + E₀) * conjByUnit μ U₀ +
        (E₁ - E₀) * conjByUnit μ (U₂ - U₀) + (E₂ - E₀) * conjByUnit μ (U₁ - U₀) +
        ((E₁ - E₀) + (E₂ - E₀) + (E₃ - E₁ - E₂ + E₀)) * conjByUnit μ (U₃ - U₁ - U₂ + U₀) +
        (E₃ - E₁ - E₂ + E₀) * (conjByUnit μ (U₁ - U₀) + conjByUnit μ (U₂ - U₀)) := by
    rw [levelDeviation_succ_eq hodd hj R W₃ hd3, levelDeviation_succ_eq hodd hj R W₁ hd1,
      levelDeviation_succ_eq hodd hj R W₂ hd2, levelDeviation_succ_eq hodd hj R W₀ hd0]
    simp only [conjByUnit_add, conjByUnit_sub]
    noncomm_ring
  rw [hgap]
  set ε₀ := ‖E₀ - 1‖ with hε₀
  set a := ‖E₁ - E₀‖ with ha
  set b := ‖E₂ - E₀‖ with hb
  set D := ‖E₃ - E₁ - E₂ + E₀‖ with hD
  have hε₀0 : 0 ≤ ε₀ := norm_nonneg _
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hD0 : 0 ≤ D := norm_nonneg _
  set Gn := ‖U₃ - U₁ - U₂ + U₀‖ with hGn
  have hGn0 : 0 ≤ Gn := norm_nonneg _
  have hE₀ : ‖E₀‖ ≤ 1 + ε₀ := by
    have := norm_add_le (1 : ComplexQuat) (E₀ - 1)
    rw [add_sub_cancel, CStarRing.norm_one] at this
    exact this
  have t1 : ‖E₀ * conjByUnit μ (U₃ - U₁ - U₂ + U₀)‖ ≤ (1 + ε₀) * Gn := by
    refine (norm_mul_le _ _).trans ?_
    rw [norm_conjByUnit]
    exact mul_le_mul_of_nonneg_right hE₀ hGn0
  have t2 : ‖(E₃ - E₁ - E₂ + E₀) * conjByUnit μ U₀‖ ≤ D * 2 := by
    refine (norm_mul_le _ _).trans ?_
    rw [norm_conjByUnit]
    exact mul_le_mul_of_nonneg_left hU0n hD0
  have t3 : ‖(E₁ - E₀) * conjByUnit μ (U₂ - U₀)‖ ≤ a * (2 * n₂) := by
    refine (norm_mul_le _ _).trans ?_
    rw [norm_conjByUnit]
    exact mul_le_mul_of_nonneg_left hQ ha0
  have t4 : ‖(E₂ - E₀) * conjByUnit μ (U₁ - U₀)‖ ≤ b * (2 * n₁) := by
    refine (norm_mul_le _ _).trans ?_
    rw [norm_conjByUnit]
    exact mul_le_mul_of_nonneg_left hP hb0
  have t5 : ‖((E₁ - E₀) + (E₂ - E₀) + (E₃ - E₁ - E₂ + E₀)) * conjByUnit μ (U₃ - U₁ - U₂ + U₀)‖ ≤
      (a + b + D) * Gn := by
    refine (norm_mul_le _ _).trans ?_
    rw [norm_conjByUnit]
    refine mul_le_mul_of_nonneg_right ?_ hGn0
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have t6 : ‖(E₃ - E₁ - E₂ + E₀) * (conjByUnit μ (U₁ - U₀) + conjByUnit μ (U₂ - U₀))‖ ≤
      D * (2 * n₁ + 2 * n₂) := by
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ hD0)
    refine (norm_add_le _ _).trans ?_
    rw [norm_conjByUnit, norm_conjByUnit]
    linarith
  have hall := second_diff_bound_arith hK0 hτ hε₀0 ha0 hb0 hD0 hn₁0 hn₂0 hn1' hn2' hh0 hQ0 hQh hLip0 hGn0 hG
  have s1 := norm_add_le (E₀ * conjByUnit μ (U₃ - U₁ - U₂ + U₀) + (E₃ - E₁ - E₂ + E₀) * conjByUnit μ U₀ +
        (E₁ - E₀) * conjByUnit μ (U₂ - U₀) + (E₂ - E₀) * conjByUnit μ (U₁ - U₀) +
        ((E₁ - E₀) + (E₂ - E₀) + (E₃ - E₁ - E₂ + E₀)) * conjByUnit μ (U₃ - U₁ - U₂ + U₀))
      ((E₃ - E₁ - E₂ + E₀) * (conjByUnit μ (U₁ - U₀) + conjByUnit μ (U₂ - U₀)))
  have s2 := norm_add_le (E₀ * conjByUnit μ (U₃ - U₁ - U₂ + U₀) + (E₃ - E₁ - E₂ + E₀) * conjByUnit μ U₀ +
        (E₁ - E₀) * conjByUnit μ (U₂ - U₀) + (E₂ - E₀) * conjByUnit μ (U₁ - U₀))
      (((E₁ - E₀) + (E₂ - E₀) + (E₃ - E₁ - E₂ + E₀)) * conjByUnit μ (U₃ - U₁ - U₂ + U₀))
  have s3 := norm_add_le (E₀ * conjByUnit μ (U₃ - U₁ - U₂ + U₀) + (E₃ - E₁ - E₂ + E₀) * conjByUnit μ U₀ +
        (E₁ - E₀) * conjByUnit μ (U₂ - U₀)) ((E₂ - E₀) * conjByUnit μ (U₁ - U₀))
  have s4 := norm_add_le (E₀ * conjByUnit μ (U₃ - U₁ - U₂ + U₀) + (E₃ - E₁ - E₂ + E₀) * conjByUnit μ U₀)
      ((E₁ - E₀) * conjByUnit μ (U₂ - U₀))
  have s5 := norm_add_le (E₀ * conjByUnit μ (U₃ - U₁ - U₂ + U₀)) ((E₃ - E₁ - E₂ + E₀) * conjByUnit μ U₀)
  linarith
end
section
theorem finsetLpNorm_const_mul_le {ι : Type} {P : ℕ} (hP : 1 ≤ P) (s : Finset ι) (f : ι → ℝ) {a : ℝ}
    (ha : 0 ≤ a) : finsetLpNorm P s (fun i => a * f i) ≤ a * finsetLpNorm P s f := by
  refine finsetLpNorm_le_of_sum_pow_le hP s s _ _ ha ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul, abs_of_nonneg ha, mul_pow]
theorem weightedScaleNorm_zero_weight (D : Finset F.Cell) (p : F.Site 0) (P m : ℕ) (f : F.Site m → Fin 4 → ℝ) :
    weightedScaleNorm D p 0 P m f = finsetLpNorm P (innerBonds D m) fun b => f b.1 b.2 := by
  simp [weightedScaleNorm, scaleWeight]
def contourSpread (F : BlockFrame) (C₀ s : ℝ) (m : ℕ) : ℝ :=
  C₀ * s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (m + 1))) ^ 2
theorem contourSpread_le (hodd : Odd F.blockSide) {C₀ s : ℝ} (hC : 0 ≤ C₀) (hs : 0 ≤ s) (m : ℕ) :
    contourSpread F C₀ s m ≤ C₀ * s := by
  unfold contourSpread
  refine mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by positivity) (inv_pow_le_one hodd.pos _))
theorem finsetLpNorm_contourSpread_le (hodd : Odd F.blockSide) {D : Finset F.Cell} (hD : D.card ≤ 81) {C₀ s : ℝ}
    (hC : 0 ≤ C₀) (hs : 0 ≤ s) (m : ℕ) :
    finsetLpNorm 4 (innerBonds D (m + 1)) (fun _ => contourSpread F C₀ s m) ≤ 5 * (C₀ * s) := by
  have hL : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  set M : ℝ := (F.blockSide : ℝ) ^ (F.top - (m + 1)) with hM
  have hM1 : 1 ≤ M := one_le_pow₀ hL
  have hcard : ((innerBonds D (m + 1)).card : ℝ) ≤ 324 * M ^ 4 := by
    have h1 := BlockLines.card_innerBonds_le hodd D (m + 1)
    have h2 : ((innerBonds D (m + 1)).card : ℝ) ≤
        ((4 * (D.card * (F.blockSide ^ (F.top - (m + 1))) ^ 4) : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    have h3 : (D.card : ℝ) ≤ 81 := by exact_mod_cast hD
    have h4 : (0 : ℝ) ≤ M ^ 4 := by positivity
    calc _ ≤ 4 * ((D.card : ℝ) * M ^ 4) := h2
      _ ≤ 4 * (81 * M ^ 4) := by gcongr
      _ = _ := by ring
  have e : contourSpread F C₀ s m = C₀ * s / M ^ 2 := by
    unfold contourSpread
    rw [hM, one_div, inv_pow, inv_pow]
    rfl
  have h0 : 0 ≤ contourSpread F C₀ s m := by
    unfold contourSpread
    positivity
  have h1 := finsetLpNorm_le_of_sum_pow_le (P := 4) (by norm_num) (innerBonds D (m + 1)) ({()} : Finset Unit)
    (fun _ => contourSpread F C₀ s m) (fun _ => (1 : ℝ)) (C := 5 * (C₀ * s)) (by positivity) (by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_singleton, abs_one, one_pow, mul_one]
      rw [abs_of_nonneg h0, e, div_pow, ← pow_mul]
      have h4 : (1 : ℝ) ≤ M ^ 4 := one_le_pow₀ hM1
      have e2 : M ^ (2 * 4) = M ^ 4 * M ^ 4 := by
        rw [← pow_add]
      rw [e2]
      have h5 : ((innerBonds D (m + 1)).card : ℝ) * ((C₀ * s) ^ 4 / (M ^ 4 * M ^ 4)) ≤
          324 * M ^ 4 * ((C₀ * s) ^ 4 / (M ^ 4 * M ^ 4)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      have e3 : 324 * M ^ 4 * ((C₀ * s) ^ 4 / (M ^ 4 * M ^ 4)) = 324 * (C₀ * s) ^ 4 / M ^ 4 := by
        field_simp
      have h6 : 324 * (C₀ * s) ^ 4 / M ^ 4 ≤ 324 * (C₀ * s) ^ 4 := div_le_self (by positivity) h4
      have h7 : (0 : ℝ) ≤ (C₀ * s) ^ 4 := by positivity
      have e4 : (5 * (C₀ * s)) ^ 4 = 625 * (C₀ * s) ^ 4 := by ring
      rw [e4]
      have c1 : ((({()} : Finset Unit).card : ℕ) : ℝ) = 1 := by simp
      rw [c1, mul_one]
      linarith)
  have h2 : finsetLpNorm 4 ({()} : Finset Unit) (fun _ => (1 : ℝ)) = 1 := by
    simp [finsetLpNorm]
  rw [h2, mul_one] at h1
  exact h1
structure DeviationBall (R : F.FieldChain) (D : Finset F.Cell) (W : ComplexChainChart F) (η B : ℝ) : Prop where
  norm_deviation_le : ∀ m, m < F.top → ∀ b ∈ innerBonds D m, ‖levelDeviation R W m b.1 b.2‖ ≤ η
  lpNorm_deviation_le : ∀ m, m < F.top →
    finsetLpNorm 4 (innerBonds D m) (fun b => ‖levelDeviation R W m b.1 b.2‖) ≤ B
  norm_source_sub_one_le : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1), ‖levelSource W m c.1 c.2 - 1‖ ≤ η
  lpNorm_source_sub_one_le : ∀ m, m + 1 < F.top →
    finsetLpNorm 4 (innerBonds D (m + 1)) (fun c => ‖levelSource W m c.1 c.2 - 1‖) ≤ B
theorem DeviationBall.bondHullNorm_le {R : F.FieldChain} {D : Finset F.Cell} {W : ComplexChainChart F} {η B : ℝ}
    (h : DeviationBall R D W η B) (hodd : Odd F.blockSide) (hη : 0 ≤ η) {m : ℕ} (hm : m < F.top)
    {c : F.Site (m + 1) × Fin 4} (hc : c ∈ innerBonds D (m + 1)) :
    bondHullNorm c (levelDeviation R W m) ≤ hullBondCount F.blockSide * η :=
  bondHullSum_le hodd hη (holdsOnHull_of_innerBonds hm hodd hc (Q := fun x i => ‖levelDeviation R W m x i‖ ≤ η)
    (fun b hb => h.norm_deviation_le m hm b hb))
theorem DeviationBall.det_eq_one {R : F.FieldChain} {D : Finset F.Cell} {W : ComplexChainChart F} {η B : ℝ}
    (h : DeviationBall R D W η B) (hodd : Odd F.blockSide) (hη : η < 1) {m : ℕ} (hm : m < F.top)
    {c : F.Site (m + 1) × Fin 4} (hc : c ∈ innerBonds D (m + 1)) :
    HoldsOnHull c (fun b i => (complexChartField R W m b i).det = 1) :=
  holdsOnHull_of_innerBonds hm hodd hc (fun b hb =>
    det_complexChartField_of_norm_lt_one R W m _ _ (lt_of_le_of_lt (h.norm_deviation_le m hm b hb) hη))
def firstDiffFactor (L : ℕ) (C₀ s B : ℝ) : ℝ :=
  B + 24 * (200000 * (L : ℝ) ^ 2) * (2 * (hullFactor L * B) + 5 * (C₀ * s))
set_option maxHeartbeats 1000000 in
theorem weightedScaleNorm_first_diff_le (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide) {D : Finset F.Cell}
    (hD : D.card ≤ 81) (p : F.Site 0) {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {W W' : ComplexChainChart F}
    {C₀ s η B S : ℝ} (hC : 0 < C₀) (hs : 0 < s) (hnear : ContoursNearUnit R D C₀ s) (hb : DeviationBall R D W η B)
    (hb' : DeviationBall R D W' η B) (hη0 : 0 ≤ η) (hη1 : η < 1) (hB0 : 0 ≤ B) (hS0 : 0 ≤ S)
    (hσ : C₀ * s ≤ 1 / 64) (hsm : 3 * (2 * (hullBondCount F.blockSide * η) + C₀ * s) < hullBallRadius F.blockSide)
    (hfac : 568 * firstDiffFactor F.blockSide C₀ s B * hullFactor F.blockSide ≤ 1)
    (hS : ∀ m, m + 1 < F.top → weightedScaleNorm D p θ 2 (m + 1)
      (fun y d => 2 * ‖levelSource W' m y d - levelSource W m y d‖) ≤ S) (m : ℕ) (hm : m < F.top) :
    weightedScaleNorm D p θ 4 m (fun z d => ‖(levelDeviation R W' m - levelDeviation R W m) z d‖) ≤
      2 * (20000 * weightedScaleNorm D p θ 4 0
        (fun z d => ‖(levelDeviation R W' 0 - levelDeviation R W 0) z d‖) + 284 * S) := by
  have hL : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  set K := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hH0 : 0 ≤ hullBondCount F.blockSide := by
    unfold hullBondCount
    positivity
  have hKH0 : 0 ≤ hullFactor F.blockSide := by
    unfold hullFactor
    positivity
  set a : (m : ℕ) → F.Site m → Fin 4 → ℝ := fun m z d => ‖(levelDeviation R W' m - levelDeviation R W m) z d‖
    with ha
  set b : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ :=
    fun m y d => 2 * ‖levelSource W' m y d - levelSource W m y d‖ with hbd
  set e : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ := fun m y d => ‖levelSource W m y d - 1‖ + 24 * K *
    (bondHullNorm (y, d) (levelDeviation R W m) + bondHullNorm (y, d) (levelDeviation R W' m) +
      contourSpread F C₀ s m) with he
  have ha0 : ∀ m z d, 0 ≤ a m z d := fun _ _ _ => norm_nonneg _
  have hb0 : ∀ m y d, 0 ≤ b m y d := fun _ _ _ => by
    simp only [hbd]
    positivity
  have he0 : ∀ m y d, 0 ≤ e m y d := by
    intro m y d
    have h1 : 0 ≤ bondHullNorm (y, d) (levelDeviation R W m) := bondHullSum_nonneg _ fun _ _ => norm_nonneg _
    have h3 : 0 ≤ bondHullNorm (y, d) (levelDeviation R W' m) := bondHullSum_nonneg _ fun _ _ => norm_nonneg _
    have h4 : 0 ≤ contourSpread F C₀ s m := by
      unfold contourSpread
      positivity
    exact add_nonneg (norm_nonneg _) (mul_nonneg (by positivity) (add_nonneg (add_nonneg h1 h3) h4))
  have hrec : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1),
      a (m + 1) c.1 c.2 ≤ lineBlockAverage (a m) c + (b m c.1 c.2 + e m c.1 c.2 * bondHullSum c (a m)) := by
    intro m hm c hc
    have hm' : m < F.top := by omega
    set σ := contourSpread F C₀ s m with hσd
    have hσ0 : 0 < σ := by
      unfold contourSpread at hσd
      rw [hσd]
      have : (0 : ℝ) < F.blockSide := by linarith
      positivity
    have hσle : σ ≤ C₀ * s := contourSpread_le hodd hC.le hs.le m
    set t := bondHullNorm c (levelDeviation R W m) + bondHullNorm c (levelDeviation R W' m) with ht
    have hn1 : 0 ≤ bondHullNorm c (levelDeviation R W m) := bondHullSum_nonneg _ fun _ _ => norm_nonneg _
    have hn2 : 0 ≤ bondHullNorm c (levelDeviation R W' m) := bondHullSum_nonneg _ fun _ _ => norm_nonneg _
    have hn1' := hb.bondHullNorm_le hodd hη0 hm' hc
    have hn2' := hb'.bondHullNorm_le hodd hη0 hm' hc
    have ht0 : 0 ≤ t := add_nonneg hn1 hn2
    have hsm' : 3 * (t + σ) < hullBallRadius F.blockSide := by linarith
    have hle1 : bondHullNorm c (levelDeviation R W m) ≤ t := by linarith
    have hle2 : bondHullNorm c (levelDeviation R W' m) ≤ t := by linarith
    have hσ64 : σ ≤ 1 / 64 := by linarith
    exact norm_levelDeviation_succ_sub_le hodd (by omega : m + 1 ≤ F.top) R W W' (t := t) hσ0 hσ64
      (hnear m (by omega) c hc) ht0 hsm' hle1 hle2
      (hb.det_eq_one hodd hη1 hm' hc) (hb'.det_eq_one hodd hη1 hm' hc)
      ((hb.norm_source_sub_one_le m hm c hc).trans hη1.le)
  have hε0 : 0 ≤ firstDiffFactor F.blockSide C₀ s B := by
    unfold firstDiffFactor
    positivity
  have hε : ∀ m, m + 1 < F.top →
      finsetLpNorm 4 (innerBonds D (m + 1)) (fun c => e m c.1 c.2) ≤ firstDiffFactor F.blockSide C₀ s B := by
    intro m hm
    have hm' : m < F.top := by omega
    have hN : ∀ {W₁ : ComplexChainChart F}, DeviationBall R D W₁ η B →
        finsetLpNorm 4 (innerBonds D (m + 1)) (fun c => bondHullNorm (c.1, c.2) (levelDeviation R W₁ m)) ≤
          hullFactor F.blockSide * B := by
      intro W₁ hW
      have h1 := weightedScaleNorm_bondHullSum_le (D := D) hodd (θ := 0) (by norm_num) hm' p 4 (by norm_num)
        (g := fun x i => ‖levelDeviation R W₁ m x i‖) (fun _ _ => norm_nonneg _)
      rw [weightedScaleNorm_zero_weight, weightedScaleNorm_zero_weight] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (hW.lpNorm_deviation_le m hm') hKH0)
    have a1 := hb.lpNorm_source_sub_one_le m hm
    have a2 := finsetLpNorm_add_le (P := 4) (by norm_num) (innerBonds D (m + 1))
      (fun c => ‖levelSource W m c.1 c.2 - 1‖)
      (fun c => 24 * K * (bondHullNorm (c.1, c.2) (levelDeviation R W m) +
        bondHullNorm (c.1, c.2) (levelDeviation R W' m) + contourSpread F C₀ s m))
    have a3 := finsetLpNorm_const_mul_le (P := 4) (by norm_num) (innerBonds D (m + 1))
      (fun c : F.Site (m + 1) × Fin 4 => bondHullNorm (c.1, c.2) (levelDeviation R W m) +
        bondHullNorm (c.1, c.2) (levelDeviation R W' m) + contourSpread F C₀ s m) (a := 24 * K) (by positivity)
    have a4 := finsetLpNorm_add_le (P := 4) (by norm_num) (innerBonds D (m + 1))
      (fun c : F.Site (m + 1) × Fin 4 => bondHullNorm (c.1, c.2) (levelDeviation R W m) +
        bondHullNorm (c.1, c.2) (levelDeviation R W' m))
      (fun _ => contourSpread F C₀ s m)
    have a5 := finsetLpNorm_add_le (P := 4) (by norm_num) (innerBonds D (m + 1))
      (fun c : F.Site (m + 1) × Fin 4 => bondHullNorm (c.1, c.2) (levelDeviation R W m))
      (fun c => bondHullNorm (c.1, c.2) (levelDeviation R W' m))
    have a6 := finsetLpNorm_contourSpread_le hodd hD hC.le hs.le m
    have a7 := hN hb
    have a8 := hN hb'
    have a9 : 24 * K * finsetLpNorm 4 (innerBonds D (m + 1)) (fun c : F.Site (m + 1) × Fin 4 =>
        bondHullNorm (c.1, c.2) (levelDeviation R W m) + bondHullNorm (c.1, c.2) (levelDeviation R W' m) +
          contourSpread F C₀ s m) ≤
        24 * K * (2 * (hullFactor F.blockSide * B) + 5 * (C₀ * s)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    unfold firstDiffFactor
    rw [← hK]
    show finsetLpNorm 4 (innerBonds D (m + 1)) (fun c => ‖levelSource W m c.1 c.2 - 1‖ + 24 * K *
      (bondHullNorm (c.1, c.2) (levelDeviation R W m) + bondHullNorm (c.1, c.2) (levelDeviation R W' m) +
        contourSpread F C₀ s m)) ≤ _
    linarith
  exact weightedScaleNorm_four_le_of_small hodd h2 D p hθ a b e ha0 hb0 he0 hrec hε0 hS0 hε hS hfac m hm
end
section
def secondDiffSource (R : F.FieldChain) (W₀ W₁ W₂ W₃ : ComplexChainChart F) (m : ℕ) (y : F.Site (m + 1))
    (d : Fin 4) : ℝ :=
  128 * (200000 * (F.blockSide : ℝ) ^ 2) * bondHullNorm (y, d) (levelDeviation R W₁ m - levelDeviation R W₀ m) *
      bondHullNorm (y, d) (levelDeviation R W₂ m - levelDeviation R W₀ m) +
    6 * ‖levelSource W₃ m y d - levelSource W₁ m y d - levelSource W₂ m y d + levelSource W₀ m y d‖ +
    2 * ‖levelSource W₁ m y d - levelSource W₀ m y d‖ *
      bondHullNorm (y, d) (levelDeviation R W₂ m - levelDeviation R W₀ m) +
    2 * ‖levelSource W₂ m y d - levelSource W₀ m y d‖ *
      bondHullNorm (y, d) (levelDeviation R W₁ m - levelDeviation R W₀ m)
def secondDiffFactor (L : ℕ) (C₀ s η : ℝ) : ℝ :=
  9 * η + 24 * (200000 * (L : ℝ) ^ 2) * (6 * (hullBondCount L * η) + C₀ * s)
set_option maxHeartbeats 1000000 in
theorem weightedScaleNorm_second_diff_le (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide) {D : Finset F.Cell}
    (p : F.Site 0) {R : F.FieldChain} {W₀ W₁ W₂ W₃ : ComplexChainChart F} {C₀ s η B S : ℝ} (hC : 0 < C₀)
    (hs : 0 < s) (hnear : ContoursNearUnit R D C₀ s) (hb₀ : DeviationBall R D W₀ η B)
    (hb₁ : DeviationBall R D W₁ η B) (hb₂ : DeviationBall R D W₂ η B) (hb₃ : DeviationBall R D W₃ η B)
    (hη0 : 0 ≤ η) (hη1 : 9 * η ≤ 1) (hS0 : 0 ≤ S) (hσ : C₀ * s ≤ 1 / 64)
    (hsm : 24 * (6 * (hullBondCount F.blockSide * η) + C₀ * s) < hullBallRadius F.blockSide)
    (hLip : 12 * (200000 * (F.blockSide : ℝ) ^ 2) * (6 * (hullBondCount F.blockSide * η) + C₀ * s) ≤ 1)
    (ht1 : 2 * (hullBondCount F.blockSide * η) ≤ 1)
    (hfac : 568 * secondDiffFactor F.blockSide C₀ s η * hullFactor F.blockSide ≤ 1)
    (hS : ∀ m, m + 1 < F.top → weightedScaleNorm D p 0 2 (m + 1) (secondDiffSource R W₀ W₁ W₂ W₃ m) ≤ S)
    (m : ℕ) (hm : m < F.top) :
    weightedScaleNorm D p 0 2 m (fun z d => ‖(levelDeviation R W₃ m - levelDeviation R W₁ m -
        levelDeviation R W₂ m + levelDeviation R W₀ m) z d‖) ≤
      2 * (142 * weightedScaleNorm D p 0 2 0
        (fun z d => ‖(levelDeviation R W₃ 0 - levelDeviation R W₁ 0 - levelDeviation R W₂ 0 +
          levelDeviation R W₀ 0) z d‖) + 284 * S) := by
  have hL : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  set K := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hH0 : 0 ≤ hullBondCount F.blockSide := by
    unfold hullBondCount
    positivity
  have hη : η < 1 := by linarith
  set H := hullBondCount F.blockSide with hH
  set t := 2 * (H * η) with ht
  have ht0 : 0 ≤ t := mul_nonneg (by norm_num) (mul_nonneg hH0 hη0)
  set a : (m : ℕ) → F.Site m → Fin 4 → ℝ :=
    fun m z d => ‖(levelDeviation R W₃ m - levelDeviation R W₁ m - levelDeviation R W₂ m +
      levelDeviation R W₀ m) z d‖ with ha
  set b : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ := secondDiffSource R W₀ W₁ W₂ W₃ with hbd
  set e : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ := fun m y d => ‖levelSource W₀ m y d - 1‖ +
    ‖levelSource W₁ m y d - levelSource W₀ m y d‖ + ‖levelSource W₂ m y d - levelSource W₀ m y d‖ +
    ‖levelSource W₃ m y d - levelSource W₁ m y d - levelSource W₂ m y d + levelSource W₀ m y d‖ +
    2 * (12 * K * (3 * t + contourSpread F C₀ s m)) with he
  have ha0 : ∀ m z d, 0 ≤ a m z d := fun _ _ _ => norm_nonneg _
  have hb0 : ∀ m y d, 0 ≤ b m y d := by
    intro m y d
    have h1 : 0 ≤ bondHullNorm (y, d) (levelDeviation R W₁ m - levelDeviation R W₀ m) :=
      bondHullSum_nonneg _ fun _ _ => norm_nonneg _
    have h3 : 0 ≤ bondHullNorm (y, d) (levelDeviation R W₂ m - levelDeviation R W₀ m) :=
      bondHullSum_nonneg _ fun _ _ => norm_nonneg _
    simp only [hbd, secondDiffSource]
    exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by positivity) h1) h3) (by positivity))
      (mul_nonneg (by positivity) h3)) (mul_nonneg (by positivity) h1)
  have he0 : ∀ m y d, 0 ≤ e m y d := by
    intro m y d
    have h4 : 0 ≤ contourSpread F C₀ s m := by
      unfold contourSpread
      positivity
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))
      (norm_nonneg _)) (mul_nonneg (by norm_num) (mul_nonneg (by positivity) (add_nonneg (by positivity) h4)))
  have hsrc : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1),
      ‖levelSource W₀ m c.1 c.2 - 1‖ ≤ η ∧ ‖levelSource W₁ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ ≤ 2 * η ∧
      ‖levelSource W₂ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ ≤ 2 * η ∧
      ‖levelSource W₃ m c.1 c.2 - levelSource W₁ m c.1 c.2 - levelSource W₂ m c.1 c.2 +
        levelSource W₀ m c.1 c.2‖ ≤ 4 * η := by
    intro m hm c hc
    have a0 := hb₀.norm_source_sub_one_le m hm c hc
    have a1 := hb₁.norm_source_sub_one_le m hm c hc
    have a2 := hb₂.norm_source_sub_one_le m hm c hc
    have a3 := hb₃.norm_source_sub_one_le m hm c hc
    set E₀ := levelSource W₀ m c.1 c.2
    set E₁ := levelSource W₁ m c.1 c.2
    set E₂ := levelSource W₂ m c.1 c.2
    set E₃ := levelSource W₃ m c.1 c.2
    have d1 : ‖E₁ - E₀‖ ≤ 2 * η := by
      have : E₁ - E₀ = (E₁ - 1) - (E₀ - 1) := by abel
      rw [this]
      exact (norm_sub_le _ _).trans (by linarith)
    have d2 : ‖E₂ - E₀‖ ≤ 2 * η := by
      have : E₂ - E₀ = (E₂ - 1) - (E₀ - 1) := by abel
      rw [this]
      exact (norm_sub_le _ _).trans (by linarith)
    have d3 : ‖E₃ - E₁ - E₂ + E₀‖ ≤ 4 * η := by
      have : E₃ - E₁ - E₂ + E₀ = (E₃ - 1) - (E₁ - 1) - (E₂ - 1) + (E₀ - 1) := by abel
      rw [this]
      have u1 := norm_add_le ((E₃ - 1) - (E₁ - 1) - (E₂ - 1)) (E₀ - 1)
      have u2 := norm_sub_le ((E₃ - 1) - (E₁ - 1)) (E₂ - 1)
      have u3 := norm_sub_le (E₃ - 1) (E₁ - 1)
      linarith
    exact ⟨a0, d1, d2, d3⟩
  have hrec : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1),
      a (m + 1) c.1 c.2 ≤ lineBlockAverage (a m) c + (b m c.1 c.2 + e m c.1 c.2 * bondHullSum c (a m)) := by
    intro m hm c hc
    have hm' : m < F.top := by omega
    set σ := contourSpread F C₀ s m with hσd
    have hσ0 : 0 < σ := by
      unfold contourSpread at hσd
      rw [hσd]
      have : (0 : ℝ) < F.blockSide := by linarith
      positivity
    have hσle : σ ≤ C₀ * s := contourSpread_le hodd hC.le hs.le m
    have e3t : 3 * t = 6 * (H * η) := by
      rw [ht]
      ring
    have hN : ∀ {W : ComplexChainChart F}, DeviationBall R D W η B → bondHullNorm c (levelDeviation R W m) ≤ t := by
      intro W hW
      have := hW.bondHullNorm_le hodd hη0 hm' hc
      rw [ht]
      linarith
    have hdiff : ∀ {W W' : ComplexChainChart F}, DeviationBall R D W η B → DeviationBall R D W' η B →
        bondHullNorm c (levelDeviation R W' m - levelDeviation R W m) ≤ t := by
      intro W W' hW hW'
      have h7 : HoldsOnHull c (fun x i => ‖(levelDeviation R W' m - levelDeviation R W m) x i‖ ≤ 2 * η) :=
        holdsOnHull_of_innerBonds hm' hodd hc (fun b hb => by
          have q1 := hW.norm_deviation_le m hm' b hb
          have q2 := hW'.norm_deviation_le m hm' b hb
          have q3 := norm_sub_le (levelDeviation R W' m b.1 b.2) (levelDeviation R W m b.1 b.2)
          show ‖levelDeviation R W' m b.1 b.2 - levelDeviation R W m b.1 b.2‖ ≤ 2 * η
          linarith)
      have := bondHullSum_le hodd (mul_nonneg (by norm_num) hη0) h7
      rw [ht]
      refine this.trans (le_of_eq ?_)
      ring
    obtain ⟨q0, q1, q2, q3⟩ := hsrc m hm c hc
    have hstep := norm_levelDeviation_succ_second_diff_le hodd (by omega : m + 1 ≤ F.top) R W₀ W₁ W₂ W₃ (t := t)
      hσ0 (by linarith) (hnear m (by omega) c hc) ht0 (by rw [e3t]; linarith) (by
        rw [e3t]
        have : 12 * (200000 * (F.blockSide : ℝ) ^ 2) * (6 * (H * η) + σ) ≤
            12 * (200000 * (F.blockSide : ℝ) ^ 2) * (6 * (H * η) + C₀ * s) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith)
      (hN hb₀) (hN hb₁) (hN hb₂) (hN hb₃) (hdiff hb₀ hb₁) (hdiff hb₀ hb₂)
      ((hdiff hb₀ hb₁).trans ht1) ((hdiff hb₀ hb₂).trans ht1)
      (hb₀.det_eq_one hodd hη hm' hc) (hb₁.det_eq_one hodd hη hm' hc) (hb₂.det_eq_one hodd hη hm' hc)
      (hb₃.det_eq_one hodd hη hm' hc)
      (by linarith)
    exact hstep
  have hε0 : 0 ≤ secondDiffFactor F.blockSide C₀ s η := by
    unfold secondDiffFactor
    have h8 : 0 ≤ 6 * (hullBondCount F.blockSide * η) + C₀ * s :=
      add_nonneg (mul_nonneg (by norm_num) (mul_nonneg hH0 hη0)) (by positivity)
    exact add_nonneg (by positivity) (mul_nonneg (by positivity) h8)
  have hε : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1), e m c.1 c.2 ≤ secondDiffFactor F.blockSide C₀ s η := by
    intro m hm c hc
    obtain ⟨q0, q1, q2, q3⟩ := hsrc m hm c hc
    have hσle := contourSpread_le (F := F) hodd hC.le hs.le m
    have h5 : 2 * (12 * K * (3 * t + contourSpread F C₀ s m)) ≤ 24 * K * (6 * (H * η) + C₀ * s) := by
      have e3t : 3 * t = 6 * (H * η) := by
        rw [ht]
        ring
      rw [e3t]
      have : 24 * K * (6 * (H * η) + contourSpread F C₀ s m) ≤ 24 * K * (6 * (H * η) + C₀ * s) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    show ‖levelSource W₀ m c.1 c.2 - 1‖ + ‖levelSource W₁ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ +
      ‖levelSource W₂ m c.1 c.2 - levelSource W₀ m c.1 c.2‖ +
      ‖levelSource W₃ m c.1 c.2 - levelSource W₁ m c.1 c.2 - levelSource W₂ m c.1 c.2 + levelSource W₀ m c.1 c.2‖ +
      2 * (12 * K * (3 * t + contourSpread F C₀ s m)) ≤ secondDiffFactor F.blockSide C₀ s η
    unfold secondDiffFactor
    rw [← hK, ← hH]
    linarith
  exact weightedScaleNorm_two_le_of_small hodd h2 D p (θ := 0) (by norm_num) a b e ha0 hb0 he0 hrec hε0 hS0 hε hS
    hfac m hm
end
end YangMills.Construction.ComplexDifferences
end
