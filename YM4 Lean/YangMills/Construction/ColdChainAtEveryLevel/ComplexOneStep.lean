import YangMills.Construction.ColdChainAtEveryLevel.ComplexContours
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction
namespace ComplexChainStep
open BlockAverages ComplexContours ComplexifiedQuaternions LatticePaths LatticeFractionalIntegration
variable {F : BlockFrame} {j : ℕ}
theorem norm_relativeHolonomy_sub_one_le_of_length_le {X : F.ComplexField j} {R : F.GaugeField j} {t : ℝ}
    (ht : 0 ≤ t) {x : F.Site j} {l : List PathStep}
    (h : PathNearReal X R t x l) {m : ℕ} (hl : l.length ≤ m) (hm : 2 * (m : ℝ) * t ≤ 1) :
    ‖relativeHolonomy X R x l - 1‖ ≤ 2 * (m : ℝ) * t := by
  have h1 := norm_relativeHolonomy_sub_one_le ht h
  have h2 : (1 + t) ^ l.length ≤ (1 + t) ^ m := pow_le_pow_right₀ (by linarith) hl
  have h3 := one_add_pow_sub_one_le_two_mul ht m hm
  linarith
def conjAdjugate (w : UnitQuaternion) : ComplexQuat →ₗ[ℂ] ComplexQuat where
  toFun e := conjByUnit w (Matrix.adjugate e)
  map_add' a b := by rw [adjugate_map_add, conjByUnit_add]
  map_smul' z a := by rw [adjugate_map_smul, conjByUnit_smul]; rfl
def mulRightLinear (b : ComplexQuat) : ComplexQuat →ₗ[ℂ] ComplexQuat := LinearMap.mulRight ℂ b
theorem blockContourMean_mul_right (b : ComplexQuat) (f : Lattice4 → Equiv.Perm (Fin 4) → ComplexQuat) :
    blockContourMean F f * b = blockContourMean F (fun h π => f h π * b) :=
  map_blockContourMean (mulRightLinear b) f
theorem norm_trace_le_sq_of_det_one_add {A : ComplexQuat} {τ : ℝ} (hA : ‖A‖ ≤ τ)
    (hd : ((1 : ComplexQuat) + A).det = 1) : ‖A.trace‖ ≤ τ ^ 2 := by
  have h1 := det_one_add A
  rw [hd] at h1
  have h2 : A.trace = - A.det := by
    have : A.trace + A.det = 0 := by
      have := h1.symm
      simpa using this
    exact eq_neg_of_add_eq_zero_left this
  rw [h2, norm_neg]
  refine (norm_det_le A).trans ?_
  have := norm_nonneg A
  gcongr
theorem norm_gaugedAverage_mul_sub_le (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    {X : F.ComplexField j} {R : F.GaugeField j} {t σ : ℝ}
    {c : F.Site (j + 1) × Fin 4} (ht : 0 ≤ t) (hσ : σ ≤ 1 / 8) (hτ : 4 * (F.blockSide : ℝ) * t ≤ 1 / 32)
    (hg : ContoursNearReal X R t σ c) :
    ‖complexGaugedContourAverage X (complexBalancingGauge X R) c * ofUnit (polarUnit (contourAverage R c))⁻¹ -
        ((‖contourAverage R c‖ : ℝ) : ℂ) • (1 : ComplexQuat) - transportedAverage R (linkDeviation X R) c‖ ≤
      205 * (4 * (F.blockSide : ℝ) * t) ^ 2 + 9 * σ * (4 * (F.blockSide : ℝ) * t) := by
  set τ : ℝ := 4 * (F.blockSide : ℝ) * t with hτd
  set w : UnitQuaternion := polarUnit (contourAverage R c) with hw
  set r : ℝ := ‖contourAverage R c‖ with hr
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hτ0 : 0 ≤ τ := by positivity
  have hm2 : 2 * ((2 * F.blockSide : ℕ) : ℝ) * t ≤ 1 := by
    push_cast
    nlinarith
  have hm1 : 2 * ((F.blockSide : ℕ) : ℝ) * t ≤ 1 := by nlinarith
  set x0 := refineSite c.1 with hx0
  set x0' := refineSite (c.1 + unitStep (j + 1) c.2) with hx0'
  let T : Lattice4 → Equiv.Perm (Fin 4) → UnitQuaternion := fun h π => pathHolonomy R x0 (axisPath h π)
  let A : Lattice4 → Equiv.Perm (Fin 4) → ComplexQuat := fun h π => relativeHolonomy X R x0 (axisPath h π) - 1
  let B : Lattice4 → Equiv.Perm (Fin 4) → ComplexQuat := fun h π =>
    conjByUnit (T h π) (relativeHolonomy X R (x0 + siteOfCoords j h) (List.replicate F.blockSide (c.2, true))) - 1
  let η : Lattice4 → Equiv.Perm (Fin 4) → ComplexQuat := fun h π =>
    ofUnit (pathHolonomy R x0 (bondContour F.blockSide h π c.2) * w⁻¹) - 1
  let Y' : Lattice4 → Equiv.Perm (Fin 4) → ComplexQuat := fun h π => relativeHolonomy X R x0' (axisPath h π)
  let D : Lattice4 → Equiv.Perm (Fin 4) → ComplexQuat := fun h π => conjAdjugate w (Y' h π) - 1
  have hA : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖A h π‖ ≤ τ := fun h hh π => by
    have := norm_relativeHolonomy_sub_one_le_of_length_le ht (hg.nearLegs h hh π)
      (length_axisPath_le F.blockSide h hh π) hm2
    refine this.trans (le_of_eq ?_)
    push_cast
    ring
  have hY' : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖Y' h π - 1‖ ≤ τ := fun h hh π => by
    have := norm_relativeHolonomy_sub_one_le_of_length_le ht (hg.nearFarLegs h hh π)
      (length_axisPath_le F.blockSide h hh π) hm2
    refine this.trans (le_of_eq ?_)
    push_cast
    ring
  have hB : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖B h π‖ ≤ τ := fun h hh π => by
    have h1 := norm_relativeHolonomy_sub_one_le_of_length_le (m := F.blockSide) ht (hg.nearLine h hh)
      (by simp) hm1
    have h2 : B h π = conjByUnit (T h π)
        (relativeHolonomy X R (x0 + siteOfCoords j h) (List.replicate F.blockSide (c.2, true)) - 1) := by
      simp only [B, conjByUnit_sub, conjByUnit_one]
    rw [h2, norm_conjByUnit]
    nlinarith
  have hD : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖D h π‖ ≤ τ := fun h hh π => by
    have h2 : D h π = conjAdjugate w (Y' h π - 1) := by
      have : conjAdjugate w 1 = 1 := by
        show conjByUnit w (Matrix.adjugate 1) = 1
        rw [adjugate_one_complexQuat, conjByUnit_one]
      simp only [D, map_sub, this]
    rw [h2]
    show ‖conjByUnit w (Matrix.adjugate (Y' h π - 1))‖ ≤ τ
    rw [norm_conjByUnit, norm_adjugate]
    exact hY' h hh π
  have hη : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖η h π‖ ≤ σ := fun h hh π => hg.realNearAverage h hh π
  have hterm : ∀ h π, complexPathHolonomy X x0 (bondContour F.blockSide h π c.2) * ofUnit w⁻¹ =
      (1 + A h π) * (1 + B h π) * (1 + η h π) * (1 + D h π) := fun h π => by
    simp only [A, B, η, D, Y', add_sub_cancel]
    exact complexPathHolonomy_bondContour_mul_inv hj X R c h π w
  have hτ1 : τ ≤ 1 := by linarith
  set a := complexRelativePathAverage X R c.1 - 1 with ha
  set a' := complexRelativePathAverage X R (c.1 + unitStep (j + 1) c.2) - 1 with ha'
  have hmA : blockContourMean F A = a := by
    simp only [A]
    rw [blockContourMean_sub, blockContourMean_const hodd]
    rfl
  have hmY : blockContourMean F Y' = 1 + a' := by
    rw [ha', add_sub_cancel]
    rfl
  have hmD : blockContourMean F D = conjByUnit w (Matrix.adjugate a') := by
    simp only [D]
    rw [blockContourMean_sub, blockContourMean_const hodd, ← map_blockContourMean, hmY]
    show conjByUnit w (Matrix.adjugate (1 + a')) - 1 = _
    rw [adjugate_map_add, adjugate_one_complexQuat, conjByUnit_add, conjByUnit_one, add_sub_cancel_left]
  set Qb := blockContourMean F B with hQb
  have hm1η : blockContourMean F (fun h π => 1 + η h π) = ((r : ℝ) : ℂ) • (1 : ComplexQuat) := by
    have h1 : (fun h π => 1 + η h π) = fun h π =>
        complexPathHolonomy (complexifyField R) x0 (bondContour F.blockSide h π c.2) * ofUnit w⁻¹ := by
      funext h π
      simp only [η, add_sub_cancel, complexPathHolonomy_complexify, ofUnit_mul]
    rw [h1, ← blockContourMean_mul_right]
    have h2 : blockContourMean F (fun h π =>
        complexPathHolonomy (complexifyField R) x0 (bondContour F.blockSide h π c.2)) =
        ofQuat (contourAverage R c) := complexContourAverage_complexify R c
    rw [h2]
    exact ofQuat_mul_ofUnit_polarUnit_inv _
  set W := complexContourAverage X c * ofUnit w⁻¹ -
    (((r : ℝ) : ℂ) • (1 : ComplexQuat) + a + Qb + conjByUnit w (Matrix.adjugate a')) with hW
  have hWn : ‖W‖ ≤ 4 * τ ^ 2 + 7 * σ * τ := by
    have h1 : W = blockContourMean F (fun h π =>
        complexPathHolonomy X x0 (bondContour F.blockSide h π c.2) * ofUnit w⁻¹ -
        (1 + η h π + A h π + B h π + D h π)) := by
      rw [blockContourMean_sub, blockContourMean_add, blockContourMean_add, blockContourMean_add, hm1η, hmA, hmD,
        ← blockContourMean_mul_right]
      rfl
    rw [h1]
    refine norm_blockContourMean_le hodd fun h hh π => ?_
    rw [hterm]
    exact norm_four_factor_sub_le _ _ _ _ hτ1 (hA h hh π) (hB h hh π) (hη h hh π) (hD h hh π)
  have hta : ‖a.trace‖ ≤ τ ^ 2 := by
    have h1 : a.trace = blockContourMean F (fun h π => (A h π).trace) := by
      rw [← hmA]
      exact map_blockContourMean (Matrix.traceLinearMap (Fin 2) ℂ ℂ) A
    rw [h1]
    refine norm_blockContourMean_le hodd fun h hh π => norm_trace_le_sq_of_det_one_add (hA h hh π) ?_
    simp only [A, add_sub_cancel]
    exact det_relativeHolonomy (hg.nearLegs h hh π)
  have hmA' : blockContourMean F (fun h π => Y' h π - 1) = a' := by
    rw [blockContourMean_sub, blockContourMean_const hodd]
    rfl
  have hta' : ‖a'.trace‖ ≤ τ ^ 2 := by
    have h1 : a'.trace = blockContourMean F (fun h π => (Y' h π - 1).trace) := by
      rw [← hmA']
      exact map_blockContourMean (Matrix.traceLinearMap (Fin 2) ℂ ℂ) _
    rw [h1]
    refine norm_blockContourMean_le hodd fun h hh π => norm_trace_le_sq_of_det_one_add (hY' h hh π) ?_
    simp only [add_sub_cancel]
    exact det_relativeHolonomy (hg.nearFarLegs h hh π)
  have han : ‖a‖ ≤ τ := by
    rw [← hmA]
    exact norm_blockContourMean_le hodd hA
  have han' : ‖a'‖ ≤ τ := by
    rw [← hmA']
    exact norm_blockContourMean_le hodd hY'
  have hQn : ‖Qb‖ ≤ τ := norm_blockContourMean_le hodd hB
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : |r - 1| ≤ σ := by
    have h1 : ((r : ℝ) : ℂ) • (1 : ComplexQuat) - 1 = blockContourMean F η := by
      rw [← hm1η, blockContourMean_add, blockContourMean_const hodd, add_sub_cancel_left]
    have h2 : ‖((r : ℝ) : ℂ) • (1 : ComplexQuat) - 1‖ ≤ σ := by
      rw [h1]
      exact norm_blockContourMean_le hodd hη
    have h3 : ((r : ℝ) : ℂ) • (1 : ComplexQuat) - 1 = ((r - 1 : ℝ) : ℂ) • (1 : ComplexQuat) := by
      push_cast
      rw [sub_smul, one_smul]
    rw [h3, norm_smul, CStarRing.norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs] at h2
    exact h2
  have hω : 4 * τ ^ 2 + 7 * σ * τ ≤ τ := by nlinarith
  have hZ : complexGaugedContourAverage X (complexBalancingGauge X R) c * ofUnit w⁻¹ =
      Matrix.adjugate (unitPart (1 + a)) *
        (((r : ℝ) : ℂ) • (1 : ComplexQuat) + a + Qb + conjByUnit w (Matrix.adjugate a') + W) *
        conjByUnit w (unitPart (1 + a')) := by
    have e1 : ((r : ℝ) : ℂ) • (1 : ComplexQuat) + a + Qb + conjByUnit w (Matrix.adjugate a') + W =
        complexContourAverage X c * ofUnit w⁻¹ := by
      rw [hW]
      abel
    have e2 : (1 : ComplexQuat) + a = complexRelativePathAverage X R c.1 := by rw [ha, add_sub_cancel]
    have e3 : (1 : ComplexQuat) + a' = complexRelativePathAverage X R (c.1 + unitStep (j + 1) c.2) := by
      rw [ha', add_sub_cancel]
    rw [e1, e2, e3]
    simp only [complexGaugedContourAverage, complexBalancingGauge, adjugate_adjugate_eq_self, conjByUnit,
      mul_assoc, ofUnit_inv_mul_cancel_left]
  have hmain := norm_sandwich_sub_le a a' Qb W w (r := r) (σ := σ) (by linarith) han han' hQn hta hta' hr0 hr1
    (by linarith) hWn hω
  rw [← hZ] at hmain
  have hline : ‖Qb - transportedAverage R (linkDeviation X R) c‖ ≤ τ ^ 2 := by
    have h1 : Qb - transportedAverage R (linkDeviation X R) c = blockContourMean F (fun h π =>
        conjByUnit (T h π) (relativeHolonomy X R (x0 + siteOfCoords j h)
          (List.replicate F.blockSide (c.2, true)) - 1 -
          straightLineSum X R (x0 + siteOfCoords j h) c.2 F.blockSide)) := by
      rw [hQb, transportedAverage, ← blockContourMean_sub]
      congr 1
      funext h π
      have e : conjByUnit (T h π) (straightLineSum X R (x0 + siteOfCoords j h) c.2 F.blockSide) =
          ∑ r ∈ Finset.range F.blockSide,
            conjByUnit (pathHolonomy R x0 (axisPath h π ++ List.replicate r (c.2, true)))
              (linkDeviation X R (x0 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2) := by
        rw [straightLineSum, conjByUnit_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [conjByUnit_conjByUnit, pathHolonomy_append, (axisPath_spec h π).2]
      rw [conjByUnit_sub, conjByUnit_sub, conjByUnit_one, e]
    rw [h1]
    refine norm_blockContourMean_le hodd fun h hh π => ?_
    rw [norm_conjByUnit]
    refine (norm_relativeHolonomy_straight_sub_le ht c.2 F.blockSide _ (hg.nearLine h hh) hm1).trans ?_
    rw [hτd]
    have : 0 ≤ (F.blockSide : ℝ) * t := by positivity
    nlinarith
  have h9 := norm_add_le
    (complexGaugedContourAverage X (complexBalancingGauge X R) c * ofUnit w⁻¹ -
      ((r : ℝ) : ℂ) • (1 : ComplexQuat) - Qb)
    (Qb - transportedAverage R (linkDeviation X R) c)
  have h10 : (complexGaugedContourAverage X (complexBalancingGauge X R) c * ofUnit w⁻¹ -
      ((r : ℝ) : ℂ) • (1 : ComplexQuat) - Qb) + (Qb - transportedAverage R (linkDeviation X R) c) =
      complexGaugedContourAverage X (complexBalancingGauge X R) c * ofUnit w⁻¹ -
        ((r : ℝ) : ℂ) • (1 : ComplexQuat) - transportedAverage R (linkDeviation X R) c := by
    abel
  rw [h10] at h9
  nlinarith
section UnitParts
theorem invSqrt_ofReal_sq_mul {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ≠ 0) :
    invSqrt (((r : ℝ) : ℂ) ^ 2 * w) = ((r⁻¹ : ℝ) : ℂ) * invSqrt w := by
  have e1 : ((r : ℝ) : ℂ) ^ 2 * w = ((r ^ 2 : ℝ) : ℂ) * w := by push_cast; ring
  rw [e1, invSqrt, Complex.log_ofReal_mul (by positivity) hw, Real.log_pow, invSqrt]
  have e2 : -(1 / 2) * (((2 : ℕ) * Real.log r : ℝ) + Complex.log w) =
      ((-Real.log r : ℝ) : ℂ) + -(1 / 2) * Complex.log w := by
    push_cast
    ring
  rw [show (((((2 : ℕ) : ℝ) * Real.log r : ℝ) : ℂ)) = (((2 : ℕ) * Real.log r : ℝ) : ℂ) from rfl, e2,
    Complex.exp_add, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hr]
theorem principalSqrt_ofReal_sq_mul {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ≠ 0) :
    principalSqrt (((r : ℝ) : ℂ) ^ 2 * w) = ((r : ℝ) : ℂ) * principalSqrt w := by
  have e1 : ((r : ℝ) : ℂ) ^ 2 * w = ((r ^ 2 : ℝ) : ℂ) * w := by push_cast; ring
  rw [e1, principalSqrt, Complex.log_ofReal_mul (by positivity) hw, Real.log_pow, principalSqrt]
  have e2 : (1 / 2) * (((2 : ℕ) * Real.log r : ℝ) + Complex.log w) =
      ((Real.log r : ℝ) : ℂ) + (1 / 2) * Complex.log w := by
    push_cast
    ring
  rw [show (((((2 : ℕ) : ℝ) * Real.log r : ℝ) : ℂ)) = (((2 : ℕ) * Real.log r : ℝ) : ℂ) from rfl, e2,
    Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]
theorem det_smul_complexQuat (r : ℂ) (q : ComplexQuat) : (r • q).det = r ^ 2 * q.det := by
  simp [Matrix.det_fin_two]
theorem unitPart_ofReal_smul {r : ℝ} (hr : 0 < r) {q : ComplexQuat} (hq : q ≠ 0) (hd : q.det ≠ 0) :
    unitPart (((r : ℝ) : ℂ) • q) = unitPart q := by
  have hrc : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h1 : ((r : ℝ) : ℂ) • q ≠ 0 := smul_ne_zero hrc hq
  rw [unitPart, if_neg h1, unitPart, if_neg hq, det_smul_complexQuat, invSqrt_ofReal_sq_mul hr hd, smul_smul]
  have : ((r⁻¹ : ℝ) : ℂ) * invSqrt q.det * ((r : ℝ) : ℂ) = invSqrt q.det := by
    push_cast
    field_simp
  rw [this]
theorem unitPart_mul_ofUnit {q : ComplexQuat} (hq : q ≠ 0) (g : UnitQuaternion) :
    unitPart (q * ofUnit g) = unitPart q * ofUnit g := by
  have h1 : q * ofUnit g ≠ 0 := by
    intro h
    apply hq
    have := congrArg (· * ofUnit g⁻¹) h
    simpa [mul_assoc, ofUnit_mul_inv] using this
  rw [unitPart, if_neg h1, unitPart, if_neg hq, Matrix.det_mul, det_ofUnit, mul_one, smul_mul_assoc]
theorem invSqrt_sq_mul {w : ℂ} (hw : w ≠ 0) : invSqrt w ^ 2 * w = 1 := by
  rw [invSqrt, ← Complex.exp_nat_mul]
  have : ((2 : ℕ) : ℂ) * (-(1 / 2) * Complex.log w) = - Complex.log w := by
    push_cast
    ring
  rw [this, Complex.exp_neg, Complex.exp_log hw]
  exact inv_mul_cancel₀ hw
theorem principalSqrt_mul_invSqrt (w : ℂ) : principalSqrt w * invSqrt w = 1 := by
  rw [principalSqrt, invSqrt, ← Complex.exp_add]
  have : 1 / 2 * Complex.log w + -(1 / 2) * Complex.log w = 0 := by ring
  rw [this, Complex.exp_zero]
theorem det_unitPart {q : ComplexQuat} (hd : q.det ≠ 0) : (unitPart q).det = 1 := by
  have hq : q ≠ 0 := by
    intro h
    rw [h] at hd
    simp at hd
  rw [unitPart, if_neg hq, det_smul_complexQuat, invSqrt_sq_mul hd]
theorem principalSqrt_det_smul_unitPart {q : ComplexQuat} (hq : q ≠ 0) :
    principalSqrt q.det • unitPart q = q := by
  rw [unitPart, if_neg hq, smul_smul, principalSqrt_mul_invSqrt, one_smul]
theorem det_one_add_ne_zero_of_norm_lt_one {e : ComplexQuat} (he : ‖e‖ < 1) :
    ((1 : ComplexQuat) + e).det ≠ 0 := by
  have h1 : IsUnit ((1 : ComplexQuat) + e) := by
    have : (1 : ComplexQuat) + e = 1 - (-e) := by abel
    rw [this]
    exact (Units.oneSub (-e) (by rwa [norm_neg])).isUnit
  have := (Matrix.isUnit_iff_isUnit_det _).1 h1
  exact this.ne_zero
theorem det_unitExp (e : ComplexQuat) : (unitExp e).det = 1 := by
  refine det_unitPart ?_
  have h : IsUnit (NormedSpace.exp e) := by
    exact NormedSpace.isUnit_exp_of_mem_ball (𝕂 := ℂ) (by
      rw [NormedSpace.expSeries_radius_eq_top ℂ ComplexQuat]
      exact edist_lt_top _ _)
  exact ((Matrix.isUnit_iff_isUnit_det _).1 h).ne_zero
end UnitParts
theorem trace_smul_complexQuat (z : ℂ) (e : ComplexQuat) : (z • e).trace = z * e.trace := by
  simp [Matrix.trace_smul]
theorem abs_norm_contourAverage_sub_one_le (hodd : Odd F.blockSide) {R : F.GaugeField j} {σ : ℝ}
    {c : F.Site (j + 1) × Fin 4}
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (contourAverage R c))⁻¹) - 1‖ ≤ σ) :
    |‖contourAverage R c‖ - 1| ≤ σ := by
  set w : UnitQuaternion := polarUnit (contourAverage R c) with hw
  set r : ℝ := ‖contourAverage R c‖ with hr
  have hm : blockContourMean F (fun h π =>
      ofUnit (pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2) * w⁻¹)) =
      ((r : ℝ) : ℂ) • (1 : ComplexQuat) := by
    have h1 : (fun h π => ofUnit (pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2) * w⁻¹)) =
        fun h π => complexPathHolonomy (complexifyField R) (refineSite c.1)
          (bondContour F.blockSide h π c.2) * ofUnit w⁻¹ := by
      funext h π
      simp only [complexPathHolonomy_complexify, ofUnit_mul]
    rw [h1, ← blockContourMean_mul_right]
    have h2 : blockContourMean F (fun h π =>
        complexPathHolonomy (complexifyField R) (refineSite c.1) (bondContour F.blockSide h π c.2)) =
        ofQuat (contourAverage R c) := complexContourAverage_complexify R c
    rw [h2]
    exact ofQuat_mul_ofUnit_polarUnit_inv _
  have h1 : ((r : ℝ) : ℂ) • (1 : ComplexQuat) - 1 = blockContourMean F (fun h π =>
      ofUnit (pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2) * w⁻¹) - 1) := by
    rw [blockContourMean_sub, blockContourMean_const hodd, hm]
  have h2 : ‖((r : ℝ) : ℂ) • (1 : ComplexQuat) - 1‖ ≤ σ := by
    rw [h1]
    exact norm_blockContourMean_le hodd href
  have h3 : ((r : ℝ) : ℂ) • (1 : ComplexQuat) - 1 = ((r - 1 : ℝ) : ℂ) • (1 : ComplexQuat) := by
    push_cast
    rw [sub_smul, one_smul]
  rw [h3, norm_smul, CStarRing.norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs] at h2
  exact h2
section NearReal
def BondNearReal (X : F.ComplexField j) (R : F.GaugeField j) (t : ℝ) (x : F.Site j) (k : Fin 4) : Prop :=
  ‖linkDeviation X R x k‖ ≤ t ∧ (X x k).det = 1
theorem pathNearReal_of_allAlong {X : F.ComplexField j} {R : F.GaugeField j} {t : ℝ} (x : F.Site j)
    {P : Lattice4 → Prop}
    (hb : ∀ v k, P v → P (v + basisVector k) → BondNearReal X R t (x + siteOfCoords j v) k)
    {l : List PathStep} {v : Lattice4}
    (hp : AllAlong P v l) : PathNearReal X R t (x + siteOfCoords j v) l := by
  induction l generalizing v with
  | nil => trivial
  | cons st r ih =>
    have hnext : P (v + FlatPairing.stepDisplacement st) := allAlong_head hp.2
    have hstep : x + siteOfCoords j v + BlockAverages.stepDisplacement j st =
        x + siteOfCoords j (v + FlatPairing.stepDisplacement st) := by
      rw [siteOfCoords_add, siteOfCoords_flatStep, add_assoc]
    refine ⟨?_, ?_⟩
    · rcases hs : st.2 with _ | _
      · have e1 : v + FlatPairing.stepDisplacement st = v - basisVector st.1 := by
          simp [FlatPairing.stepDisplacement, hs, sub_eq_add_neg]
        have e2 : crossedBond (x + siteOfCoords j v) st =
            x + siteOfCoords j (v + FlatPairing.stepDisplacement st) := by
          simp only [crossedBond, hs, Bool.false_eq_true, if_false]
          rw [e1, siteOfCoords_sub, unitStep_eq]
          abel
        have := hb (v + FlatPairing.stepDisplacement st) st.1 hnext (by
          rw [e1, sub_add_cancel]
          exact hp.1)
        rw [StepNearReal, e2]
        exact this
      · have e1 : v + FlatPairing.stepDisplacement st = v + basisVector st.1 := by
          simp [FlatPairing.stepDisplacement, hs]
        have e2 : crossedBond (x + siteOfCoords j v) st = x + siteOfCoords j v := by
          simp [crossedBond, hs]
        rw [StepNearReal, e2]
        exact hb v st.1 hp.1 (e1 ▸ hnext)
    · rw [hstep]
      exact ih hp.2
theorem mem_centredCube_of_between {L : ℕ} {h v : Lattice4} (hh : h ∈ centredCube L) (hL : 1 ≤ L)
    (hv : BetweenOrigin h v) : v ∈ centredCube L := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.mem_centredCube_of_betweenOrigin <;> assumption
theorem pathNearReal_axisPath {X : F.ComplexField j} {R : F.GaugeField j} {t : ℝ} (x : F.Site j)
    (hL : 1 ≤ F.blockSide)
    (hb : ∀ v ∈ centredCube F.blockSide, ∀ k, v + Pi.single k 1 ∈ centredCube F.blockSide →
      BondNearReal X R t (x + siteOfCoords j v) k)
    {h : Lattice4} (hh : h ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    PathNearReal X R t x (axisPath h π) := by
  have h1 : AllAlong (fun v => v ∈ centredCube F.blockSide) 0 (axisPath h π) :=
    allAlong_mono (fun v hv => mem_centredCube_of_between hh hL hv) (axisPath_spec h π).1
  have h2 := pathNearReal_of_allAlong (X := X) (R := R) (t := t) x (P := fun v => v ∈ centredCube F.blockSide)
    (fun v k a b => hb v a k b) h1
  rwa [siteOfCoords_zero, add_zero] at h2
theorem pathNearReal_replicate {X : F.ComplexField j} {R : F.GaugeField j} {t : ℝ} (x : F.Site j)
    (i : Fin 4) (m : ℕ)
    (hb : ∀ r ∈ Finset.range m, BondNearReal X R t (x + (r : ℤ) • unitStep j i) i) :
    PathNearReal X R t x (List.replicate m (i, true)) := by
  induction m generalizing x with
  | zero => trivial
  | succ m ih =>
    rw [List.replicate_succ]
    refine ⟨?_, ih _ fun r hr => ?_⟩
    · have := hb 0 (by simp)
      simpa [StepNearReal, crossedBond, BondNearReal] using this
    · have := hb (r + 1) (by simpa using hr)
      have e : x + BlockAverages.stepDisplacement j (i, true) + (r : ℤ) • unitStep j i =
          x + ((r + 1 : ℕ) : ℤ) • unitStep j i := by
        simp only [BlockAverages.stepDisplacement, if_true]
        push_cast
        rw [add_smul, one_smul]
        abel
      rw [e]
      exact this
theorem bondNearReal_of_pathNearReal_replicate {X : F.ComplexField j} {R : F.GaugeField j} {t : ℝ}
    (x : F.Site j) (i : Fin 4) (m : ℕ)
    (hp : PathNearReal X R t x (List.replicate m (i, true))) :
    ∀ r ∈ Finset.range m, BondNearReal X R t (x + (r : ℤ) • unitStep j i) i := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ] at hp
    intro r hr
    rcases r with _ | r
    · have := hp.1
      simpa [StepNearReal, crossedBond, BondNearReal] using this
    · have h1 := ih _ hp.2 r (by simpa using hr)
      have e : x + BlockAverages.stepDisplacement j (i, true) + (r : ℤ) • unitStep j i =
          x + ((r + 1 : ℕ) : ℤ) • unitStep j i := by
        simp only [BlockAverages.stepDisplacement, if_true]
        push_cast
        rw [add_smul, one_smul]
        abel
      rw [e] at h1
      exact h1
theorem norm_transportedAverage_le (hodd : Odd F.blockSide) (R : F.GaugeField j)
    (f : F.Site j → Fin 4 → ComplexQuat) (c : F.Site (j + 1) × Fin 4) :
    ‖transportedAverage R f c‖ ≤ lineBlockAverage (fun x i => ‖f x i‖) c := by
  have hL : (F.blockSide : ℝ) ≠ 0 := by
    have := hodd.pos
    positivity
  have hw : ‖contourWeight F‖ = 1 / (24 * (F.blockSide : ℝ) ^ 4) := by
    rw [contourWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [transportedAverage, blockContourMean, norm_smul, hw, lineBlockAverage]
  set G : Lattice4 → ℝ := fun h => ∑ r ∈ Finset.range F.blockSide,
    ‖f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2‖ with hG
  have h1 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide,
      conjByUnit (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
        (f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2)‖ ≤
      ∑ h ∈ centredCube F.blockSide, 24 * G h := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
    refine (norm_sum_le _ _).trans ?_
    have : ∀ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin 4))),
        ‖∑ r ∈ Finset.range F.blockSide,
          conjByUnit (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
            (f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2)‖ ≤ G h := fun π _ => by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
      rw [norm_conjByUnit]
    refine (Finset.sum_le_card_nsmul _ _ (G h) this).trans ?_
    simp [Finset.card_univ, card_perm_fin_four]
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * _ ≤
        1 / (24 * (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide, 24 * G h :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 / (F.blockSide : ℝ) ^ 4 * ∑ h ∈ centredCube F.blockSide, G h := by
        rw [← Finset.mul_sum]
        field_simp
theorem norm_trace_linkDeviation_le {X : F.ComplexField j} {R : F.GaugeField j} {t : ℝ} {x : F.Site j}
    {k : Fin 4} (h : BondNearReal X R t x k) : ‖(linkDeviation X R x k).trace‖ ≤ t ^ 2 := by
  refine norm_trace_le_sq_of_det_one_add h.1 ?_
  rw [linkDeviation, add_sub_cancel, Matrix.det_mul, h.2, det_ofUnit, one_mul]
theorem transportedAverage_linkDeviation_small (hodd : Odd F.blockSide) {X : F.ComplexField j}
    {R : F.GaugeField j} {t : ℝ} {c : F.Site (j + 1) × Fin 4}
    (hb : ∀ h ∈ centredCube F.blockSide, ∀ r ∈ Finset.range F.blockSide,
      BondNearReal X R t (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2) (ht : 0 ≤ t) :
    ‖transportedAverage R (linkDeviation X R) c‖ ≤ F.blockSide * t ∧
      ‖(transportedAverage R (linkDeviation X R) c).trace‖ ≤ F.blockSide * t ^ 2 := by
  constructor
  · refine norm_blockContourMean_le hodd fun h hh π => ?_
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ t fun r hr => ?_).trans (by simp)
    rw [norm_conjByUnit]
    exact (hb h hh r hr).1
  · have h1 : (transportedAverage R (linkDeviation X R) c).trace = blockContourMean F (fun h π =>
        ∑ r ∈ Finset.range F.blockSide,
          (linkDeviation X R (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2).trace) := by
      rw [transportedAverage]
      have := map_blockContourMean (F := F) (Matrix.traceLinearMap (Fin 2) ℂ ℂ) (fun h π =>
        ∑ r ∈ Finset.range F.blockSide,
          conjByUnit (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
            (linkDeviation X R (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2))
      refine this.trans ?_
      congr 1
      funext h π
      rw [map_sum]
      exact Finset.sum_congr rfl fun r _ => trace_conjByUnit _ _
    rw [h1]
    refine norm_blockContourMean_le hodd fun h hh π => ?_
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (t ^ 2) fun r hr =>
      norm_trace_linkDeviation_le (hb h hh r hr)).trans (by simp)
set_option maxHeartbeats 1000000 in
theorem unitPart_and_sqrt_near (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {X : F.ComplexField j}
    {R : F.GaugeField j} {t σ : ℝ}
    {c : F.Site (j + 1) × Fin 4} (ht : 0 ≤ t) (hσ : σ ≤ 1 / 64) (hτ : 4 * (F.blockSide : ℝ) * t ≤ 1 / 1024)
    (hg : ContoursNearReal X R t σ c) :
    0 < (complexGaugedContourAverage X (complexBalancingGauge X R) c).det.re ∧
    ‖unitPart (complexGaugedContourAverage X (complexBalancingGauge X R) c) *
        ofUnit (polarUnit (contourAverage R c))⁻¹ - 1 -
        purePart (transportedAverage R (linkDeviation X R) c)‖ ≤
      700 * (4 * (F.blockSide : ℝ) * t) ^ 2 + 20 * σ * (4 * (F.blockSide : ℝ) * t) ∧
    ‖principalSqrt (complexGaugedContourAverage X (complexBalancingGauge X R) c).det -
        ((‖contourAverage R c‖ : ℝ) : ℂ)‖ ≤
      1700 * (4 * (F.blockSide : ℝ) * t) ^ 2 + 72 * σ * (4 * (F.blockSide : ℝ) * t) := by
  set τ : ℝ := 4 * (F.blockSide : ℝ) * t with hτd
  set r : ℝ := ‖contourAverage R c‖ with hr
  set w : UnitQuaternion := polarUnit (contourAverage R c) with hw
  set M := complexGaugedContourAverage X (complexBalancingGauge X R) c with hM
  set P := transportedAverage R (linkDeviation X R) c with hP
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hτ0 : 0 ≤ τ := by positivity
  have hσ0 : 0 ≤ σ := by
    have h0 : (0 : Lattice4) ∈ centredCube F.blockSide := by
      rw [mem_centredCube_iff]
      intro i
      have := hodd.pos
      simp only [Pi.zero_apply]
      omega
    exact (norm_nonneg _).trans (hg.realNearAverage 0 h0 1)
  have hr1 := abs_norm_contourAverage_sub_one_le hodd hg.realNearAverage
  have hrlo : 1 / 2 ≤ r := by
    have := (abs_le.1 hr1).1
    linarith
  have hr0 : 0 < r := by linarith
  have hrc : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hmain := norm_gaugedAverage_mul_sub_le hodd hj ht (by linarith) (by linarith) hg
  rw [← hτd, ← hr, ← hw, ← hM, ← hP] at hmain
  set Z := M * ofUnit w⁻¹ with hZ
  set W := Z - ((r : ℝ) : ℂ) • (1 : ComplexQuat) - P with hW
  have hbonds : ∀ h ∈ centredCube F.blockSide, ∀ q ∈ Finset.range F.blockSide,
      BondNearReal X R t (refineSite c.1 + siteOfCoords j h + (q : ℤ) • unitStep j c.2) c.2 :=
    fun h hh => bondNearReal_of_pathNearReal_replicate _ _ _ (hg.nearLine h hh)
  obtain ⟨hPn, hPt⟩ := transportedAverage_linkDeviation_small hodd hbonds ht
  rw [← hP] at hPn hPt
  have hPτ : ‖P‖ ≤ τ :=
    hPn.trans (by rw [hτd]; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ F.blockSide) ht])
  have hPt2 : ‖P.trace‖ ≤ τ ^ 2 := by
    refine hPt.trans ?_
    rw [hτd]
    have : 0 ≤ (F.blockSide : ℝ) * t ^ 2 := by positivity
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ F.blockSide)
      (by linarith : (0 : ℝ) ≤ F.blockSide)) (sq_nonneg t)]
  set E0 := 205 * τ ^ 2 + 9 * σ * τ with hE0
  have hE0s : E0 ≤ τ / 2 := by
    rw [hE0]
    nlinarith
  set e : ComplexQuat := ((r⁻¹ : ℝ) : ℂ) • (P + W) with he
  have hZe : Z = ((r : ℝ) : ℂ) • (1 + e) := by
    rw [smul_add, he, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr0.ne', hW]
    simp only [Complex.ofReal_one, one_smul]
    abel
  have hrinv : ‖((r⁻¹ : ℝ) : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [inv_le_comm₀ hr0 (by norm_num)]
    linarith
  have hen : ‖e‖ ≤ 3 * τ := by
    rw [he, norm_smul]
    have h1 := norm_add_le P W
    have h2 : ‖P + W‖ ≤ 3 / 2 * τ := by linarith
    calc _ ≤ 2 * (3 / 2 * τ) := mul_le_mul hrinv h2 (norm_nonneg _) (by norm_num)
      _ = 3 * τ := by ring
  have hen1 : ‖e‖ < 1 := by linarith
  have hne := one_add_ne_zero_of_norm_lt_one hen1
  have hdet := det_one_add_ne_zero_of_norm_lt_one hen1
  have hMZ : M = Z * ofUnit w := by
    rw [hZ, mul_assoc, ofUnit_inv_mul, mul_one]
  have hZne : Z ≠ 0 := by
    rw [hZe]
    exact smul_ne_zero hrc hne
  have hdetM : M.det = ((r : ℝ) : ℂ) ^ 2 * ((1 : ComplexQuat) + e).det := by
    rw [hMZ, Matrix.det_mul, det_ofUnit, mul_one, hZe, det_smul_complexQuat]
  refine ⟨?_, ?_, ?_⟩
  · rw [hdetM, det_one_add]
    have h1 := norm_trace_le e
    have h2 := norm_det_le e
    have h4 := norm_add_le e.trace e.det
    have he1 : ‖e‖ ≤ 1 / 100 := by linarith
    have he2 : ‖e‖ ^ 2 ≤ 1 / 100 := by
      have := pow_le_pow_left₀ (norm_nonneg e) he1 2
      linarith
    have h5 : ‖e.trace + e.det‖ ≤ 1 / 2 := by linarith
    have h6 := Complex.abs_re_le_norm (e.trace + e.det)
    have h7 := (abs_le.1 (h6.trans h5)).1
    have e1 : ((r : ℝ) : ℂ) ^ 2 * (1 + (e.trace + e.det)) =
        ((r ^ 2 : ℝ) : ℂ) * (1 + (e.trace + e.det)) := by push_cast; ring
    rw [e1, Complex.re_ofReal_mul]
    have h8 : (1 + (e.trace + e.det)).re = 1 + (e.trace + e.det).re := by simp
    rw [h8]
    have : 0 < r ^ 2 := by positivity
    have h9 : (0 : ℝ) < 1 + (e.trace + e.det).re := by linarith
    positivity
  · have h1 : unitPart M * ofUnit w⁻¹ = unitPart (1 + e) := by
      rw [hMZ, unitPart_mul_ofUnit hZne, mul_assoc, ofUnit_mul_inv, mul_one, hZe,
        unitPart_ofReal_smul hr0 hne hdet]
    rw [h1]
    have h2 := norm_unitPart_one_add_sub_le (e := e) (by linarith)
    have h3 : purePart e - purePart P =
        ((r⁻¹ - 1 : ℝ) : ℂ) • purePart P + ((r⁻¹ : ℝ) : ℂ) • purePart W := by
      rw [he, purePart_smul, purePart_add]
      push_cast
      module
    have hd : |r⁻¹ - 1| ≤ 2 * σ := by
      have e1 : r⁻¹ - 1 = (1 - r) * r⁻¹ := by
        field_simp
      rw [e1, abs_mul, abs_sub_comm, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r⁻¹)]
      have h5 : r⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hr0 (by norm_num)]
        linarith
      nlinarith [abs_nonneg (r - 1)]
    have h4 : ‖purePart e - purePart P‖ ≤ 2 * σ * τ + 2 * E0 := by
      rw [h3]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul]
      have n1 : ‖((r⁻¹ - 1 : ℝ) : ℂ)‖ ≤ 2 * σ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact hd
      have n2 := (norm_purePart_le P).trans hPτ
      have n3 := (norm_purePart_le W).trans hmain
      have m1 := mul_le_mul n1 n2 (norm_nonneg _) (by positivity)
      have m2 := mul_le_mul hrinv n3 (norm_nonneg _) (by norm_num)
      linarith
    have h5 : unitPart (1 + e) - 1 - purePart P =
        (unitPart (1 + e) - 1 - purePart e) + (purePart e - purePart P) := by abel
    rw [h5]
    refine (norm_add_le _ _).trans ?_
    have h6 : ‖e‖ ^ 2 ≤ (3 * τ) ^ 2 := by gcongr
    rw [hE0] at h4
    nlinarith
  · set y : ℂ := e.trace + e.det with hy
    have hdet1 : ((1 : ComplexQuat) + e).det = 1 + y := det_one_add e
    have htr : e.trace = ((r⁻¹ : ℝ) : ℂ) * (P.trace + W.trace) := by
      have := trace_smul_complexQuat ((r⁻¹ : ℝ) : ℂ) (P + W)
      rw [he, this, Matrix.trace_add]
    have hyn : ‖y‖ ≤ 2 * (τ ^ 2 + 2 * E0) + 9 * τ ^ 2 := by
      have h1 := norm_add_le e.trace e.det
      have h2 := norm_det_le e
      have h3 : ‖e‖ ^ 2 ≤ (3 * τ) ^ 2 := by gcongr
      have h4 : ‖e.trace‖ ≤ 2 * (τ ^ 2 + 2 * E0) := by
        rw [htr, norm_mul]
        have h5 := norm_add_le P.trace W.trace
        have h6 := (norm_trace_le W).trans (by linarith : 2 * ‖W‖ ≤ 2 * E0)
        exact mul_le_mul hrinv (by linarith) (norm_nonneg _) (by norm_num)
      nlinarith
    have hy2 : ‖y‖ ≤ 1 / 2 := by nlinarith
    have hw1 : (1 : ℂ) + y ≠ 0 := by
      rw [← hdet1]
      exact hdet
    have hroot : principalSqrt M.det = ((r : ℝ) : ℂ) * principalSqrt (1 + y) := by
      rw [hdetM, hdet1, principalSqrt_ofReal_sq_mul hr0 hw1]
    have h7 := norm_principalSqrt_one_add_sub_le hy2
    have h8 : ‖principalSqrt (1 + y) - 1‖ ≤ ‖y‖ / 2 + 2 * ‖y‖ ^ 2 := by
      have e1 : principalSqrt (1 + y) - 1 = (principalSqrt (1 + y) - 1 - y / 2) + y / 2 := by ring
      rw [e1]
      refine (norm_add_le _ _).trans ?_
      have : ‖y / 2‖ = ‖y‖ / 2 := by simp
      linarith
    have h9 : ‖principalSqrt (1 + y) - 1‖ ≤ ‖y‖ * (3 / 2) := by nlinarith [norm_nonneg y]
    rw [hroot]
    have e2 : ((r : ℝ) : ℂ) * principalSqrt (1 + y) - ((r : ℝ) : ℂ) =
        ((r : ℝ) : ℂ) * (principalSqrt (1 + y) - 1) := by ring
    rw [e2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    have hr2 : r ≤ 5 / 4 := by
      have := (abs_le.1 hr1).2
      linarith
    have h10 : r * ‖principalSqrt (1 + y) - 1‖ ≤ 5 / 4 * (‖y‖ * (3 / 2)) :=
      mul_le_mul hr2 h9 (norm_nonneg _) (by norm_num)
    have hy3 : ‖y‖ ≤ 831 * τ ^ 2 + 36 * (σ * τ) := by
      have e3 : E0 = 205 * τ ^ 2 + 9 * (σ * τ) := by rw [hE0]; ring
      linarith
    have h11 : 0 ≤ σ * τ := mul_nonneg hσ0 hτ0
    have h12 : 0 ≤ τ ^ 2 := sq_nonneg τ
    have e4 : 1700 * τ ^ 2 + 72 * σ * τ = 1700 * τ ^ 2 + 72 * (σ * τ) := by ring
    rw [e4]
    linarith
end NearReal
end ComplexChainStep
end YangMills.Construction
end
