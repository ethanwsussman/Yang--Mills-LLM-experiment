import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction
namespace ComplexifiedQuaternions
abbrev ComplexQuat : Type := Matrix (Fin 2) (Fin 2) ℂ
def ofQuat (q : ℍ[ℝ]) : ComplexQuat :=
  !![(⟨q.re, q.imI⟩ : ℂ), ⟨q.imJ, q.imK⟩; ⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩]
theorem ofQuat_add (p q : ℍ[ℝ]) : ofQuat (p + q) = ofQuat p + ofQuat q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofQuat, Complex.ext_iff, add_comm]
theorem ofQuat_mul (p q : ℍ[ℝ]) : ofQuat (p * q) = ofQuat p * ofQuat q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ofQuat, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;> constructor <;> ring
theorem ofQuat_one : ofQuat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofQuat, Complex.ext_iff]
theorem ofQuat_zero : ofQuat 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofQuat, Complex.ext_iff]
theorem ofQuat_smul (r : ℝ) (q : ℍ[ℝ]) : ofQuat (r • q) = (r : ℂ) • ofQuat q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofQuat, Complex.ext_iff]
theorem ofQuat_star (q : ℍ[ℝ]) : ofQuat (star q) = star (ofQuat q) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofQuat, Complex.ext_iff]
theorem adjugate_ofQuat (q : ℍ[ℝ]) : Matrix.adjugate (ofQuat q) = ofQuat (star q) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofQuat, Matrix.adjugate_fin_two, Complex.ext_iff]
theorem det_ofQuat (q : ℍ[ℝ]) : (ofQuat q).det = ((‖q‖ ^ 2 : ℝ) : ℂ) := by
  have h : ‖q‖ ^ 2 = Quaternion.normSq q := by
    rw [Quaternion.normSq_eq_norm_mul_self]
    ring
  rw [h]
  simp [ofQuat, Matrix.det_fin_two, Complex.ext_iff, Quaternion.normSq_def', sq]
  constructor <;> ring
theorem trace_ofQuat (q : ℍ[ℝ]) : (ofQuat q).trace = ((2 * q.re : ℝ) : ℂ) := by
  simp [ofQuat, Matrix.trace_fin_two, Complex.ext_iff]
  ring
theorem norm_ofQuat (q : ℍ[ℝ]) : ‖ofQuat q‖ = ‖q‖ := by
  have h : ‖star (ofQuat q) * ofQuat q‖ = ‖ofQuat q‖ * ‖ofQuat q‖ := CStarRing.norm_star_mul_self
  have h2 : star (ofQuat q) * ofQuat q = ((‖q‖ ^ 2 : ℝ) : ℂ) • (1 : ComplexQuat) := by
    rw [← ofQuat_star, ← adjugate_ofQuat, Matrix.adjugate_mul, det_ofQuat]
  rw [h2, norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)] at h
  nlinarith [norm_nonneg (ofQuat q), norm_nonneg q]
theorem ofQuat_mem_unitary (g : unitary ℍ[ℝ]) : ofQuat (g : ℍ[ℝ]) ∈ unitary ComplexQuat := by
  have h1 : star (g : ℍ[ℝ]) * g = 1 := Unitary.coe_star_mul_self g
  have h2 : (g : ℍ[ℝ]) * star (g : ℍ[ℝ]) = 1 := Unitary.coe_mul_star_self g
  rw [Unitary.mem_iff]
  constructor
  · rw [← ofQuat_star, ← ofQuat_mul, h1, ofQuat_one]
  · rw [← ofQuat_star, ← ofQuat_mul, h2, ofQuat_one]
theorem norm_ofQuat_unitary_mul (g : unitary ℍ[ℝ]) (e : ComplexQuat) : ‖ofQuat (g : ℍ[ℝ]) * e‖ = ‖e‖ :=
  CStarRing.norm_coe_unitary_mul ⟨_, ofQuat_mem_unitary g⟩ e
theorem norm_mul_ofQuat_unitary (g : unitary ℍ[ℝ]) (e : ComplexQuat) : ‖e * ofQuat (g : ℍ[ℝ])‖ = ‖e‖ :=
  CStarRing.norm_mul_coe_unitary e ⟨_, ofQuat_mem_unitary g⟩
theorem adjugate_map_add (a b : ComplexQuat) :
    Matrix.adjugate (a + b) = Matrix.adjugate a + Matrix.adjugate b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] <;> ring
theorem adjugate_map_sub (a b : ComplexQuat) :
    Matrix.adjugate (a - b) = Matrix.adjugate a - Matrix.adjugate b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] <;> ring
theorem adjugate_map_smul (z : ℂ) (a : ComplexQuat) : Matrix.adjugate (z • a) = z • Matrix.adjugate a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two]
theorem adjugate_adjugate_eq_self (a : ComplexQuat) : Matrix.adjugate (Matrix.adjugate a) = a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two]
theorem adjugate_eq_trace_smul_sub (a : ComplexQuat) : Matrix.adjugate a = a.trace • (1 : ComplexQuat) - a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two, Matrix.trace_fin_two]
theorem norm_map_conj_le (a : ComplexQuat) : ‖a.map (starRingEnd ℂ)‖ ≤ ‖a‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM (a.map (starRingEnd ℂ))]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  set w : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 fun i => starRingEnd ℂ (v i) with hw
  have hwn : ‖w‖ = ‖v‖ := by simp [EuclideanSpace.norm_eq, hw]
  have h := (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) a).le_opNorm w
  rw [Matrix.l2_opNorm_toEuclideanCLM, hwn] at h
  refine le_trans (le_of_eq ?_) h
  simp only [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [Matrix.ofLp_toEuclideanCLM]
  have : (a.map (starRingEnd ℂ)).mulVec (WithLp.ofLp v) i =
      starRingEnd ℂ (a.mulVec (WithLp.ofLp w) i) := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hw]
  rw [this, Complex.norm_conj]
def symplecticJ : unitary ComplexQuat := ⟨!![0, 1; -1, 0], by
  rw [Unitary.mem_iff]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]⟩
theorem adjugate_eq_symplectic_conj (a : ComplexQuat) : Matrix.adjugate a =
    (symplecticJ : ComplexQuat) * (a.map (starRingEnd ℂ)).conjTranspose * star (symplecticJ : ComplexQuat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symplecticJ, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
      Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, Matrix.map_apply]
theorem norm_adjugate_le (a : ComplexQuat) : ‖Matrix.adjugate a‖ ≤ ‖a‖ := by
  have h : star (symplecticJ : ComplexQuat) = ((star symplecticJ : unitary ComplexQuat) : ComplexQuat) := rfl
  rw [adjugate_eq_symplectic_conj, h, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_conjTranspose]
  exact norm_map_conj_le a
theorem norm_adjugate (a : ComplexQuat) : ‖Matrix.adjugate a‖ = ‖a‖ := by
  refine le_antisymm (norm_adjugate_le a) ?_
  have := norm_adjugate_le (Matrix.adjugate a)
  rwa [adjugate_adjugate_eq_self] at this
def purePart (e : ComplexQuat) : ComplexQuat := (1 / 2 : ℂ) • (e - Matrix.adjugate e)
theorem norm_purePart_le (e : ComplexQuat) : ‖purePart e‖ ≤ ‖e‖ := by
  unfold purePart
  rw [norm_smul]
  have h := norm_sub_le e (Matrix.adjugate e)
  rw [norm_adjugate] at h
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [this]
  linarith
theorem purePart_add (a b : ComplexQuat) : purePart (a + b) = purePart a + purePart b := by
  simp only [purePart, adjugate_map_add, ← smul_add]
  congr 1
  abel
theorem purePart_sub (a b : ComplexQuat) : purePart (a - b) = purePart a - purePart b := by
  simp only [purePart, adjugate_map_sub, ← smul_sub]
  congr 1
  abel
theorem purePart_smul (z : ℂ) (a : ComplexQuat) : purePart (z • a) = z • purePart a := by
  simp only [purePart, adjugate_map_smul, ← smul_sub, smul_comm z]
theorem purePart_ofQuat (q : ℍ[ℝ]) : purePart (ofQuat q) = ofQuat ((1 / 2 : ℝ) • (q - star q)) := by
  rw [ofQuat_smul, purePart, adjugate_ofQuat, sub_eq_add_neg (q) (star q), ofQuat_add]
  have : ofQuat (-star q) = - ofQuat (star q) := by
    have h := ofQuat_smul (-1) (star q)
    simpa using h
  rw [this, sub_eq_add_neg]
  norm_num
theorem purePart_conj (g : unitary ℍ[ℝ]) (e : ComplexQuat) :
    purePart (ofQuat (g : ℍ[ℝ]) * e * ofQuat (star (g : ℍ[ℝ]))) =
      ofQuat (g : ℍ[ℝ]) * purePart e * ofQuat (star (g : ℍ[ℝ])) := by
  have h1 : Matrix.adjugate (ofQuat (g : ℍ[ℝ]) * e * ofQuat (star (g : ℍ[ℝ]))) =
      ofQuat (g : ℍ[ℝ]) * Matrix.adjugate e * ofQuat (star (g : ℍ[ℝ])) := by
    rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, adjugate_ofQuat, adjugate_ofQuat, star_star,
      mul_assoc]
  simp only [purePart, h1, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul]
theorem trace_smul_one_eq_add_adjugate (e : ComplexQuat) :
    e.trace • (1 : ComplexQuat) = e + Matrix.adjugate e := by
  rw [adjugate_eq_trace_smul_sub]
  abel
theorem norm_trace_le (e : ComplexQuat) : ‖e.trace‖ ≤ 2 * ‖e‖ := by
  have h : ‖e.trace • (1 : ComplexQuat)‖ = ‖e.trace‖ := by
    rw [norm_smul, CStarRing.norm_one, mul_one]
  rw [← h, trace_smul_one_eq_add_adjugate]
  have := norm_add_le e (Matrix.adjugate e)
  rw [norm_adjugate] at this
  linarith
theorem norm_det_le (e : ComplexQuat) : ‖e.det‖ ≤ ‖e‖ ^ 2 := by
  have h : ‖e.det • (1 : ComplexQuat)‖ = ‖e.det‖ := by
    rw [norm_smul, CStarRing.norm_one, mul_one]
  rw [← h, ← Matrix.mul_adjugate]
  have := norm_mul_le e (Matrix.adjugate e)
  rw [norm_adjugate] at this
  nlinarith
theorem det_one_add (e : ComplexQuat) : ((1 : ComplexQuat) + e).det = 1 + (e.trace + e.det) := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]
  ring
theorem purePart_eq_sub_half_trace (e : ComplexQuat) : purePart e = e - (e.trace / 2) • (1 : ComplexQuat) := by
  rw [purePart, adjugate_eq_trace_smul_sub]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring
def invSqrt (w : ℂ) : ℂ := Complex.exp (-(1 / 2) * Complex.log w)
def principalSqrt (w : ℂ) : ℂ := Complex.exp ((1 / 2) * Complex.log w)
theorem log_ofReal_sq {x : ℝ} (hx : 0 < x) : Complex.log ((x ^ 2 : ℝ) : ℂ) = 2 * (Real.log x : ℂ) := by
  rw [← Complex.ofReal_log (by positivity), Real.log_pow]
  push_cast
  ring
theorem invSqrt_ofReal_sq {x : ℝ} (hx : 0 < x) : invSqrt ((x ^ 2 : ℝ) : ℂ) = ((x⁻¹ : ℝ) : ℂ) := by
  rw [invSqrt, log_ofReal_sq hx]
  have : -(1 / 2) * (2 * (Real.log x : ℂ)) = ((-Real.log x : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hx]
theorem principalSqrt_ofReal_sq {x : ℝ} (hx : 0 < x) : principalSqrt ((x ^ 2 : ℝ) : ℂ) = (x : ℂ) := by
  rw [principalSqrt, log_ofReal_sq hx]
  have : (1 / 2) * (2 * (Real.log x : ℂ)) = ((Real.log x : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this, ← Complex.ofReal_exp, Real.exp_log hx]
def unitPart (q : ComplexQuat) : ComplexQuat := if q = 0 then 1 else invSqrt q.det • q
theorem norm_invSqrt_one_add_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖invSqrt (1 + w) - 1 + w / 2‖ ≤ 2 * ‖w‖ ^ 2 := by
  have hlt : ‖w‖ < 1 := by linarith
  have h1 := Complex.norm_log_one_add_sub_self_le hlt
  have hw0 := norm_nonneg w
  have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have h2 : ‖Complex.log (1 + w) - w‖ ≤ ‖w‖ ^ 2 := by
    refine h1.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖w‖)]
  set y : ℂ := -(1 / 2) * Complex.log (1 + w) with hy
  have h3 : ‖y + w / 2‖ ≤ ‖w‖ ^ 2 / 2 := by
    have : y + w / 2 = -(1 / 2) * (Complex.log (1 + w) - w) := by
      rw [hy]
      ring
    rw [this, norm_mul]
    have : ‖(-(1 / 2) : ℂ)‖ = 1 / 2 := by simp
    rw [this]
    linarith
  have h4 : ‖y‖ ≤ ‖w‖ := by
    have : y = (y + w / 2) - w / 2 := by ring
    have h5 : ‖y‖ ≤ ‖y + w / 2‖ + ‖w / 2‖ := by
      conv_lhs => rw [this]
      exact norm_sub_le _ _
    have h6 : ‖w / 2‖ = ‖w‖ / 2 := by simp
    nlinarith
  have h7 : ‖y‖ ≤ 1 := by linarith
  have h8 := Complex.norm_exp_sub_one_sub_id_le h7
  have h9 : invSqrt (1 + w) - 1 + w / 2 = (Complex.exp y - 1 - y) + (y + w / 2) := by
    rw [invSqrt]
    ring
  rw [h9]
  refine (norm_add_le _ _).trans ?_
  nlinarith [sq_nonneg ‖w‖, sq_nonneg ‖y‖, mul_le_mul h4 h4 (norm_nonneg y) hw0]
theorem norm_principalSqrt_one_add_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖principalSqrt (1 + w) - 1 - w / 2‖ ≤ 2 * ‖w‖ ^ 2 := by
  have hlt : ‖w‖ < 1 := by linarith
  have h1 := Complex.norm_log_one_add_sub_self_le hlt
  have hw0 := norm_nonneg w
  have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have h2 : ‖Complex.log (1 + w) - w‖ ≤ ‖w‖ ^ 2 := by
    refine h1.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖w‖)]
  set y : ℂ := (1 / 2) * Complex.log (1 + w) with hy
  have h3 : ‖y - w / 2‖ ≤ ‖w‖ ^ 2 / 2 := by
    have : y - w / 2 = (1 / 2) * (Complex.log (1 + w) - w) := by
      rw [hy]
      ring
    rw [this, norm_mul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
    linarith
  have h4 : ‖y‖ ≤ ‖w‖ := by
    have : y = (y - w / 2) + w / 2 := by ring
    have h5 : ‖y‖ ≤ ‖y - w / 2‖ + ‖w / 2‖ := by
      conv_lhs => rw [this]
      exact norm_add_le _ _
    have h6 : ‖w / 2‖ = ‖w‖ / 2 := by simp
    nlinarith
  have h7 : ‖y‖ ≤ 1 := by linarith
  have h8 := Complex.norm_exp_sub_one_sub_id_le h7
  have h9 : principalSqrt (1 + w) - 1 - w / 2 = (Complex.exp y - 1 - y) + (y - w / 2) := by
    rw [principalSqrt]
    ring
  rw [h9]
  refine (norm_add_le _ _).trans ?_
  nlinarith [sq_nonneg ‖w‖, sq_nonneg ‖y‖, mul_le_mul h4 h4 (norm_nonneg y) hw0]
theorem one_add_ne_zero_of_norm_lt_one {e : ComplexQuat} (he : ‖e‖ < 1) : (1 : ComplexQuat) + e ≠ 0 := by
  intro h
  have : e = -1 := by
    rw [add_comm] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [this, norm_neg, CStarRing.norm_one] at he
  exact lt_irrefl _ he
theorem norm_unitPart_one_add_sub_le {e : ComplexQuat} (he : ‖e‖ ≤ 1 / 8) :
    ‖unitPart (1 + e) - 1 - purePart e‖ ≤ 32 * ‖e‖ ^ 2 := by
  have hne := one_add_ne_zero_of_norm_lt_one (lt_of_le_of_lt he (by norm_num))
  set w : ℂ := e.trace + e.det with hw
  have he0 := norm_nonneg e
  have hw3 : ‖w‖ ≤ 3 * ‖e‖ := by
    have := norm_add_le e.trace e.det
    have h1 := norm_trace_le e
    have h2 := norm_det_le e
    nlinarith
  have hw2 : ‖w‖ ≤ 1 / 2 := by linarith
  have h1 := norm_invSqrt_one_add_sub_le hw2
  set ε : ℂ := invSqrt (1 + w) - 1 + w / 2 with hε
  have hinv : invSqrt (1 + w) = 1 - w / 2 + ε := by
    rw [hε]
    ring
  have h2 : unitPart (1 + e) - 1 - purePart e =
      ε • (1 : ComplexQuat) + (-(e.det / 2)) • (1 : ComplexQuat) + (ε - w / 2) • e := by
    rw [unitPart, if_neg hne, det_one_add, ← hw, hinv, purePart_eq_sub_half_trace]
    rw [hw]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have h3 : ‖ε • (1 : ComplexQuat)‖ = ‖ε‖ := by
    rw [norm_smul, CStarRing.norm_one, mul_one]
  have h4 : ‖(-(e.det / 2)) • (1 : ComplexQuat)‖ ≤ ‖e‖ ^ 2 / 2 := by
    rw [norm_smul, CStarRing.norm_one, mul_one, norm_neg, norm_div]
    have := norm_det_le e
    simp only [Complex.norm_ofNat]
    linarith
  have h5 : ‖(ε - w / 2) • e‖ ≤ (‖ε‖ + ‖w‖ / 2) * ‖e‖ := by
    rw [norm_smul]
    have : ‖ε - w / 2‖ ≤ ‖ε‖ + ‖w‖ / 2 := by
      refine (norm_sub_le _ _).trans ?_
      simp
    exact mul_le_mul_of_nonneg_right this he0
  rw [h2]
  have h6 := norm_add_le (ε • (1 : ComplexQuat) + (-(e.det / 2)) • (1 : ComplexQuat)) ((ε - w / 2) • e)
  have h7 := norm_add_le (ε • (1 : ComplexQuat)) ((-(e.det / 2)) • (1 : ComplexQuat))
  have h8 : ‖ε‖ ≤ 18 * ‖e‖ ^ 2 := by
    have : ‖w‖ ^ 2 ≤ (3 * ‖e‖) ^ 2 := by gcongr
    nlinarith
  have h9 : (‖ε‖ + ‖w‖ / 2) * ‖e‖ ≤ (18 * ‖e‖ ^ 2 + 3 * ‖e‖ / 2) * ‖e‖ :=
    mul_le_mul_of_nonneg_right (by linarith) he0
  nlinarith [sq_nonneg ‖e‖]
end ComplexifiedQuaternions
end YangMills.Construction
end
