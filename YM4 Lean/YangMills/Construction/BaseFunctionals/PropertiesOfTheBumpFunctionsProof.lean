import YangMills.Construction.BaseFunctionals.PropertiesOfTheBumpFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
noncomputable section
namespace YangMills.Construction
open EuclideanFour Euclidean
namespace Mollifiers.BumpProperties
theorem expBump_eq_expNegInvGlue : expBump = expNegInvGlue := by
  funext t
  unfold expBump expNegInvGlue
  by_cases h : 0 < t
  · rw [if_pos h, if_neg (not_le.2 h), neg_div, one_div]
  · rw [if_neg h, if_pos (not_lt.1 h)]
theorem contDiff_expBump : ContDiff ℝ ∞ expBump := by
  rw [expBump_eq_expNegInvGlue]
  exact expNegInvGlue.contDiff
theorem expBump_pos {t : ℝ} (ht : 0 < t) : 0 < expBump t := by
  unfold expBump
  rw [if_pos ht]
  exact Real.exp_pos _
theorem expBump_of_nonpos {t : ℝ} (ht : t ≤ 0) : expBump t = 0 := by
  unfold expBump
  rw [if_neg (not_lt.2 ht)]
theorem expBump_nonneg (t : ℝ) : 0 ≤ expBump t := by
  by_cases ht : 0 < t
  · exact (expBump_pos ht).le
  · rw [expBump_of_nonpos (not_lt.1 ht)]
theorem expBump_lt_one (t : ℝ) : expBump t < 1 := by
  by_cases ht : 0 < t
  · unfold expBump
    rw [if_pos ht, Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by norm_num) ht
  · rw [expBump_of_nonpos (not_lt.1 ht)]
    exact zero_lt_one
theorem expBump_pos_iff (t : ℝ) : 0 < expBump t ↔ 0 < t := by
  refine ⟨fun hp => ?_, expBump_pos⟩
  by_contra hn
  rw [expBump_of_nonpos (not_lt.1 hn)] at hp
  exact lt_irrefl _ hp
theorem expBump_ne_zero_iff (t : ℝ) : expBump t ≠ 0 ↔ 0 < t := by
  rw [← expBump_pos_iff]
  exact ⟨fun hp => lt_of_le_of_ne (expBump_nonneg t) hp.symm, fun hp => hp.ne'⟩
theorem eucNorm_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ eucNorm x :=
  Real.sqrt_nonneg _
theorem eucNorm_sq {n : ℕ} (x : Fin n → ℝ) : eucNorm x ^ 2 = ∑ i, x i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))
theorem eucNorm_smul {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    eucNorm (c • x) = |c| * eucNorm x := by
  unfold eucNorm
  have hsum : ∑ i, (c • x) i ^ 2 = c ^ 2 * ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_pow]
  rw [hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
theorem continuous_eucNorm {n : ℕ} : Continuous (eucNorm (n := n)) := by
  unfold eucNorm
  fun_prop
theorem contDiff_eucNorm_sq {n : ℕ} :
    ContDiff ℝ ∞ (fun x : Fin n → ℝ => eucNorm x ^ 2) := by
  simp_rw [eucNorm_sq]
  exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).pow 2
theorem eucNorm_orthAct (A : O4) (x : R4Point) :
    eucNorm (orthAct A x) = eucNorm x := by
  have hA : (A : RealMatrix4)ᵀ * (A : RealMatrix4) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ).1 A.2
  have hsq : ∑ i, ((A : RealMatrix4) *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
    calc ∑ i, ((A : RealMatrix4) *ᵥ x) i ^ 2
        = ((A : RealMatrix4) *ᵥ x) ⬝ᵥ ((A : RealMatrix4) *ᵥ x) := by simp [dotProduct, sq]
      _ = x ⬝ᵥ x := by
          rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hA,
            Matrix.one_mulVec]
      _ = ∑ i, x i ^ 2 := by simp [dotProduct, sq]
  unfold eucNorm orthAct
  rw [hsq]
theorem closedBallAt_zero_eq (r : ℝ) : closedBallAt 0 r = {x | eucNorm x ≤ r} := by
  ext x
  change TorusMetric.euclidNormVec (x - 0) ≤ r ↔ eucNorm x ≤ r
  rw [sub_zero]
  rfl
theorem closure_eucNorm_lt {ε : ℝ} (hε : 0 < ε) :
    closure {x : R4Point | eucNorm x < ε} = {x | eucNorm x ≤ ε} := by
  apply Subset.antisymm
  · exact closure_minimal (fun x (hx : eucNorm x < ε) => (le_of_lt hx : eucNorm x ≤ ε))
      (isClosed_le continuous_eucNorm continuous_const)
  · intro x hx
    have hlim : Tendsto (fun t : ℝ => t • x) (𝓝[<] 1) (𝓝 x) := by
      have h1 : Tendsto (fun t : ℝ => t • x) (𝓝 1) (𝓝 ((1 : ℝ) • x)) :=
        (continuous_id.smul continuous_const).tendsto 1
      rw [one_smul] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with t ht
    rw [eucNorm_smul, abs_of_pos ht.1]
    calc t * eucNorm x ≤ t * ε := mul_le_mul_of_nonneg_left hx ht.1.le
      _ < 1 * ε := mul_lt_mul_of_pos_right ht.2 hε
      _ = ε := one_mul ε
theorem hasCompactSupport_of_eucNorm_sq_le {n : ℕ} {f : (Fin n → ℝ) → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ x, f x ≠ 0 → eucNorm x ^ 2 ≤ r ^ 2) : HasCompactSupport f := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℝ) r) fun x hx => ?_
  by_contra hne
  apply hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hr]
  intro i
  rw [Real.norm_eq_abs]
  refine abs_le_of_sq_le_sq ?_ hr
  calc x i ^ 2 ≤ ∑ j, x j ^ 2 :=
        Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    _ = eucNorm x ^ 2 := (eucNorm_sq x).symm
    _ ≤ r ^ 2 := hf x hne
theorem ofReal_mem_smoothCompact {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : (fun x => (f x : ℂ)) ∈ smoothCompact n := by
  refine ⟨Complex.ofRealCLM.contDiff.comp hf, ?_⟩
  have hs : closedSupport (fun x => (f x : ℂ)) = tsupport f := by
    unfold closedSupport tsupport Function.support
    simp
  rw [hs]
  exact hc
theorem contDiff_bumpProfileFour :
    ContDiff ℝ ∞ (fun x : R4Point => expBump (1 - eucNorm x ^ 2)) :=
  contDiff_expBump.comp (contDiff_const.sub contDiff_eucNorm_sq)
theorem hasCompactSupport_bumpProfileFour :
    HasCompactSupport (fun x : R4Point => expBump (1 - eucNorm x ^ 2)) := by
  refine hasCompactSupport_of_eucNorm_sq_le zero_le_one fun x hx => ?_
  have := (expBump_ne_zero_iff _).1 hx
  rw [one_pow]
  linarith
theorem bumpMassFour_pos : 0 < bumpMassFour := by
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    contDiff_bumpProfileFour.continuous hasCompactSupport_bumpProfileFour
    (fun x => expBump_nonneg _) (x := 0) ?_
  refine (expBump_ne_zero_iff _).2 ?_
  have h0 : eucNorm (0 : R4Point) = 0 := by simp [eucNorm]
  rw [h0]
  norm_num
theorem integral_stdMollifier : (∫ x : R4Point, stdMollifier x) = 1 := by
  unfold stdMollifier
  rw [integral_const_mul]
  exact inv_mul_cancel₀ bumpMassFour_pos.ne'
theorem rescaledMollifier_nonneg {ε : ℝ} (hε : 0 < ε) (x : R4Point) :
    0 ≤ rescaledMollifier ε x := by
  unfold rescaledMollifier stdMollifier
  have h1 : 0 ≤ ε ^ (-4 : ℤ) := (zpow_pos hε _).le
  have h2 : 0 ≤ bumpMassFour⁻¹ := (inv_pos.2 bumpMassFour_pos).le
  exact mul_nonneg h1 (mul_nonneg h2 (expBump_nonneg _))
theorem rescaledMollifier_ne_zero_iff {ε : ℝ} (hε : 0 < ε) (x : R4Point) :
    rescaledMollifier ε x ≠ 0 ↔ eucNorm x < ε := by
  unfold rescaledMollifier stdMollifier
  have h1 : ε ^ (-4 : ℤ) ≠ 0 := (zpow_pos hε _).ne'
  have h2 : bumpMassFour⁻¹ ≠ 0 := (inv_pos.2 bumpMassFour_pos).ne'
  rw [Ne, mul_eq_zero, mul_eq_zero, not_or, not_or]
  have h3 : 0 < 1 - eucNorm (ε⁻¹ • x) ^ 2 ↔ eucNorm x < ε := by
    rw [eucNorm_smul, abs_of_pos (inv_pos.2 hε), sub_pos,
      sq_lt_one_iff₀ (mul_nonneg (inv_pos.2 hε).le (eucNorm_nonneg x)), inv_mul_lt_iff₀ hε,
      mul_one]
  rw [← h3, ← expBump_ne_zero_iff]
  exact ⟨fun h => h.2.2, fun h => ⟨h1, h2, h⟩⟩
theorem contDiff_rescaledMollifier (ε : ℝ) : ContDiff ℝ ∞ (rescaledMollifier ε) := by
  unfold rescaledMollifier stdMollifier
  exact contDiff_const.mul (contDiff_const.mul
    (contDiff_bumpProfileFour.comp (contDiff_const_smul ε⁻¹)))
theorem integral_rescaledMollifier {ε : ℝ} (hε : 0 < ε) :
    (∫ x : R4Point, rescaledMollifier ε x) = 1 := by
  unfold rescaledMollifier
  rw [integral_const_mul, Measure.integral_comp_smul volume stdMollifier ε⁻¹,
    integral_stdMollifier]
  have hdim : Module.finrank ℝ R4Point = 4 := by simp
  rw [hdim, abs_of_pos (inv_pos.2 (pow_pos (inv_pos.2 hε) 4)), smul_eq_mul, mul_one,
    inv_pow, inv_inv, _root_.zpow_neg]
  have h4 : ε ^ (4 : ℤ) = ε ^ 4 := by norm_cast
  rw [h4]
  exact inv_mul_cancel₀ (pow_pos hε 4).ne'
theorem rescaledMollifierFacts_holds {ε : ℝ} (hε : 0 < ε) : RescaledMollifierFacts ε := by
  refine ⟨ofReal_mem_smoothCompact (contDiff_rescaledMollifier ε) ?_,
    rescaledMollifier_nonneg hε, integral_rescaledMollifier hε, ?_, fun R => ?_⟩
  · refine hasCompactSupport_of_eucNorm_sq_le hε.le fun x hx => ?_
    exact pow_le_pow_left₀ (eucNorm_nonneg x)
      ((rescaledMollifier_ne_zero_iff hε x).1 hx).le 2
  · unfold closedSupport
    have hset : {x | rescaledMollifier ε x ≠ 0} = {x : R4Point | eucNorm x < ε} := by
      ext x
      exact rescaledMollifier_ne_zero_iff hε x
    rw [hset, closure_eucNorm_lt hε, closedBallAt_zero_eq]
  · funext x
    rw [RigidMotion.ofO4_actFun]
    unfold rescaledMollifier stdMollifier
    have hn : eucNorm (ε⁻¹ • orthAct R⁻¹ x) = eucNorm (ε⁻¹ • x) := by
      rw [eucNorm_smul, eucNorm_smul, eucNorm_orthAct]
    rw [hn]
theorem contDiff_bumpProfileOne : ContDiff ℝ ∞ (fun u : ℝ => expBump (1 - u ^ 2)) :=
  contDiff_expBump.comp (contDiff_const.sub (contDiff_id.pow 2))
theorem hasCompactSupport_bumpProfileOne :
    HasCompactSupport (fun u : ℝ => expBump (1 - u ^ 2)) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun u hu => ?_
  refine expBump_of_nonpos ?_
  have h1 : 1 < |u| := by
    by_contra hn
    exact hu (abs_le.1 (not_lt.1 hn))
  have h2 : 1 < u ^ 2 := by
    rw [← sq_abs]
    exact one_lt_pow₀ h1 two_ne_zero
  linarith
theorem bumpMassOne_pos : 0 < bumpMassOne := by
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    contDiff_bumpProfileOne.continuous hasCompactSupport_bumpProfileOne
    (fun u => expBump_nonneg _) (x := 0) ?_
  refine (expBump_ne_zero_iff _).2 ?_
  norm_num
theorem integral_stdMollifierLine : (∫ u : ℝ, stdMollifierLine u) = 1 := by
  unfold stdMollifierLine
  rw [integral_const_mul]
  exact inv_mul_cancel₀ bumpMassOne_pos.ne'
theorem rescaledMollifierLine_nonneg {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    0 ≤ rescaledMollifierLine ε u := by
  unfold rescaledMollifierLine stdMollifierLine
  exact mul_nonneg (inv_pos.2 hε).le
    (mul_nonneg (inv_pos.2 bumpMassOne_pos).le (expBump_nonneg _))
theorem rescaledMollifierLine_ne_zero_iff {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    rescaledMollifierLine ε u ≠ 0 ↔ |u| < ε := by
  unfold rescaledMollifierLine stdMollifierLine
  have h1 : ε⁻¹ ≠ 0 := (inv_pos.2 hε).ne'
  have h2 : bumpMassOne⁻¹ ≠ 0 := (inv_pos.2 bumpMassOne_pos).ne'
  rw [Ne, mul_eq_zero, mul_eq_zero, not_or, not_or]
  have h3 : 0 < 1 - (u / ε) ^ 2 ↔ |u| < ε := by
    rw [sub_pos, sq_lt_one_iff_abs_lt_one, abs_div, abs_of_pos hε, div_lt_one hε]
  rw [← h3, ← expBump_ne_zero_iff]
  exact ⟨fun h => h.2.2, fun h => ⟨h1, h2, h⟩⟩
theorem contDiff_rescaledMollifierLine (ε : ℝ) : ContDiff ℝ ∞ (rescaledMollifierLine ε) := by
  unfold rescaledMollifierLine stdMollifierLine
  exact contDiff_const.mul (contDiff_const.mul
    (contDiff_bumpProfileOne.comp (contDiff_id.div_const ε)))
theorem integral_rescaledMollifierLine {ε : ℝ} (hε : 0 < ε) :
    (∫ u : ℝ, rescaledMollifierLine ε u) = 1 := by
  unfold rescaledMollifierLine
  rw [integral_const_mul, Measure.integral_comp_div stdMollifierLine ε, integral_stdMollifierLine,
    abs_of_pos hε, smul_eq_mul, mul_one]
  exact inv_mul_cancel₀ hε.ne'
theorem rescaledMollifierLineFacts_holds {ε : ℝ} (hε : 0 < ε) :
    RescaledMollifierLineFacts ε := by
  refine ⟨ofReal_mem_smoothCompact
      ((contDiff_rescaledMollifierLine ε).comp (contDiff_apply ℝ ℝ (0 : Fin 1))) ?_,
    rescaledMollifierLine_nonneg hε, integral_rescaledMollifierLine hε, ?_⟩
  · refine hasCompactSupport_of_eucNorm_sq_le hε.le fun u hu => ?_
    have h := (rescaledMollifierLine_ne_zero_iff hε (u 0)).1 hu
    rw [eucNorm_sq, Fin.sum_univ_one, ← sq_abs (u 0)]
    exact pow_le_pow_left₀ (abs_nonneg _) h.le 2
  · unfold closedSupport
    have hset : {u : Fin 1 → ℝ | rescaledMollifierLine ε (u 0) ≠ 0} =
        (Homeomorph.funUnique (Fin 1) ℝ) ⁻¹' Ioo (-ε) ε := by
      ext u
      change rescaledMollifierLine ε (u 0) ≠ 0 ↔ u 0 ∈ Ioo (-ε) ε
      rw [rescaledMollifierLine_ne_zero_iff hε, abs_lt]
      rfl
    rw [hset, ← Homeomorph.preimage_closure, closure_Ioo (by linarith : -ε ≠ ε)]
    rfl
theorem contDiff_shellCutoff_inner :
    ContDiff ℝ ∞ (fun x : R4Point => expBump (3 / 4 - eucNorm x ^ 2)) :=
  contDiff_expBump.comp (contDiff_const.sub contDiff_eucNorm_sq)
theorem contDiff_shellCutoff_outer :
    ContDiff ℝ ∞ (fun x : R4Point => expBump (eucNorm x ^ 2 - 1 / 4)) :=
  contDiff_expBump.comp (contDiff_eucNorm_sq.sub contDiff_const)
theorem shellCutoff_denom_pos (x : R4Point) :
    0 < expBump (3 / 4 - eucNorm x ^ 2) + expBump (eucNorm x ^ 2 - 1 / 4) := by
  by_cases h : eucNorm x ^ 2 < 3 / 4
  · exact add_pos_of_pos_of_nonneg (expBump_pos (by linarith)) (expBump_nonneg _)
  · exact add_pos_of_nonneg_of_pos (expBump_nonneg _) (expBump_pos (by linarith))
theorem contDiff_shellCutoff : ContDiff ℝ ∞ shellCutoff :=
  contDiff_shellCutoff_inner.div (contDiff_shellCutoff_inner.add contDiff_shellCutoff_outer)
    fun x => (shellCutoff_denom_pos x).ne'
theorem eucNorm_sq_lt_of_shellCutoff_ne_zero {x : R4Point} (h : shellCutoff x ≠ 0) :
    eucNorm x ^ 2 < 3 / 4 := by
  by_contra hn
  apply h
  unfold shellCutoff
  rw [expBump_of_nonpos (by linarith), zero_div]
theorem half_sqrt_three_sq : (1 / 2 * Real.sqrt 3) ^ 2 = 3 / 4 := by
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  norm_num
theorem shellCutoffFacts_holds : ShellCutoffFacts := by
  have hr : (0 : ℝ) ≤ 1 / 2 * Real.sqrt 3 := by positivity
  refine ⟨ofReal_mem_smoothCompact contDiff_shellCutoff ?_, fun x => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · refine hasCompactSupport_of_eucNorm_sq_le zero_le_one fun x hx => ?_
    have := eucNorm_sq_lt_of_shellCutoff_ne_zero hx
    rw [one_pow]
    linarith
  · exact div_nonneg (expBump_nonneg _) (shellCutoff_denom_pos x).le
  · refine (div_le_one (shellCutoff_denom_pos x)).2 ?_
    linarith [expBump_nonneg (eucNorm x ^ 2 - 1 / 4)]
  · intro x hx
    rw [closedBallAt_zero_eq] at hx
    have hx' : eucNorm x ≤ 1 / 2 := hx
    have h2 : eucNorm x ^ 2 ≤ (1 / 2) ^ 2 :=
      pow_le_pow_left₀ (eucNorm_nonneg x) hx' 2
    have h3 : eucNorm x ^ 2 ≤ 1 / 4 := by
      norm_num at h2 ⊢
      linarith
    unfold shellCutoff
    rw [expBump_of_nonpos (by linarith : eucNorm x ^ 2 - 1 / 4 ≤ 0), add_zero]
    exact div_self (expBump_pos (by linarith)).ne'
  · rw [closedBallAt_zero_eq]
    refine closure_minimal (fun x hx => ?_)
      (isClosed_le continuous_eucNorm continuous_const)
    have h := eucNorm_sq_lt_of_shellCutoff_ne_zero hx
    rw [← half_sqrt_three_sq] at h
    exact (le_abs_self _).trans (abs_le_of_sq_le_sq h.le hr)
  · rw [closedBallAt_zero_eq]
    intro x hx
    have hs : Real.sqrt 3 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hx' : eucNorm x ≤ 1 / 2 * Real.sqrt 3 := hx
    change eucNorm (x - 0) < 1
    rw [sub_zero]
    linarith
theorem bumpFacts_holds : bumpFacts := by
  refine ⟨⟨contDiff_expBump, fun t => ⟨expBump_nonneg t, expBump_lt_one t⟩, expBump_pos_iff⟩,
    fun ε hε => ⟨rescaledMollifierFacts_holds hε, rescaledMollifierLineFacts_holds hε⟩, ⟨?_, ?_⟩,
    shellCutoffFacts_holds⟩
  · funext x
    simp [rescaledMollifier]
  · funext u
    simp [rescaledMollifierLine]
end Mollifiers.BumpProperties
end YangMills.Construction
