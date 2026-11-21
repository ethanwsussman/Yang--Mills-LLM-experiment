import YangMills.Construction.Matrices.PointwiseDerivativeRules
import Mathlib
open Filter Asymptotics
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
private theorem completeSpace_complexMatrix2 : CompleteSpace ComplexMatrix2 :=
  FiniteDimensional.complete ℂ ComplexMatrix2
private theorem logSeries_one : logSeries (1 : ComplexMatrix2) = 0 := by
  simp [logSeries]
private theorem norm_logSeries_one_add_sub_le {E : ComplexMatrix2} (hE : ‖E‖ ≤ 1 / 2) :
    ‖logSeries (1 + E) - E‖ ≤ 2 * ‖E‖ ^ 2 := by
  have := completeSpace_complexMatrix2
  have hlt : ‖E‖ < 1 := by linarith
  set a : ℕ → ComplexMatrix2 := fun n => ((n + 1 : ℂ)⁻¹) • (-E) ^ (n + 1) with ha
  have hbound : ∀ n, ‖a n‖ ≤ ‖E‖ ^ (n + 1) := by
    intro n
    have h1 : ‖((n + 1 : ℂ)⁻¹)‖ ≤ 1 := by
      rw [norm_inv]
      apply inv_le_one_of_one_le₀
      have h2 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
        exact_mod_cast Complex.norm_natCast (n + 1)
      rw [h2]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h3 : ‖(-E) ^ (n + 1)‖ ≤ ‖E‖ ^ (n + 1) := by
      simpa using norm_pow_le' (-E) (Nat.succ_pos n)
    calc ‖a n‖ ≤ ‖((n + 1 : ℂ)⁻¹)‖ * ‖(-E) ^ (n + 1)‖ := norm_smul_le _ _
      _ ≤ 1 * ‖E‖ ^ (n + 1) := mul_le_mul h1 h3 (norm_nonneg _) zero_le_one
      _ = ‖E‖ ^ (n + 1) := one_mul _
  have hgeo : Summable fun n : ℕ => ‖E‖ ^ n :=
    summable_geometric_of_lt_one (norm_nonneg _) hlt
  have hsum : Summable a :=
    Summable.of_norm_bounded ((summable_nat_add_iff 1).2 hgeo) hbound
  have hlog : logSeries (1 + E) = -∑' n, a n := by
    simp only [logSeries, ha]
    congr 1
    refine tsum_congr fun n => ?_
    congr 2
    abel
  have hsplit : ∑' n, a n = a 0 + ∑' n, a (n + 1) := hsum.tsum_eq_zero_add
  have ha0 : a 0 = -E := by simp [ha]
  have htail : ‖∑' n, a (n + 1)‖ ≤ ‖E‖ ^ 2 * (1 - ‖E‖)⁻¹ := by
    refine tsum_of_norm_bounded
      ((hasSum_geometric_of_lt_one (norm_nonneg E) hlt).mul_left (‖E‖ ^ 2)) fun n => ?_
    calc ‖a (n + 1)‖ ≤ ‖E‖ ^ (n + 1 + 1) := hbound (n + 1)
      _ = ‖E‖ ^ 2 * ‖E‖ ^ n := by ring
  have hinv : (1 - ‖E‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have heq : logSeries (1 + E) - E = -∑' n, a (n + 1) := by
    rw [hlog, hsplit, ha0]
    abel
  rw [heq, norm_neg]
  calc ‖∑' n, a (n + 1)‖ ≤ ‖E‖ ^ 2 * (1 - ‖E‖)⁻¹ := htail
    _ ≤ ‖E‖ ^ 2 * 2 := by gcongr
    _ = 2 * ‖E‖ ^ 2 := mul_comm _ _
private theorem hasFDerivAt_logSeries_one (𝕜 : Type) [RCLike 𝕜] [NormedAlgebra 𝕜 ComplexMatrix2] :
    HasFDerivAt logSeries (ContinuousLinearMap.id 𝕜 ComplexMatrix2) 1 := by
  refine HasFDerivAt.of_isLittleO ?_
  have hO : (fun A : ComplexMatrix2 =>
      logSeries A - logSeries 1 - ContinuousLinearMap.id 𝕜 ComplexMatrix2 (A - 1)) =O[𝓝 1]
      fun A : ComplexMatrix2 => ‖A - 1‖ ^ 2 := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [Metric.closedBall_mem_nhds (1 : ComplexMatrix2) (by norm_num : (0 : ℝ) < 1 / 2)]
      with A hA
    have hA' : ‖A - 1‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hA
    have h := norm_logSeries_one_add_sub_le hA'
    rw [add_sub_cancel] at h
    simpa [logSeries_one] using h
  exact hO.trans_isLittleO (isLittleO_pow_sub_sub (1 : ComplexMatrix2) one_lt_two)
private theorem mul_fullTrace_smul_one_sub (A : ComplexMatrix2) :
    A * (fullTrace A • (1 : ComplexMatrix2) - A) = A.det • (1 : ComplexMatrix2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fullTrace, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring
private theorem pointwiseDerivativeRules_over (𝕜 : Type) [RCLike 𝕜]
    [NormedAlgebra 𝕜 ComplexMatrix2] [LinearMap.CompatibleSMul ComplexMatrix2 ComplexMatrix2 𝕜 ℂ] :
    PointwiseDerivativeRules.Over 𝕜 := by
  have := completeSpace_complexMatrix2
  intro I₀ X Y Z X' Y' Z' hI hX hY hZ
  refine ⟨?_, ?_, ?_⟩
  · have h := (hX.mul hY).mul hZ
    have hval : (X' * Y 0 + X 0 * Y') * Z 0 + (X * Y) 0 * Z' =
        X' * Y 0 * Z 0 + X 0 * Y' * Z 0 + X 0 * Y 0 * Z' := by
      rw [add_mul]
      rfl
    rw [hval] at h
    exact h
  · intro h1
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hnear : {A : ComplexMatrix2 | IsUnit A ∧ A ∈ logBall} ∈ 𝓝 (X 0) := by
        rw [h1]
        refine inter_mem (Units.isOpen.mem_nhds isUnit_one) ?_
        refine mem_of_superset (Metric.ball_mem_nhds (1 : ComplexMatrix2) one_pos) fun A hA => ?_
        simpa [logBall, dist_eq_norm] using hA
      exact hX.continuousAt hnear
    · have hinv := hasFDerivAt_ringInverse (𝕜 := 𝕜) (1 : ComplexMatrix2ˣ)
      have h := HasFDerivAt.comp_hasDerivAt_of_eq (0 : 𝕜) hinv hX (by simp [h1])
      have hfun : (fun t => (X t)⁻¹) = Ring.inverse ∘ X := by
        funext t
        exact Matrix.nonsing_inv_eq_ringInverse (X t)
      rw [hfun]
      exact h.congr_deriv (by simp)
    · have h := HasFDerivAt.comp_hasDerivAt_of_eq (0 : 𝕜) (hasFDerivAt_logSeries_one 𝕜) hX h1.symm
      exact h
    · intro hdet
      let L : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 :=
        (Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight (1 : ComplexMatrix2) - LinearMap.id
      let Lc : ComplexMatrix2 →L[ℂ] ComplexMatrix2 := LinearMap.toContinuousLinearMap L
      have hL : HasFDerivAt (𝕜 := 𝕜) (fun A : ComplexMatrix2 => fullTrace A • (1 : ComplexMatrix2) - A)
          (Lc.restrictScalars 𝕜) (X 0) :=
        (Lc.restrictScalars 𝕜).hasFDerivAt
      have hadj : HasDerivAt (fun t => fullTrace (X t) • (1 : ComplexMatrix2) - X t)
          (fullTrace X' • (1 : ComplexMatrix2) - X') 0 :=
        HasFDerivAt.comp_hasDerivAt (F := ComplexMatrix2) (E := ComplexMatrix2) (0 : 𝕜) hL hX
      have hprod := hX.mul hadj
      have hev : (X * fun t => fullTrace (X t) • (1 : ComplexMatrix2) - X t) =ᶠ[𝓝 (0 : 𝕜)]
          fun _ => (1 : ComplexMatrix2) := by
        filter_upwards [hI] with t ht
        rw [Pi.mul_apply, mul_fullTrace_smul_one_sub, hdet t ht, one_smul]
      have hc := (hasDerivAt_const (0 : 𝕜) (1 : ComplexMatrix2)).congr_of_eventuallyEq hev
      have hz := hprod.unique hc
      have htr : fullTrace X' = 0 := by
        simp only [h1] at hz
        have h00 := congrFun (congrFun hz 0) 0
        simp [fullTrace, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at h00
        simp only [fullTrace, Matrix.trace_fin_two]
        linear_combination h00
      exact ⟨htr, htr⟩
  · intro h0
    have hexp := hasFDerivAt_exp_zero (𝕂 := 𝕜) (𝔸 := ComplexMatrix2)
    have h := HasFDerivAt.comp_hasDerivAt_of_eq (0 : 𝕜) hexp hY h0.symm
    exact h
theorem pointwiseDerivativeRules_holds : PointwiseDerivativeRules.RealAndComplex :=
  ⟨pointwiseDerivativeRules_over ℝ, pointwiseDerivativeRules_over ℂ⟩
end YangMills.Construction.Matrices.ComplexMatrix2
end
