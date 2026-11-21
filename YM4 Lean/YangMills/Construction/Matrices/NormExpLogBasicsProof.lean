import YangMills.Construction.Lattice.NormExpAndGaugeTransportProof
import YangMills.Construction.Matrices.OperatorNormAbsoluteSeriesProof
import YangMills.Construction.Matrices.NormExpLogBasics
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices.ComplexMatrix2
private theorem norm_toEuclideanCLM_apply_le (X : ComplexMatrix2) (v : EuclideanSpace ℂ (Fin 2)) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) X v‖ ≤ ‖X‖ * ‖v‖ := by
  rw [Matrix.cstar_norm_def]
  exact ContinuousLinearMap.le_opNorm _ _
private theorem norm_entry_le (X : ComplexMatrix2) (i j : Fin 2) : ‖X i j‖ ≤ ‖X‖ := by apply _root_.YangMills.DeltaSharedProofs.p500882 <;> assumption
abbrev _root_.YangMills.SharedProofs.p14523 := @norm_entry_le
private theorem norm_eigenvalue_le (X : ComplexMatrix2) (μ : ℂ) (v : Fin 2 → ℂ) (hv : v ≠ 0)
    (h : X.mulVec v = μ • v) : ‖μ‖ ≤ ‖X‖ := by
  have hb := norm_toEuclideanCLM_apply_le X (WithLp.toLp 2 v)
  rw [Matrix.toEuclideanCLM_toLp, h, WithLp.toLp_smul, norm_smul] at hb
  have hp : 0 < ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 2))‖ := by
    rw [norm_pos_iff]
    intro h0
    exact hv (by simpa using h0)
  exact le_of_mul_le_mul_right hb hp
private theorem norm_le_two_mul_of_entries_le (X : ComplexMatrix2) (m : ℝ) (hm : 0 ≤ m)
    (h : ∀ i j, ‖X i j‖ ≤ m) : ‖X‖ ≤ 2 * m := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have row : ∀ i, ‖(Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) X x) i‖ ≤ m * (‖x 0‖ + ‖x 1‖) := by
    intro i
    have e : (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) X x) i = X i 0 * x 0 + X i 1 * x 1 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [e]
    calc ‖X i 0 * x 0 + X i 1 * x 1‖ ≤ ‖X i 0‖ * ‖x 0‖ + ‖X i 1‖ * ‖x 1‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ m * ‖x 0‖ + m * ‖x 1‖ := by
          gcongr
          · exact h i 0
          · exact h i 1
      _ = m * (‖x 0‖ + ‖x 1‖) := by ring
  have hs : ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) X x‖ ^ 2 ≤ (2 * m * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, mul_pow, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_two]
    have r0 := pow_le_pow_left₀ (norm_nonneg _) (row 0) 2
    have r1 := pow_le_pow_left₀ (norm_nonneg _) (row 1) 2
    have key : (m * (‖x 0‖ + ‖x 1‖)) ^ 2 + (m * (‖x 0‖ + ‖x 1‖)) ^ 2
        ≤ (2 * m) ^ 2 * (‖x 0‖ ^ 2 + ‖x 1‖ ^ 2) := by
      have : 0 ≤ m ^ 2 * (‖x 0‖ - ‖x 1‖) ^ 2 := by positivity
      nlinarith
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs
private theorem summable_logSeries_terms (X : ComplexMatrix2) (h : ‖X - 1‖ < 1) :
    Summable fun n : ℕ => ((n + 1 : ℂ)⁻¹) • (1 - X) ^ (n + 1) := by apply _root_.YangMills.DeltaSharedProofs.p501283 <;> assumption
theorem normExpLogBasics_holds : NormExpLogBasics := by
  have unitary_mem : ∀ {u : ComplexMatrix2}, u ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      u ∈ unitary ComplexMatrix2 :=
    fun h => h
  refine ⟨⟨fun X Y => norm_mul_le X Y, norm_one, fun X => Matrix.l2_opNorm_conjTranspose X, ?_,
    norm_entry_le, norm_eigenvalue_le, ?_, ?_, fun X Y => dist_eq_norm X Y,
    fun S hS => hS.isComplete⟩, ?_, ?_, ?_⟩
  · intro X u v hu hv
    show ‖u * X * v‖ = ‖X‖
    rw [CStarRing.norm_mul_mem_unitary _ (unitary_mem hv),
      CStarRing.norm_mem_unitary_mul _ (unitary_mem hu)]
  · intro X
    show ‖Matrix.trace X‖ ≤ 2 * ‖X‖
    rw [Matrix.trace_fin_two]
    calc _ ≤ ‖X 0 0‖ + ‖X 1 1‖ := norm_add_le _ _
      _ ≤ ‖X‖ + ‖X‖ := add_le_add (norm_entry_le X 0 0) (norm_entry_le X 1 1)
      _ = 2 * ‖X‖ := by ring
  · intro X
    have bdd : BddAbove (Set.range fun p : Fin 2 × Fin 2 => ‖X p.1 p.2‖) :=
      (Set.finite_range _).bddAbove
    refine norm_le_two_mul_of_entries_le X _ (Real.iSup_nonneg fun _ => norm_nonneg _) fun i j => ?_
    exact le_ciSup bdd (i, j)
  · intro Z
    have hexp : matExp Z * matExp (-Z) = 1 := by
      show NormedSpace.exp Z * NormedSpace.exp (-Z) = 1
      rw [Matrix.exp_neg]
      exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp Z))
    refine ⟨?_, ?_, hexp, Matrix.isUnit_exp Z, (Matrix.exp_neg Z).symm,
      (Matrix.exp_conjTranspose Z).symm, fun W hW => (Matrix.exp_conj W Z hW).symm⟩
    · simpa using NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) Z
    · simpa using NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Z
  · intro X W hX hW
    have hWW : W⁻¹ = star W := Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp hW)
    have hmul : W * W⁻¹ = 1 := by rw [hWW]; exact Matrix.mem_unitaryGroup_iff.mp hW
    have hmul' : W⁻¹ * W = 1 := by rw [hWW]; exact Matrix.mem_unitaryGroup_iff'.mp hW
    have conj_sub : W * X * W⁻¹ - 1 = W * (X - 1) * W⁻¹ := by
      rw [mul_sub, sub_mul, mul_one, hmul]
    have hnorm : operatorNorm (W * X * W⁻¹ - 1) = operatorNorm (X - 1) := by
      show ‖W * X * W⁻¹ - 1‖ = ‖X - 1‖
      rw [conj_sub, hWW]
      exact (CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem (unitary_mem hW))).trans
        (CStarRing.norm_mem_unitary_mul _ (unitary_mem hW))
    refine ⟨hnorm, ?_⟩
    have hpow : ∀ n : ℕ, (1 - W * X * W⁻¹) ^ n = W * (1 - X) ^ n * W⁻¹ := by
      intro n
      induction n with
      | zero => simp [hmul]
      | succ n ih =>
        rw [pow_succ, ih, pow_succ]
        have : 1 - W * X * W⁻¹ = W * (1 - X) * W⁻¹ := by
          rw [mul_sub, sub_mul, mul_one, hmul]
        rw [this]
        calc W * (1 - X) ^ n * W⁻¹ * (W * (1 - X) * W⁻¹)
            = W * (1 - X) ^ n * (W⁻¹ * W) * (1 - X) * W⁻¹ := by simp only [mul_assoc]
          _ = _ := by rw [hmul', mul_one]; simp only [mul_assoc]
    have hs := summable_logSeries_terms X hX
    unfold logSeries
    rw [mul_neg, neg_mul, neg_inj, ← hs.tsum_mul_left W, ← (hs.mul_left W).tsum_mul_right W⁻¹]
    refine tsum_congr fun n => ?_
    rw [hpow, mul_smul_comm, smul_mul_assoc]
  · ext A
    constructor
    · rintro ⟨B, hB, C, hC, rfl⟩
      have tB : Matrix.trace B = 0 := hB.2
      have tC : Matrix.trace C = 0 := hC.2
      show Matrix.trace _ = 0
      rw [Matrix.trace_add, Matrix.trace_smul, tB, tC]
      simp
    · intro hA
      have tA : Matrix.trace A = 0 := hA
      have tH : Matrix.trace A.conjTranspose = 0 := by
        rw [Matrix.trace_conjTranspose, tA, star_zero]
      refine ⟨(1 / 2 : ℂ) • (A + A.conjTranspose), ⟨?_, ?_⟩,
        (1 / (2 * Complex.I) : ℂ) • (A - A.conjTranspose), ⟨?_, ?_⟩, ?_⟩
      · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
          add_comm]
        simp
      · show Matrix.trace _ = 0
        rw [Matrix.trace_smul, Matrix.trace_add, tA, tH]
        simp
      · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
          Matrix.conjTranspose_conjTranspose]
        ext i j
        simp
        field_simp
        ring
      · show Matrix.trace _ = 0
        rw [Matrix.trace_smul, Matrix.trace_sub, tA, tH]
        simp
      · ext i j
        simp
        field_simp
        rw [Complex.I_sq]
        ring
end YangMills.Construction.Matrices.ComplexMatrix2
