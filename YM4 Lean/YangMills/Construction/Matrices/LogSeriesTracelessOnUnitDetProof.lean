import YangMills.Construction.Lattice.DomainsOfTheTwoSchemesProof
import YangMills.Construction.Matrices.LogSeriesTracelessOnUnitDet
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices.ComplexMatrix2
namespace TracelessLogSeries
theorem mul_self_eq_trace_smul_sub_det_smul (E : ComplexMatrix2) :
    E * E = fullTrace E • E - E.det • (1 : ComplexMatrix2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two,
      fullTrace] <;> ring
theorem fullTrace_pow_eq_power_sums (E : ComplexMatrix2) (μ ν : ℂ) (hs : μ + ν = fullTrace E)
    (hp : μ * ν = E.det) (n : ℕ) :
    fullTrace (E ^ n) = μ ^ n + ν ^ n ∧
      fullTrace (E ^ (n + 1)) = μ ^ (n + 1) + ν ^ (n + 1) := by apply _root_.YangMills.DeltaSharedProofs.p501865 <;> assumption
theorem norm_charpoly_root_le (E : ComplexMatrix2) (μ : ℂ)
    (h : μ * μ - fullTrace E * μ + E.det = 0) : ‖μ‖ ≤ ‖E‖ := by
  have hdet : (algebraMap ℂ ComplexMatrix2 μ - E).det = 0 := by
    rw [← h]
    simp [Matrix.det_fin_two, Matrix.trace_fin_two, fullTrace, Matrix.algebraMap_matrix_apply]
    ring
  have hmem : μ ∈ spectrum ℂ E := by
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, hdet]
    exact not_isUnit_zero
  exact spectrum.norm_le_norm_of_mem hmem
theorem hasSum_neg_log_one_sub {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => ((n + 1 : ℂ)⁻¹) * z ^ (n + 1)) (-Complex.log (1 - z)) := by
  have h := Complex.hasSum_taylorSeries_neg_log hz
  have h' := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, div_zero, sub_zero] at h'
  have he : (fun n : ℕ => ((n + 1 : ℂ)⁻¹) * z ^ (n + 1)) =
      fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) := by
    funext n
    push_cast
    rw [div_eq_inv_mul]
  rw [he]
  exact h'
theorem log_add_log_eq_zero_of_mul_eq_one {a b : ℂ} (hab : a * b = 1) (ha : 0 < a.re) :
    Complex.log a + Complex.log b = 0 := by
  have hb : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab
  have harg : a.arg ≠ Real.pi := by
    intro h
    have h₁ := Complex.arg_eq_pi_iff.mp h
    exact absurd h₁.1 (not_lt.mpr ha.le)
  rw [hb, Complex.log_inv a harg]
  ring
theorem re_one_sub_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (1 - z).re := by
  have := (Complex.abs_re_le_norm z).trans_lt hz
  have h := (abs_lt.mp this).2
  simp only [Complex.sub_re, Complex.one_re]
  linarith
end TracelessLogSeries
open TracelessLogSeries in
theorem logSeriesTracelessOfUnitDet_holds : LogSeriesTracelessOfUnitDet := by
  intro X hdet hdom
  have hX : X.det = 1 := hdet
  set E : ComplexMatrix2 := 1 - X with hEdef
  have hE : ‖E‖ < 1 := by
    have h : ‖X - 1‖ < 1 := hdom
    rwa [norm_sub_rev] at h
  obtain ⟨s, hs⟩ :=
    IsAlgClosed.exists_pow_nat_eq (fullTrace E ^ 2 - 4 * E.det) (n := 2) (by norm_num)
  set μ : ℂ := (fullTrace E + s) / 2 with hμ
  set ν : ℂ := (fullTrace E - s) / 2 with hν
  have hsum : μ + ν = fullTrace E := by rw [hμ, hν]; ring
  have hprod : μ * ν = E.det := by
    rw [hμ, hν]
    linear_combination (-1 / 4 : ℂ) * hs
  have hμr : μ * μ - fullTrace E * μ + E.det = 0 := by
    rw [← hsum, ← hprod]; ring
  have hνr : ν * ν - fullTrace E * ν + E.det = 0 := by
    rw [← hsum, ← hprod]; ring
  have hμ1 : ‖μ‖ < 1 := (norm_charpoly_root_le E μ hμr).trans_lt hE
  have hν1 : ‖ν‖ < 1 := (norm_charpoly_root_le E ν hνr).trans_lt hE
  have hXE : X = 1 - E := by rw [hEdef]; abel
  have hdetE : (1 - E).det = 1 - fullTrace E + E.det := by
    simp [Matrix.det_fin_two, Matrix.trace_fin_two, fullTrace]
    ring
  have hinv : (1 - μ) * (1 - ν) = 1 := by
    have h₁ : (1 : ℂ) - fullTrace E + E.det = 1 := by rw [← hdetE, ← hXE, hX]
    linear_combination h₁ - hsum + hprod
  have hsummable : Summable fun n : ℕ => ((n + 1 : ℂ)⁻¹) • (1 - X) ^ (n + 1) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => ‖E‖ ^ (n + 1)) ?_ ?_
    · exact (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hE)
    · intro n
      rw [norm_smul, norm_inv]
      have h₁ : ‖(n + 1 : ℂ)‖⁻¹ ≤ 1 := by
        apply inv_le_one_of_one_le₀
        have : ‖(n + 1 : ℂ)‖ = (n : ℝ) + 1 := by
          have h₂ : (n + 1 : ℂ) = ((n + 1 : ℕ) : ℂ) := by push_cast; rfl
          rw [h₂, Complex.norm_natCast]
          push_cast
          rfl
        rw [this]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have h₂ : ‖(1 - X) ^ (n + 1)‖ ≤ ‖E‖ ^ (n + 1) := norm_pow_le _ _
      calc ‖(n + 1 : ℂ)‖⁻¹ * ‖(1 - X) ^ (n + 1)‖ ≤ 1 * ‖E‖ ^ (n + 1) :=
            mul_le_mul h₁ h₂ (norm_nonneg _) zero_le_one
        _ = ‖E‖ ^ (n + 1) := one_mul _
  have htr : HasSum (fun n : ℕ => fullTrace (((n + 1 : ℂ)⁻¹) • (1 - X) ^ (n + 1)))
      (fullTrace (∑' n : ℕ, ((n + 1 : ℂ)⁻¹) • (1 - X) ^ (n + 1))) := by
    have hc : Continuous (Matrix.traceLinearMap (Fin 2) ℂ ℂ) :=
      LinearMap.continuous_of_finiteDimensional _
    exact hsummable.hasSum.map (Matrix.traceLinearMap (Fin 2) ℂ ℂ) hc
  have hterms : (fun n : ℕ => fullTrace (((n + 1 : ℂ)⁻¹) • (1 - X) ^ (n + 1))) =
      fun n : ℕ => ((n + 1 : ℂ)⁻¹) * μ ^ (n + 1) + ((n + 1 : ℂ)⁻¹) * ν ^ (n + 1) := by
    funext n
    have h := (fullTrace_pow_eq_power_sums E μ ν hsum hprod n).2
    have h' : fullTrace (((n + 1 : ℂ)⁻¹) • E ^ (n + 1)) =
        ((n + 1 : ℂ)⁻¹) * fullTrace (E ^ (n + 1)) := by
      simp [fullTrace, Matrix.trace_smul]
    rw [h', h]
    ring
  rw [hterms] at htr
  have hval := htr.unique ((hasSum_neg_log_one_sub hμ1).add (hasSum_neg_log_one_sub hν1))
  show fullTrace (logSeries X) = 0
  have hneg : fullTrace (logSeries X) =
      -fullTrace (∑' n : ℕ, ((n + 1 : ℂ)⁻¹) • (1 - X) ^ (n + 1)) := by
    simp [logSeries, fullTrace, Matrix.trace_neg]
  rw [hneg, hval]
  have hlog := log_add_log_eq_zero_of_mul_eq_one hinv (re_one_sub_pos hμ1)
  linear_combination hlog
end YangMills.Construction.Matrices.ComplexMatrix2
