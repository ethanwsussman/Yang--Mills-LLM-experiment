import YangMills.Construction.Lattice.NormExpAndGaugeTransportProof
import YangMills.Construction.Matrices.NormExpLogConjugation
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices.ComplexMatrix2
namespace NormExpLogConj
theorem unitary_inv_mem {g : ComplexMatrix2} (hg : g ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    g⁻¹ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have h : g⁻¹ = star g := Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp hg)
  rw [h, Matrix.mem_unitaryGroup_iff, star_star]
  exact Matrix.mem_unitaryGroup_iff'.mp hg
theorem mul_inv_eq_one_of_isUnit {g : ComplexMatrix2} (hg : IsUnit g) : g * g⁻¹ = 1 :=
  Matrix.mul_nonsing_inv g ((Matrix.isUnit_iff_isUnit_det g).mp hg)
theorem inv_mul_eq_one_of_isUnit {g : ComplexMatrix2} (hg : IsUnit g) : g⁻¹ * g = 1 :=
  Matrix.nonsing_inv_mul g ((Matrix.isUnit_iff_isUnit_det g).mp hg)
theorem operatorNorm_unitary_mul_mul {X u v : ComplexMatrix2}
    (hu : u ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hv : v ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    operatorNorm (u * X * v) = operatorNorm X := by
  show ‖u * X * v‖ = ‖X‖
  rw [CStarRing.norm_mul_mem_unitary _ hv, CStarRing.norm_mem_unitary_mul _ hu]
theorem conj_sub_one_eq {g : ComplexMatrix2} (hg : IsUnit g) (X : ComplexMatrix2) :
    g * X * g⁻¹ - 1 = g * (X - 1) * g⁻¹ := by
  rw [mul_sub, sub_mul, mul_one, mul_inv_eq_one_of_isUnit hg]
theorem operatorNorm_conj_sub_one {X g : ComplexMatrix2}
    (hg : g ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    operatorNorm (g * X * g⁻¹ - 1) = operatorNorm (X - 1) := by
  have hunit : IsUnit g :=
    IsUnit.of_mul_eq_one _ (Matrix.mem_unitaryGroup_iff.mp hg)
  rw [conj_sub_one_eq hunit]
  exact operatorNorm_unitary_mul_mul hg (unitary_inv_mem hg)
theorem operatorNorm_inv_sub_one {V : ComplexMatrix2} (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    operatorNorm (V⁻¹ - 1) = operatorNorm (V - 1) := by
  have hunit : IsUnit V :=
    IsUnit.of_mul_eq_one _ (Matrix.mem_unitaryGroup_iff.mp hV)
  have h : V⁻¹ - 1 = V⁻¹ * (-(V - 1)) := by
    rw [mul_neg, mul_sub, inv_mul_eq_one_of_isUnit hunit, mul_one, neg_sub]
  show ‖V⁻¹ - 1‖ = ‖V - 1‖
  rw [h, CStarRing.norm_mem_unitary_mul _ (unitary_inv_mem hV), norm_neg]
theorem conj_pow_eq {g : ComplexMatrix2} (hg : IsUnit g) (Y : ComplexMatrix2) (n : ℕ) :
    (g * Y * g⁻¹) ^ n = g * Y ^ n * g⁻¹ := by
  induction n with
  | zero => simp [mul_inv_eq_one_of_isUnit hg]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    calc g * Y ^ n * g⁻¹ * (g * Y * g⁻¹) = g * Y ^ n * (g⁻¹ * g) * Y * g⁻¹ := by
          simp only [mul_assoc]
      _ = g * (Y ^ n * Y) * g⁻¹ := by
          rw [inv_mul_eq_one_of_isUnit hg, mul_one]
          simp only [mul_assoc]
theorem summable_logSeries_terms {X : ComplexMatrix2} (hX : operatorNorm (X - 1) < 1) :
    Summable fun n : ℕ => ((n + 1 : ℂ)⁻¹) • (1 - X) ^ (n + 1) := by apply _root_.YangMills.SharedProofs.p26260 <;> assumption
theorem logSeries_conj {g X : ComplexMatrix2} (hg : IsUnit g) (hX : operatorNorm (X - 1) < 1) :
    logSeries (g * X * g⁻¹) = g * logSeries X * g⁻¹ := by
  have hone : 1 - g * X * g⁻¹ = g * (1 - X) * g⁻¹ := by
    rw [mul_sub, sub_mul, mul_one, mul_inv_eq_one_of_isUnit hg]
  have hterm : ∀ n : ℕ, ((n + 1 : ℂ)⁻¹) • (1 - g * X * g⁻¹) ^ (n + 1) =
      g * (((n + 1 : ℂ)⁻¹) • (1 - X) ^ (n + 1)) * g⁻¹ := by
    intro n
    rw [hone, conj_pow_eq hg, mul_smul_comm, smul_mul_assoc]
  have hs := summable_logSeries_terms hX
  unfold logSeries
  simp only [hterm]
  rw [(hs.mul_left g).tsum_mul_right, hs.tsum_mul_left, mul_neg, neg_mul]
end NormExpLogConj
theorem normExpLogConjugation_holds : NormExpLogConjugation := by
  refine ⟨fun X Z => norm_mul_le X Z, norm_one, fun X u v hu hv => ?_, fun X g hg => ?_,
    fun V hV => ?_, fun g Z hg => ?_, fun g X hg hX _ => ?_, fun g X hg hX => ?_⟩
  · exact NormExpLogConj.operatorNorm_unitary_mul_mul hu hv
  · exact NormExpLogConj.operatorNorm_conj_sub_one hg
  · exact NormExpLogConj.operatorNorm_inv_sub_one hV
  · exact Matrix.exp_conj g Z hg
  · exact NormExpLogConj.logSeries_conj hg hX
  · rw [NormExpLogConj.operatorNorm_conj_sub_one hg]
    exact hX
end YangMills.Construction.Matrices.ComplexMatrix2
