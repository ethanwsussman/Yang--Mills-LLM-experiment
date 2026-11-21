import YangMills.Construction.Averaging.MeanOfTheConstantFamily
import YangMills.Construction.Matrices.ExpLogEstimates
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Averaging
open Matrices PeriodicLattice
private theorem logSeries_one : ComplexMatrix2.logSeries 1 = 0 := by
  simp [ComplexMatrix2.logSeries]
private theorem det_eq_one_of_mem {H : Set ComplexMatrix2}
    (hH : H = compactGaugeGroup ∨ H = complexGaugeGroup) {W : ComplexMatrix2}
    (hW : W ∈ H) : W.det = 1 := by
  rcases hH with rfl | rfl
  · exact (Matrix.mem_specialUnitaryGroup_iff.mp hW).2
  · exact hW
private theorem one_mem_gaugeGroup {H : Set ComplexMatrix2}
    (hH : H = compactGaugeGroup ∨ H = complexGaugeGroup) :
    (1 : ComplexMatrix2) ∈ H := by
  rcases hH with rfl | rfl
  · exact one_mem (ComplexMatrix2.specialUnitary)
  · exact Matrix.det_one
private theorem isLogMean_one (n : ℕ) {H : Set ComplexMatrix2}
    (hH : H = compactGaugeGroup ∨ H = complexGaugeGroup) :
    ComplexMatrix2.IsLogMean H (identityFamily n) 1 := by
  refine ⟨one_mem_gaugeGroup hH, fun i => ?_, ?_⟩
  · simp [identityFamily, ComplexMatrix2.operatorNorm]
  · simp [identityFamily, logSeries_one]
private theorem eq_one_of_isLogMean (h : ComplexMatrix2.ExpLogEstimates) {n : ℕ} (hn : 1 ≤ n)
    {H : Set ComplexMatrix2} (hH : H = compactGaugeGroup ∨ H = complexGaugeGroup)
    {W : ComplexMatrix2}
    (hW : ComplexMatrix2.IsLogMean H (identityFamily n) W) : W = 1 := by
  obtain ⟨hmem, hclose, hsum⟩ := hW
  have hnear : ComplexMatrix2.operatorNorm (W⁻¹ - 1) < 1 := by
    simpa [identityFamily] using hclose ⟨0, hn⟩
  have hlog : ComplexMatrix2.logSeries W⁻¹ = 0 := by
    have hs : (n : ℂ) • ComplexMatrix2.logSeries W⁻¹ = 0 := by
      simpa [identityFamily, Nat.cast_smul_eq_nsmul] using hsum
    have hne : (n : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
    exact (smul_eq_zero.mp hs).resolve_left hne
  have hexp := (h.2.2.2.1 (W⁻¹ - 1) hnear).2.2.2.2
  have hinv : W⁻¹ = 1 := by
    rw [add_sub_cancel, hlog] at hexp
    simpa using hexp.symm
  have hunit : IsUnit W.det := by
    rw [det_eq_one_of_mem hH hmem]
    exact isUnit_one
  simpa [hinv] using Matrix.mul_nonsing_inv W hunit
theorem identityFamilyMeanIsOne_of_expLogEstimates (h : ComplexMatrix2.ExpLogEstimates) :
    IdentityFamilyMeanIsOne := by
  intro n hn
  have hOnly : ∀ H : Set ComplexMatrix2, (H = compactGaugeGroup ∨ H = complexGaugeGroup) →
      ∀ W, ComplexMatrix2.IsLogMean H (identityFamily n) W ↔ W = 1 := fun H hH W =>
    ⟨eq_one_of_isLogMean h hn hH, fun e => e ▸ isLogMean_one n hH⟩
  refine ⟨?_, fun H hH => ⟨hOnly H hH, ?_, ?_⟩, ?_⟩
  · simp [ComplexMatrix2.familyDiameter, identityFamily, ComplexMatrix2.operatorNorm]
  · exact ⟨1, isLogMean_one n hH, fun W hW => (hOnly H hH W).1 hW⟩
  · exact (hOnly H hH _).1 (Classical.epsilon_spec (⟨1, isLogMean_one n hH⟩ :
      ∃ W, ComplexMatrix2.IsLogMean H (identityFamily n) W))
  · have hnear : ComplexMatrix2.IsLogMean complexGaugeGroup (identityFamily n) 1 ∧
        ∃ i, ComplexMatrix2.operatorNorm (identityFamily n i * (1 : ComplexMatrix2)⁻¹ - 1) ≤
          complexMeanTolerance :=
      ⟨isLogMean_one n (Or.inr rfl), ⟨0, hn⟩, by
        simp [identityFamily, ComplexMatrix2.operatorNorm, complexMeanTolerance]⟩
    have hchosen := Classical.epsilon_spec (p := fun W => ComplexMatrix2.IsLogMean
      complexGaugeGroup (identityFamily n) W ∧
        ∃ i, ComplexMatrix2.operatorNorm (identityFamily n i * W⁻¹ - 1) ≤ complexMeanTolerance)
      ⟨1, hnear⟩
    exact (hOnly complexGaugeGroup (Or.inr rfl) _).1 hchosen.1
end YangMills.Construction.Averaging
