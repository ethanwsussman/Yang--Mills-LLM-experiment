import YangMills.Construction.Matrices.LogMeanCovariance
import YangMills.Construction.Matrices.LogarithmicChartsOfASpaceOfConfigurationsProof
import YangMills.Construction.Matrices.OperatorNormUnderConjugation
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices.ComplexMatrix2
private theorem isUnit_of_mem_specialUnitarySet {A : ComplexMatrix2}
    (hA : A ∈ (specialUnitary : Set ComplexMatrix2)) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).mpr (by
    rw [(Matrix.mem_specialUnitaryGroup_iff.mp hA).2]
    exact isUnit_one)
abbrev _root_.YangMills.SharedProofs.p13429 := @isUnit_of_mem_specialUnitarySet
private theorem mul_inv_of_mem_specialUnitarySet {A : ComplexMatrix2}
    (hA : A ∈ (specialUnitary : Set ComplexMatrix2)) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp (isUnit_of_mem_specialUnitarySet hA))
private theorem inv_mul_of_mem_specialUnitarySet {A : ComplexMatrix2}
    (hA : A ∈ (specialUnitary : Set ComplexMatrix2)) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp (isUnit_of_mem_specialUnitarySet hA))
private theorem inv_mem_specialUnitarySet {A : ComplexMatrix2}
    (hA : A ∈ (specialUnitary : Set ComplexMatrix2)) :
    A⁻¹ ∈ (specialUnitary : Set ComplexMatrix2) := by apply _root_.YangMills.SharedProofs.p33390 <;> assumption
private theorem mul_mul_mem_specialUnitarySet {A B C : ComplexMatrix2}
    (hA : A ∈ (specialUnitary : Set ComplexMatrix2))
    (hB : B ∈ (specialUnitary : Set ComplexMatrix2))
    (hC : C ∈ (specialUnitary : Set ComplexMatrix2)) :
    A * B * C ∈ (specialUnitary : Set ComplexMatrix2) :=
  specialUnitary.mul_mem (specialUnitary.mul_mem hA hB) hC
private theorem sandwich_mul_sandwich_inv {W W' : ComplexMatrix2}
    (hW' : W' ∈ (specialUnitary : Set ComplexMatrix2)) (X Y : ComplexMatrix2) :
    (W * Y * W') * (W * X * W')⁻¹ = W * (Y * X⁻¹) * W⁻¹ := by
  have cancel : ∀ Z : ComplexMatrix2, W' * (W'⁻¹ * Z) = Z := fun Z => by
    rw [← mul_assoc, mul_inv_of_mem_specialUnitarySet hW', one_mul]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [mul_assoc]
  rw [cancel]
theorem logMeanCovariance_holds (h : OperatorNormUnderConjugation) :
    LogMeanCovariance := by
  obtain ⟨-, hconj, -, -, -, hlog, -⟩ := h
  have hdist : ∀ W Y : ComplexMatrix2, W ∈ (specialUnitary : Set ComplexMatrix2) →
      operatorNorm (W * Y * W⁻¹ - 1) = operatorNorm (Y - 1) := by
    intro W Y hW
    have e : W * Y * W⁻¹ - 1 = W * (Y - 1) * W⁻¹ := by
      rw [mul_sub, sub_mul, mul_one, mul_inv_of_mem_specialUnitarySet hW]
    rw [e]
    exact hconj _ _ (Matrix.specialUnitaryGroup_le_unitaryGroup hW)
  have mean_iff : ∀ (ι : Type) [Fintype ι] (V : ι → ComplexMatrix2) (W W' X : ComplexMatrix2),
      W ∈ (specialUnitary : Set ComplexMatrix2) → W' ∈ (specialUnitary : Set ComplexMatrix2) →
      X ∈ (specialUnitary : Set ComplexMatrix2) →
      (IsLogMean (specialUnitary : Set ComplexMatrix2) V X ↔
        IsLogMean (specialUnitary : Set ComplexMatrix2) (fun i => W * V i * W') (W * X * W')) := by
    intro ι _ V W W' X hW hW' hX
    have bound : ∀ i, operatorNorm ((W * V i * W') * (W * X * W')⁻¹ - 1) =
        operatorNorm (V i * X⁻¹ - 1) := by
      intro i
      rw [sandwich_mul_sandwich_inv hW', hdist _ _ hW]
    have total : (∀ i, operatorNorm (V i * X⁻¹ - 1) < 1) →
        ∑ i, logSeries ((W * V i * W') * (W * X * W')⁻¹) =
          W * (∑ i, logSeries (V i * X⁻¹)) * W⁻¹ := by
      intro hb
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sandwich_mul_sandwich_inv hW']
      exact hlog W _ (isUnit_of_mem_specialUnitarySet hW) (hb i) (by rw [hdist _ _ hW]; exact hb i)
    constructor
    · rintro ⟨-, hb, hs⟩
      refine ⟨mul_mul_mem_specialUnitarySet hW hX hW', fun i => lt_of_eq_of_lt (bound i) (hb i), ?_⟩
      change ∑ i, logSeries ((W * V i * W') * (W * X * W')⁻¹) = 0
      rw [total hb, hs, mul_zero, zero_mul]
    · rintro ⟨-, hb, hs⟩
      have hb' : ∀ i, operatorNorm (V i * X⁻¹ - 1) < 1 := fun i =>
        lt_of_eq_of_lt (bound i).symm (hb i)
      refine ⟨hX, hb', ?_⟩
      have hs' : ∑ i, logSeries ((W * V i * W') * (W * X * W')⁻¹) = 0 := hs
      rw [total hb'] at hs'
      have back : ∀ S : ComplexMatrix2, W⁻¹ * (W * S * W⁻¹) * W = S := fun S => by
        simp only [mul_assoc]
        rw [inv_mul_of_mem_specialUnitarySet hW, mul_one, ← mul_assoc,
          inv_mul_of_mem_specialUnitarySet hW, one_mul]
      rw [← back (∑ i, logSeries (V i * X⁻¹)), hs', mul_zero, zero_mul]
  have one_mean : ∀ (ι : Type) [Fintype ι] (V : ι → ComplexMatrix2) (W W' : ComplexMatrix2),
      W ∈ (specialUnitary : Set ComplexMatrix2) → W' ∈ (specialUnitary : Set ComplexMatrix2) →
      HasUniqueLogMean (specialUnitary : Set ComplexMatrix2) V →
      HasUniqueLogMean (specialUnitary : Set ComplexMatrix2) (fun i => W * V i * W') := by
    rintro ι _ V W W' hW hW' ⟨X, hX, hu⟩
    have hX' : IsLogMean (specialUnitary : Set ComplexMatrix2) V X := hX
    refine ExistsUnique.intro (W * X * W') ((mean_iff ι V W W' X hW hW' hX'.1).mp hX') ?_
    intro Y hY
    have hYG : Y ∈ (specialUnitary : Set ComplexMatrix2) := hY.1
    have hPre : W⁻¹ * Y * W'⁻¹ ∈ (specialUnitary : Set ComplexMatrix2) :=
      mul_mul_mem_specialUnitarySet (inv_mem_specialUnitarySet hW) hYG
        (inv_mem_specialUnitarySet hW')
    have back : W * (W⁻¹ * Y * W'⁻¹) * W' = Y := by
      simp only [mul_assoc]
      rw [inv_mul_of_mem_specialUnitarySet hW', mul_one, ← mul_assoc,
        mul_inv_of_mem_specialUnitarySet hW, one_mul]
    have hm : IsLogMean (specialUnitary : Set ComplexMatrix2) V (W⁻¹ * Y * W'⁻¹) :=
      (mean_iff ι V W W' _ hW hW' hPre).mpr (by rw [back]; exact hY)
    rw [← back, hu _ hm]
  intro ι _ V W W' _ hW hW'
  refine ⟨fun X hX => mean_iff ι V W W' X hW hW' hX, ⟨one_mean ι V W W' hW hW', fun h₁ => ?_⟩,
    fun h₁ => ?_⟩
  · have h₂ : HasUniqueLogMean (specialUnitary : Set ComplexMatrix2)
        (fun i => W⁻¹ * (W * V i * W') * W'⁻¹) :=
      one_mean ι (fun i => W * V i * W') W⁻¹ W'⁻¹ (inv_mem_specialUnitarySet hW)
        (inv_mem_specialUnitarySet hW') h₁
    have e : (fun i => W⁻¹ * (W * V i * W') * W'⁻¹) = V := by
      funext i
      simp only [mul_assoc]
      rw [mul_inv_of_mem_specialUnitarySet hW', mul_one, ← mul_assoc,
        inv_mul_of_mem_specialUnitarySet hW, one_mul]
    rwa [e] at h₂
  · have h₂ := one_mean ι V W W' hW hW' h₁
    obtain ⟨X, hX, -⟩ := h₁
    have hAv : IsLogMean (specialUnitary : Set ComplexMatrix2) V
        (logMean (specialUnitary : Set ComplexMatrix2) V) :=
      Classical.epsilon_spec ⟨X, hX⟩
    obtain ⟨Y, hY, hu⟩ := h₂
    have hAv₂ : IsLogMean (specialUnitary : Set ComplexMatrix2) (fun i => W * V i * W')
        (logMean (specialUnitary : Set ComplexMatrix2) (fun i => W * V i * W')) :=
      Classical.epsilon_spec ⟨Y, hY⟩
    rw [hu _ hAv₂, hu _ ((mean_iff ι V W W' _ hW hW' hAv.1).mp hAv)]
end YangMills.Construction.Matrices.ComplexMatrix2
