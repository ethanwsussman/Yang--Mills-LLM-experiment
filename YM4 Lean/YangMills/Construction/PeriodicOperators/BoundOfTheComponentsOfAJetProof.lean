import YangMills.Construction.PeriodicOperators.BoundOfTheComponentsOfAJet
import YangMills.Construction.PeriodicOperators.NormOfAMatrixWithABoundedKernelOfFiniteValence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetComponentBound
theorem norm_relPhase_le (I I' : PeriodicData) (κ : Fin 4 → ℂ) (r : ℝ) (j : I'.Carrier)
    (i : I.Carrier) (h : WithinBox r (I.pos i) (I'.pos j)) :
    ‖relPhase I I' κ j i‖ ≤ Real.exp (∑ μ, |(κ μ).im| * r) := by
  unfold relPhase
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (Complex.I * bilinDot κ (toComplexVec (I.pos i - I'.pos j))).re =
      ∑ μ, -((κ μ).im * (I.pos i μ - I'.pos j μ)) := by
    rw [Complex.I_mul_re]
    simp only [bilinDot, toComplexVec, Complex.im_sum, Pi.sub_apply, Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Complex.im_mul_ofReal]
  rw [hre]
  refine Finset.sum_le_sum fun μ _ => ?_
  calc -((κ μ).im * (I.pos i μ - I'.pos j μ))
      ≤ |(κ μ).im * (I.pos i μ - I'.pos j μ)| := neg_le_abs _
    _ = |(κ μ).im| * |I.pos i μ - I'.pos j μ| := abs_mul _ _
    _ ≤ |(κ μ).im| * r := mul_le_mul_of_nonneg_left (h μ) (abs_nonneg _)
theorem withinBox_translate {I I' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (r : ℝ) (n : Fin 4 → ℤ) (j : I'.Carrier) (i : I.Carrier)
    (h : WithinBox r (I.pos i) (I'.pos j)) :
    WithinBox r (I.pos (I.translate n i)) (I'.pos (I'.translate n j)) := by
  intro μ
  rw [hI.pos_translate, hI'.pos_translate]
  have := h μ
  simpa using this
theorem quotHomNorm_le_of_coeff
    (hMatrix : FiniteValenceNorm.Claim)
    {I I' : PeriodicData} (hI : IsPeriodic I) (hI' : IsPeriodic I') (w : ℝ)
    (hw : ∀ i, I.weightOf i = w) (hw' : ∀ j, I'.weightOf j = w) (r β : ℝ) (N : ℕ) (hβ : 0 ≤ β)
    (hrow : ∀ j, {i | WithinBox r (I.pos i) (I'.pos j)}.encard ≤ N)
    (hcol : ∀ i, {j | WithinBox r (I.pos i) (I'.pos j)}.encard ≤ N)
    (κ : Fin 4 → ℂ) (M : QuotHom I I') (c : I'.Carrier → I.Carrier → ℂ)
    (hzero : ∀ j i, ¬ WithinBox r (I.pos i) (I'.pos j) → c j i = 0)
    (hbound : ∀ j i, WithinBox r (I.pos i) (I'.pos j) → ‖c j i‖ ≤ β)
    (hM : ∀ (φ : I.UnitQuot → ℂ) j,
      M φ (I'.mkQuot 1 j) = ∑' i, relPhase I I' κ j i * c j i * φ (I.mkQuot 1 i)) :
    quotHomNorm M ≤ ENNReal.ofReal (N * (Real.exp (∑ μ, |(κ μ).im| * r) * β)) := by
  have hnonneg : 0 ≤ Real.exp (∑ μ, |(κ μ).im| * r) * β := mul_nonneg (Real.exp_pos _).le hβ
  refine hMatrix I I' hI hI' w hw hw' M (fun j i => relPhase I I' κ j i * c j i)
    (fun j i => WithinBox r (I.pos i) (I'.pos j)) N _ hnonneg
    (fun n j i h => withinBox_translate hI hI' r n j i h) hrow hcol ?_ ?_ hM
  · intro j i
    by_cases h : WithinBox r (I.pos i) (I'.pos j)
    · rw [norm_mul]
      exact mul_le_mul (norm_relPhase_le I I' κ r j i h) (hbound j i h) (norm_nonneg _)
        (Real.exp_pos _).le
    · simpa [hzero j i h] using hnonneg
  · intro j i h
    simp [hzero j i h]
theorem claim_holds (hMatrix : FiniteValenceNorm.Claim)
    (hRows : JetExpansions.Claim) : JetComponentBound.Claim := by
  intro F I I' hF hI hI' T hT w hw hw' r β N hβ hrow hcol p εa εb hzero hbound κ
  have key := quotHomNorm_le_of_coeff hMatrix hI hI' w hw hw' r β N hβ hrow hcol κ
  refine ⟨key _ _ (fun j i h => (hzero j i h).1) (fun j i h => (hbound j i h).1)
      fun φ j => (hRows F I I' hF hI hI' T hT p κ εa εb φ j).1,
    key _ _ (fun j i h => (hzero j i h).2.1) (fun j i h => (hbound j i h).2.1)
      fun φ j => (hRows F I I' hF hI hI' T hT p κ εa εb φ j).2.1,
    key _ _ (fun j i h => (hzero j i h).2.2) (fun j i h => (hbound j i h).2.2)
      fun φ j => (hRows F I I' hF hI hI' T hT p κ εa εb φ j).2.2⟩
end YangMills.Construction.PeriodicOperators.JetComponentBound
end
