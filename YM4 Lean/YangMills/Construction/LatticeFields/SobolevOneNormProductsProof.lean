import YangMills.Construction.LatticeFields.SobolevOneNormProducts
import Mathlib
namespace YangMills.Construction.LatticeFields
theorem SobolevOneNormProducts.claim_holds : SobolevOneNormProducts.Claim := by
  intro d N r ℓ hℓ _ hr F F'
  have hX := sobolevOneNorm_sq hr F'
  have hY := sobolevOneNorm_sq hr F
  have hX0 : 0 ≤ sobolevOneNorm hr F' := Real.sqrt_nonneg _
  have hY0 : 0 ≤ sobolevOneNorm hr F := Real.sqrt_nonneg _
  generalize sobolevOneNorm hr F' = X at *
  generalize sobolevOneNorm hr F = Y at *
  generalize fieldNorm F' = a at *
  generalize fieldNorm F = c at *
  generalize fieldNorm (tensorGrad F') = b at *
  generalize fieldNorm (tensorGrad F) = e at *
  have hXY : 0 ≤ X * Y := mul_nonneg hX0 hY0
  have hsq : (X * Y) ^ 2 = (b ^ 2 + a ^ 2) * (e ^ 2 + c ^ 2) := by rw [mul_pow, hX, hY]
  refine ⟨(abs_le_of_sq_le_sq' ?_ hXY).2, (abs_le_of_sq_le_sq' ?_ hXY).2,
    (abs_le_of_sq_le_sq' ?_ hXY).2⟩
  · rw [hsq]; nlinarith [sq_nonneg (b * e - a * c)]
  · rw [hsq]; nlinarith [sq_nonneg (b * e), sq_nonneg (b * c), sq_nonneg (a * e)]
  · rw [hsq]; nlinarith [sq_nonneg (a * c), sq_nonneg (b * c), sq_nonneg (a * e)]
end YangMills.Construction.LatticeFields
