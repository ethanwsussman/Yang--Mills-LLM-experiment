import YangMills.Construction.LinearAlgebra.ExponentialDecayOfInverseBySchurTest
import YangMills.Construction.Torus.ExactlyOneOperatorOfAPairFormProof
import YangMills.Construction.Weighted.ChainSiteSums
import YangMills.Construction.Weighted.ExpDecayInverse
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace Weighted.InverseDecay
theorem isUnit_det_of_coercive {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    {γ : ℝ} (hγ : 0 < γ)
    (hlow : ∀ v : ι → ℝ, γ * ∑ y, v y ^ 2 ≤ ∑ y, ∑ y', v y * A y y' * v y') :
    IsUnit A.det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  refine hv (funext fun z => ?_)
  have h1 : ∑ y, ∑ y', v y * A y y' * v y' = 0 := by
    refine Finset.sum_eq_zero fun y _ => ?_
    have h2 : ∑ y', A y y' * v y' = 0 := congrFun hAv y
    calc ∑ y', v y * A y y' * v y' = v y * ∑ y', A y y' * v y' := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
      _ = 0 := by rw [h2, mul_zero]
  have h3 := hlow v
  rw [h1] at h3
  have h4 : ∑ y, v y ^ 2 ≤ 0 := by
    by_contra h
    have := mul_pos hγ (not_le.1 h)
    linarith
  have h5 : v z ^ 2 ≤ ∑ y, v y ^ 2 :=
    Finset.single_le_sum (f := fun y => v y ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ z)
  have h6 : v z ^ 2 ≤ 0 := h5.trans h4
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h6 (sq_nonneg _))
section Distance
variable {D : TorusData} (B : SeparatedChain D)
end Distance
theorem latticeSumConst_half_pos {L : ℕ} (hL : 0 < L) {κ : ℝ} (hκ : 0 < κ) :
    0 < latticeSumConst 4 L (κ / 2) := by
  unfold latticeSumConst
  positivity
theorem decayRateOfInverse_pos {L : ℕ} {γ κ C : ℝ} (hL : 0 < L) (hγ : 0 < γ) (hκ : 0 < κ)
    (hC : 0 < C) : 0 < decayRateOfInverse L γ κ C := by
  have hc := latticeSumConst_half_pos hL hκ
  unfold decayRateOfInverse
  exact lt_min (by positivity) (by positivity)
end Weighted.InverseDecay
end YangMills.Construction
end
