import YangMills.Construction.HilbertSpace.CommutingPositiveProduct
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ComplexOrder
namespace YangMills.Construction.PositiveOperators.CommutingPositiveProductNonneg
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
theorem nonneg_iff_isPositiveOp (A : ℋ →L[ℂ] ℋ) : 0 ≤ A ↔ HilbertSpaceBasics.IsPositiveOp A := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff']
  constructor
  · rintro ⟨hA, h⟩
    refine ⟨hA, fun ψ => ?_⟩
    have e : ⟪ψ, A ψ⟫_ℂ = ⟪A ψ, ψ⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
        hA.star_eq]
    rw [e]
    exact h ψ
  · rintro ⟨hA, h⟩
    refine ⟨hA, fun ψ => ?_⟩
    have e : ⟪ψ, A ψ⟫_ℂ = ⟪A ψ, ψ⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
        hA.star_eq]
    rw [← e]
    exact h ψ
theorem list_prod_nonneg_of_pairwise_commute (l : List (ℋ →L[ℂ] ℋ)) (hc : l.Pairwise Commute)
    (hp : ∀ A ∈ l, 0 ≤ A) : 0 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons A t ih =>
    rw [List.pairwise_cons] at hc
    rw [List.prod_cons]
    exact Commute.mul_nonneg (hp A (by simp))
      (ih hc.2 fun B hB => hp B (by simp [hB]))
      (Commute.list_prod_right t A hc.1)
theorem commutingPositiveProduct_holds : CommutingPositiveProduct := by
  intro ℋ _ _ _ J _ A hc hp
  rw [← nonneg_iff_isPositiveOp]
  refine list_prod_nonneg_of_pairwise_commute _ ?_ ?_
  · rw [List.pairwise_ofFn]
    exact fun i j hij => hc hij.ne
  · intro B hB
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hB
    exact (nonneg_iff_isPositiveOp _).mpr (hp i)
end YangMills.Construction.PositiveOperators.CommutingPositiveProductNonneg
