import YangMills.Construction.LinearAlgebra.SymmetricOperatorOfBilinForm
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SymmetricOperator
theorem symmetric_eq_of_diagonal_eq : SymmetricEqOfDiagonalEq := by
  intro X _ _ T T' hT hT' hd
  have hS : (T - T').IsSymmetric := fun x y => by
    simp only [LinearMap.sub_apply, inner_sub_left, inner_sub_right, hT x y, hT' x y]
  have hz : ∀ v : X, inner ℝ v ((T - T') v) = 0 := fun v => by
    simp only [LinearMap.sub_apply, inner_sub_right, hd v, sub_self]
  have hvw : ∀ v w : X, inner ℝ v ((T - T') w) = 0 := fun v w => by
    have h1 := hz (v + w)
    have h2 := hz (v - w)
    have h3 : inner ℝ w ((T - T') v) = inner ℝ v ((T - T') w) := by
      rw [← hS w v, real_inner_comm]
    simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right] at h1 h2 h3 ⊢
    linarith
  ext w
  have h0 := hvw ((T - T') w) w
  have h1 : (T - T') w = 0 := inner_self_eq_zero.mp h0
  exact sub_eq_zero.mp h1
theorem exists_isSymmetric_inner_eq_bilinForm (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] (β : LinearMap.BilinForm ℝ X) :
    ∃ T : X →ₗ[ℝ] X, T.IsSymmetric ∧ ∀ v : X, inner ℝ v (T v) = β v v := by
  let b := stdOrthonormalBasis ℝ X
  let B : X → X →ₗ[ℝ] ℝ := fun u => (1 / 2 : ℝ) • (β u + LinearMap.flip β u)
  have hB : ∀ u w : X, B u w = (1 / 2 : ℝ) * (β u w + β w u) := fun u w => by
    simp [B]
    ring
  let T : X →ₗ[ℝ] X := ∑ i, (B (b i)).smulRight (b i)
  have hT : ∀ w : X, T w = ∑ i, B (b i) w • b i := fun w => by
    simp [T, LinearMap.sum_apply]
  have hvw : ∀ v w : X, inner ℝ v (T w) = (1 / 2 : ℝ) * (β v w + β w v) := fun v w => by
    have hv : v = ∑ i, inner ℝ (b i) v • b i := (b.sum_repr' v).symm
    have h1 : β v w = ∑ i, inner ℝ (b i) v * β (b i) w := by
      conv_lhs => rw [hv]
      simp [map_sum, LinearMap.sum_apply]
    have h2 : β w v = ∑ i, inner ℝ (b i) v * β w (b i) := by
      conv_lhs => rw [hv]
      simp [map_sum]
    rw [hT, inner_sum, h1, h2, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right, hB, real_inner_comm]
    ring
  refine ⟨T, fun x y => ?_, fun v => ?_⟩
  · rw [real_inner_comm, hvw, hvw]
    ring
  · rw [hvw]
    ring
theorem symmetricOperatorOfBilinForm_holds : SymmetricOperatorOfBilinForm := by
  refine ⟨fun X _ _ _ β => ?_, symmetric_eq_of_diagonal_eq⟩
  obtain ⟨T, hT, hd⟩ := exists_isSymmetric_inner_eq_bilinForm X β
  exact ⟨T, ⟨hT, hd⟩, fun T' h' =>
    symmetric_eq_of_diagonal_eq X T' T h'.1 hT fun v => by rw [h'.2 v, hd v]⟩
end YangMills.Construction.SymmetricOperator
