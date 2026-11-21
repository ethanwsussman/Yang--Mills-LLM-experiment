import YangMills.Construction.LinearAlgebra.ExponentialDecayOfInverseOfPositiveMatrix
import YangMills.Construction.Torus.BoundsOnTheInversesOfTheCubes
import YangMills.Construction.Torus.ColumnsOfTheGreenOperatorOnTheTori
import YangMills.Construction.Torus.GeometryOfCubesAndCutSequences
import YangMills.Construction.Torus.QuadraticFormsAndMatricesOfTheAverages
import YangMills.Construction.Torus.ScalarProductsTransposesAndProjectionsOfASettingProof
import Mathlib
set_option autoImplicit false
open Set Matrix
noncomputable section
namespace YangMills.Construction.GeneralTorus
namespace CubeInverse
theorem levelSpacing_pos (D : ScaleData) (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem finite_coarseBond (W : GaugeSetting) : Finite W.CoarseBond := by apply _root_.YangMills.Construction.GeneralTorus.InnerProductsAdjointsProjections.finite_coarseBond <;> assumption
theorem inv_apply_of_conj_diagonal {X : Type} [Fintype X] [DecidableEq X] (μ : X → ℝ)
    (hμ : ∀ x, μ x ≠ 0) (Z V S : Matrix X X ℝ)
    (hS : ∀ i j, S i j = (μ i)⁻¹ * (μ j)⁻¹ * Z i j) (hVZ : V * Z = 1) (i j : X) :
    S⁻¹ i j = μ i * V i j * μ j := by
  have h : (Matrix.of fun i j => μ i * V i j * μ j) * S = 1 := by
    ext i k
    have hik := congrFun (congrFun hVZ i) k
    rw [Matrix.mul_apply] at hik ⊢
    have hsum : ∑ j, (Matrix.of fun i j => μ i * V i j * μ j) i j * S j k =
        μ i * (μ k)⁻¹ * ∑ j, V i j * Z j k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hS, Matrix.of_apply]
      have h1 := hμ j
      have h2 := hμ k
      field_simp
    rw [hsum, hik]
    by_cases hc : i = k
    · subst hc
      simp [hμ i]
    · simp [Matrix.one_apply_ne hc]
  rw [Matrix.inv_eq_left_inv h, Matrix.of_apply]
theorem posSemidef_sub_smul_one {X : Type} [Fintype X] [DecidableEq X] (S : Matrix X X ℝ)
    (γ : ℝ) (hS : S.IsSymm)
    (h : ∀ v : X → ℝ, γ * ∑ c, v c ^ 2 ≤ ∑ c, ∑ c', v c * S c c' * v c') :
    (S - γ • (1 : Matrix X X ℝ)).PosSemidef := by
  refine .of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · change (S - γ • (1 : Matrix X X ℝ))ᴴ = _
    rw [conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul, transpose_one, hS.eq]
  · have h0 := h x
    have hform : star x ⬝ᵥ ((S - γ • (1 : Matrix X X ℝ)) *ᵥ x) =
        ∑ c, ∑ c', x c * S c c' * x c' - γ * ∑ c, x c ^ 2 := by
      simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
        star_trivial]
      congr 1
      · simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
      · simp only [dotProduct, smul_eq_mul, sq]
    rw [hform]
    linarith
section LocalBonds
variable {C : CubeGaugeSetting} {Q : C.data.CubeIndex}
end LocalBonds
end CubeInverse
end YangMills.Construction.GeneralTorus
end
