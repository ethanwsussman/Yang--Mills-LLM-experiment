import YangMills.Construction.RunningCouplingSlope.GaussianNumberInCoordinates
import YangMills.Construction.RunningCouplingSlope.GaussianNumberThroughLevels
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.LinearConstraint
namespace LevelwiseDeterminant
section Matrices
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
private theorem det_one_sub_of_blockTriangular {α : Type} [LinearOrder α] (b : Ω → α) (N : Matrix Ω Ω ℝ)
    (hb : (1 - N).BlockTriangular b) (hd : ∀ e e', b e = b e' → N e e' = 0) : (1 - N).det = 1 := by
  rw [hb.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have e : (1 - N).toSquareBlock b a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    have h₁ : N i j = 0 := hd i j (hi.trans hj.symm)
    by_cases hij : i = j
    · subst hij
      simp [Matrix.toSquareBlock, Matrix.toSquareBlockProp, h₁]
    · have : (⟨i, hi⟩ : {x // b x = a}) ≠ ⟨j, hj⟩ := fun h => hij (congrArg Subtype.val h)
      simp [Matrix.toSquareBlock, Matrix.toSquareBlockProp, h₁, Matrix.one_apply_ne hij,
        Matrix.one_apply_ne this]
  rw [e, Matrix.det_one]
private theorem det_one_sub_strictLower (lev : Ω → ℕ) (N : Matrix Ω Ω ℝ)
    (h : ∀ e e', lev e ≤ lev e' → N e e' = 0) : (1 - N).det = 1 := by
  refine det_one_sub_of_blockTriangular (fun e => OrderDual.toDual (lev e)) N (fun i j hij => ?_) fun e e' he => ?_
  · have hlt : lev i < lev j := hij
    have hne : i ≠ j := fun hh => by subst hh; exact lt_irrefl _ hlt
    simp [Matrix.one_apply_ne hne, h i j hlt.le]
  · exact h e e' (le_of_eq (OrderDual.toDual.injective he))
private theorem det_one_sub_strictUpper (lev : Ω → ℕ) (N : Matrix Ω Ω ℝ)
    (h : ∀ e e', lev e' ≤ lev e → N e e' = 0) : (1 - N).det = 1 := by
  refine det_one_sub_of_blockTriangular lev N (fun i j hij => ?_) fun e e' he => ?_
  · have hlt : lev j < lev i := hij
    have hne : i ≠ j := fun hh => by subst hh; exact lt_irrefl _ hlt
    simp [Matrix.one_apply_ne hne, h i j hlt.le]
  · exact h e e' (le_of_eq he.symm)
private theorem linearMap_det_toEuclideanLin (D : Matrix Ω Ω ℝ) :
    LinearMap.det (Matrix.toEuclideanLin D) = D.det := by
  rw [Matrix.toEuclideanLin_eq_toLin, LinearMap.det_toLin]
private theorem absDetOfMap_toEuclideanLin (D : Matrix Ω Ω ℝ) :
    absDetOfMap (Matrix.toEuclideanLin D) = |D.det| := by
  have e : LinearMap.adjoint (Matrix.toEuclideanLin D) ∘ₗ Matrix.toEuclideanLin D =
      Matrix.toEuclideanLin (D.conjTranspose * D) := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    refine LinearMap.ext fun x => ?_
    ext e
    simp [Matrix.ofLp_toEuclideanLin_apply, Matrix.mulVec_mulVec]
  rw [absDetOfMap, e, linearMap_det_toEuclideanLin, Matrix.det_mul, Matrix.det_conjTranspose]
  simp only [star_trivial]
  rw [← sq, Real.sqrt_sq_eq_abs]
end Matrices
end LevelwiseDeterminant
open LevelwiseDeterminant in
theorem gaussianNumberByLevels_of_coordinateFormula (hc : GaussianNumberCoordinateFormula) :
    GaussianNumberByLevels := by
  intro E C _ _ _ _ _ _ Ω _ _ lev p q s j M T N N' A G hin hps hqs hpj hqj hMj hN hN' hA hG hT
  have d₁ := det_one_sub_strictLower lev N hN
  have d₂ := det_one_sub_strictUpper lev N' hN'
  have u₂ : IsUnit (1 - N').det := by rw [d₂]; exact isUnit_one
  set R : Matrix Ω Ω ℝ := (1 - N')⁻¹ * A with hR
  set D : Matrix Ω Ω ℝ := (1 - N) * R with hD
  have hRdet : (1 - N') * R = A := by
    rw [hR, ← mul_assoc, Matrix.mul_nonsing_inv _ u₂, one_mul]
  have hDdet : D.det = A.det := by
    have h₁ : (1 - N').det * R.det = A.det := by rw [← Matrix.det_mul, hRdet]
    rw [hD, Matrix.det_mul, d₁, one_mul, ← h₁, d₂, one_mul]
  have hker : ∀ x, (s x - j (M (s x))) ∈ LinearMap.ker M := fun x => by
    have h₁ : M (j (M (s x))) = M (s x) := LinearMap.congr_fun hMj (M (s x))
    rw [LinearMap.mem_ker, map_sub, h₁, sub_self]
  have hpR : ∀ x, p (s x - j (M (s x))) = x := fun x => by
    have h₁ : p (s x) = x := LinearMap.congr_fun hps x
    have h₂ : p (j (M (s x))) = 0 := LinearMap.congr_fun hpj (M (s x))
    rw [map_sub, h₁, h₂, sub_zero]
  let S : EuclideanSpace ℝ Ω →ₗ[ℝ] E := s - j ∘ₗ M ∘ₗ s
  let Ψ : EuclideanSpace ℝ Ω →ₗ[ℝ] LinearMap.ker M :=
    LinearMap.codRestrict (LinearMap.ker M) (S ∘ₗ Matrix.toEuclideanLin D) fun u => hker _
  have hΨ : p ∘ₗ (LinearMap.ker M).subtype ∘ₗ Ψ = Matrix.toEuclideanLin D :=
    LinearMap.ext fun u => hpR _
  have hne : LinearMap.det (Matrix.toEuclideanLin D) ≠ 0 := by
    rw [linearMap_det_toEuclideanLin, hDdet]
    exact hA
  have hbij : Function.Bijective (p ∘ₗ (LinearMap.ker M).subtype ∘ₗ Ψ) := by
    rw [hΨ]
    exact (LinearMap.equivOfDetNeZero _ hne).bijective
  have hval : ∀ u, T (Ψ u) = dotProduct (WithLp.ofLp u) (Matrix.mulVec G (WithLp.ofLp u)) := by
    intro u
    refine hT (Ψ u) (Matrix.mulVec R (WithLp.ofLp u)) (WithLp.ofLp u) ?_ ?_
    · have h₁ : p ((Ψ u : LinearMap.ker M) : E) = Matrix.toEuclideanLin D u :=
        LinearMap.congr_fun hΨ u
      have e : Matrix.mulVec D (WithLp.ofLp u) =
          Matrix.mulVec (1 - N) (Matrix.mulVec R (WithLp.ofLp u)) := by
        rw [Matrix.mulVec_mulVec]
      rw [h₁, Matrix.ofLp_toEuclideanLin_apply, e, Matrix.sub_mulVec, Matrix.one_mulVec]
    · have e : Matrix.mulVec (1 - N') (Matrix.mulVec R (WithLp.ofLp u)) =
          Matrix.mulVec A (WithLp.ofLp u) := by
        rw [Matrix.mulVec_mulVec, hRdet]
      rw [← e, Matrix.sub_mulVec, Matrix.one_mulVec]
  have key := hc E (EuclideanSpace ℝ Ω) C Ω p q s j M T Ψ G hin hps hqs hpj hqj hMj hG hbij hval
  rw [key, hΨ, absDetOfMap_toEuclideanLin, hDdet]
end YangMills.Construction.LinearConstraint
end
