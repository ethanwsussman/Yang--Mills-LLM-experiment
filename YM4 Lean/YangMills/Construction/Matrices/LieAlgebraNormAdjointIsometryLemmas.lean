import YangMills.Construction.Lattice.MatricesBlocksAndGaugeTransformationsProof
import YangMills.Construction.Matrices.LieAlgebraNormAdjointIsometry
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices.ComplexMatrix2.LieNormAdjoint
private theorem unitary_of_mem_specialUnitary {u : ComplexMatrix2} (hu : u ∈ specialUnitary) :
    u ∈ unitary ComplexMatrix2 :=
  Matrix.specialUnitaryGroup_le_unitaryGroup hu
private theorem conjugateBy_eq {u : ComplexMatrix2} (hu : u ∈ specialUnitary) (Y : ComplexMatrix2) :
    conjugateBy u Y = u * Y * star u := by
  rw [conjugateBy, Matrix.inv_eq_right_inv
    (Matrix.mem_unitaryGroup_iff.mp (unitary_of_mem_specialUnitary hu))]
private theorem norm_unitary_conj {u : ComplexMatrix2} (hu : u ∈ unitary ComplexMatrix2)
    (Y : ComplexMatrix2) : ‖u * Y * star u‖ = ‖Y‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hu), CStarRing.norm_mem_unitary_mul _ hu]
private theorem conj_mem_hermitianTraceless {v X : ComplexMatrix2} (hv : star v * v = 1)
    (hX : X ∈ hermitianTraceless) : v * X * star v ∈ hermitianTraceless := by apply _root_.YangMills.Construction.PeriodicLattice.ElementaryStepFacts.mul_mul_star_mem_hermitianTraceless <;> assumption
private def lieElementOfMatrix (A : ComplexMatrix2) (h : A ∈ hermitianTraceless) : LieElement :=
  (⟨A, h⟩ : hermitianTraceless)
private theorem lieElement_ext {X Y : LieElement} (h : X.toMatrix = Y.toMatrix) : X = Y :=
  Subtype.ext h
private theorem mul_self_eq_halfTrace_smul {X : ComplexMatrix2} (h : fullTrace X = 0) :
    X * X = halfTrace (X * X) • (1 : ComplexMatrix2) := by
  have h₁ : X 1 1 = -X 0 0 := by
    have : X 0 0 + X 1 1 = 0 := by simpa [fullTrace, Matrix.trace, Fin.sum_univ_two] using h
    linear_combination this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfTrace, fullTrace, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, h₁] <;> ring
abbrev _root_.YangMills.SharedProofs.p123376 := @mul_self_eq_halfTrace_smul
private theorem halfTrace_mul_eq_re (X Y : LieElement) :
    halfTrace (X.toMatrix * Y.toMatrix) =
      (((halfTrace (X.toMatrix * Y.toMatrix)).re : ℝ) : ℂ) := by
  have h := LieElement.star_fullTrace_mul X Y
  have h₁ : (fullTrace (X.toMatrix * Y.toMatrix)).im = 0 := Complex.conj_eq_iff_im.mp h
  apply Complex.ext <;> simp [halfTrace, h₁]
private theorem inner_eq_halfTrace (X Y : LieElement) :
    inner ℝ X Y = (halfTrace (X.toMatrix * Y.toMatrix)).re := rfl
private theorem halfTrace_mul_self (X : LieElement) :
    halfTrace (X.toMatrix * X.toMatrix) = ((operatorNorm X.toMatrix ^ 2 : ℝ) : ℂ) := by
  have hnn : 0 ≤ (halfTrace (X.toMatrix * X.toMatrix)).re := by
    have := real_inner_self_nonneg (x := X)
    rwa [inner_eq_halfTrace] at this
  have hs : X.toMatrix * X.toMatrix = halfTrace (X.toMatrix * X.toMatrix) • (1 : ComplexMatrix2) :=
    mul_self_eq_halfTrace_smul X.2.2
  have hst : star X.toMatrix = X.toMatrix := X.2.1.symm
  have hn : ‖X.toMatrix‖ ^ 2 = (halfTrace (X.toMatrix * X.toMatrix)).re := by
    calc ‖X.toMatrix‖ ^ 2 = ‖X.toMatrix‖ * ‖X.toMatrix‖ := sq _
      _ = ‖star X.toMatrix * X.toMatrix‖ := CStarRing.norm_star_mul_self.symm
      _ = ‖X.toMatrix * X.toMatrix‖ := by rw [hst]
      _ = ‖halfTrace (X.toMatrix * X.toMatrix)‖ := by
        conv_lhs => rw [hs]
        rw [norm_smul, CStarRing.norm_one, mul_one]
      _ = (halfTrace (X.toMatrix * X.toMatrix)).re := by
        rw [halfTrace_mul_eq_re X X, Complex.norm_real, Complex.ofReal_re,
          Real.norm_of_nonneg hnn]
  rw [operatorNorm, hn]
  exact halfTrace_mul_eq_re X X
private theorem norm_eq_operatorNorm (X : LieElement) : ‖X‖ = operatorNorm X.toMatrix := by
  have h : ‖X‖ ^ 2 = operatorNorm X.toMatrix ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_halfTrace, halfTrace_mul_self, Complex.ofReal_re]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
private noncomputable def signedConjugateLinear {u : ComplexMatrix2} (hu : u ∈ specialUnitary)
    (s : ℝ) : LieElement →ₗ[ℝ] LieElement where
  toFun X := lieElementOfMatrix (s • conjugateBy u X.toMatrix) (hermitianTraceless.smul_mem s (by
    rw [conjugateBy_eq hu]
    exact conj_mem_hermitianTraceless
      (Matrix.mem_unitaryGroup_iff'.mp (unitary_of_mem_specialUnitary hu)) X.2))
  map_add' X Y := by
    apply lieElement_ext
    change s • conjugateBy u (X.toMatrix + Y.toMatrix) =
      s • conjugateBy u X.toMatrix + s • conjugateBy u Y.toMatrix
    rw [← smul_add]
    simp only [conjugateBy, mul_add, add_mul]
  map_smul' c X := by
    apply lieElement_ext
    change s • conjugateBy u (c • X.toMatrix) = c • s • conjugateBy u X.toMatrix
    rw [smul_comm]
    simp only [conjugateBy, Matrix.mul_smul, Matrix.smul_mul]
theorem lieAlgebraNormAdjointIsometry_holds : LieAlgebraNormAdjointIsometry := by
  have : CompleteSpace LieElement := FiniteDimensional.complete ℝ LieElement
  have hnorm : ∀ u ∈ specialUnitary, ∀ Y : ComplexMatrix2,
      operatorNorm (conjugateBy u Y) = operatorNorm Y := fun u hu Y => by
    rw [conjugateBy_eq hu]
    exact norm_unitary_conj (unitary_of_mem_specialUnitary hu) Y
  refine ⟨halfTrace_mul_self, fun X Y => ?_, norm_eq_operatorNorm, fun X Y => ?_, fun T => ?_,
    hnorm, fun u hu => ?_, fun u hu X _ Y _ => ?_, fun u hu s hs => ?_, fun u hu u' hu' Y => ?_⟩
  · rw [inner_eq_halfTrace]
    exact halfTrace_mul_eq_re X Y
  · rw [← norm_eq_operatorNorm, ← norm_eq_operatorNorm]
    exact abs_real_inner_le_norm X Y
  · rw [LinearMap.adjoint_toContinuousLinearMap]
    exact LinearIsometryEquiv.norm_map _ _
  · have h₁ : star u * u = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp (unitary_of_mem_specialUnitary hu)
    have h₂ : u * star u = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (unitary_of_mem_specialUnitary hu)
    ext X
    constructor
    · rintro ⟨Y, hY, rfl⟩
      rw [conjugateBy_eq hu]
      exact conj_mem_hermitianTraceless h₁ hY
    · intro hX
      refine ⟨star u * X * u, ?_, ?_⟩
      · have := conj_mem_hermitianTraceless (v := star u) (by rw [star_star, h₂]) hX
        rwa [star_star] at this
      · rw [conjugateBy_eq hu]
        calc u * (star u * X * u) * star u = (u * star u) * X * (u * star u) := by
              simp only [mul_assoc]
          _ = X := by rw [h₂, one_mul, mul_one]
  · have h₁ : star u * u = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp (unitary_of_mem_specialUnitary hu)
    rw [conjugateBy_eq hu, conjugateBy_eq hu]
    have h₂ : u * X * star u * (u * Y * star u) = u * (X * Y) * star u := by
      calc u * X * star u * (u * Y * star u) = u * X * (star u * u) * Y * star u := by
            simp only [mul_assoc]
        _ = u * (X * Y) * star u := by rw [h₁, mul_one, mul_assoc u X Y]
    simp only [halfTrace, fullTrace]
    rw [h₂, Matrix.trace_mul_comm, ← mul_assoc, ← mul_assoc, h₁, one_mul]
  · refine ⟨LinearIsometry.toLinearIsometryEquiv
      { toLinearMap := signedConjugateLinear hu s, norm_map' := fun X => ?_ } rfl, fun X => rfl⟩
    rw [norm_eq_operatorNorm, norm_eq_operatorNorm]
    change operatorNorm (s • conjugateBy u X.toMatrix) = operatorNorm X.toMatrix
    rcases hs with rfl | rfl
    · rw [one_smul]
      exact hnorm u hu _
    · rw [neg_smul, one_smul, operatorNorm, norm_neg]
      exact hnorm u hu _
  · have hu₁ := unitary_of_mem_specialUnitary hu
    have hu₂ := unitary_of_mem_specialUnitary hu'
    have h : conjugateBy u Y - conjugateBy u' Y =
        (u - u') * Y * star u + u' * (Y * star (u - u')) := by
      rw [conjugateBy_eq hu, conjugateBy_eq hu', star_sub]
      noncomm_ring
    rw [h]
    calc ‖(u - u') * Y * star u + u' * (Y * star (u - u'))‖
        ≤ ‖(u - u') * Y * star u‖ + ‖u' * (Y * star (u - u'))‖ := norm_add_le _ _
      _ = ‖(u - u') * Y‖ + ‖Y * star (u - u')‖ := by
        rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hu₁),
          CStarRing.norm_mem_unitary_mul _ hu₂]
      _ ≤ ‖u - u'‖ * ‖Y‖ + ‖Y‖ * ‖star (u - u')‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = 2 * operatorNorm (u - u') * operatorNorm Y := by
        rw [norm_star]
        simp only [operatorNorm]
        ring
end YangMills.Construction.Matrices.ComplexMatrix2.LieNormAdjoint
