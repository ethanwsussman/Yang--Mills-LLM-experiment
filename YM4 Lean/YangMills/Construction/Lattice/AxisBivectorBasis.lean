import YangMills.Construction.Geometry.MinimalLift
import YangMills.Construction.Lattice.CurvatureKernelGradient
import YangMills.Construction.LinearAlgebra.BivectorsReflectionsAngles
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusMetric Exterior
namespace PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def axisBivector (P : AxisPlane) : Bivector :=
  wedgeProd (Pi.single P.lower 1) (Pi.single P.upper 1)
theorem axisBivector_apply (P : AxisPlane) {a b : Fin 4} (h : a < b) :
    (axisBivector P).1 a b = if a = P.lower ∧ b = P.upper then 1 else 0 := by
  have hP := P.lower_lt_upper
  have hval : (axisBivector P).1 =
      Matrix.vecMulVec (Pi.single P.lower (1 : ℝ)) (Pi.single P.upper 1) -
        Matrix.vecMulVec (Pi.single P.upper (1 : ℝ)) (Pi.single P.lower 1) := rfl
  rw [hval, Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.vecMulVec_apply]
  simp only [Pi.single_apply]
  have h2 : ¬(a = P.upper ∧ b = P.lower) := by
    rintro ⟨rfl, rfl⟩
    exact absurd h (not_lt.2 hP.le)
  by_cases h1 : a = P.lower ∧ b = P.upper
  · obtain ⟨rfl, rfl⟩ := h1
    simp [hP.ne, hP.ne']
  · have t₁ : (if a = P.lower then (1 : ℝ) else 0) * (if b = P.upper then 1 else 0) = 0 := by
      by_cases ha : a = P.lower
      · have hb : b ≠ P.upper := fun hb => h1 ⟨ha, hb⟩
        simp [hb]
      · simp [ha]
    have t₂ : (if a = P.upper then (1 : ℝ) else 0) * (if b = P.lower then 1 else 0) = 0 := by
      by_cases ha : a = P.upper
      · have hb : b ≠ P.lower := fun hb => h2 ⟨ha, hb⟩
        simp [hb]
      · simp [ha]
    rw [t₁, t₂, if_neg h1, sub_zero]
theorem inner_axisBivector (P : AxisPlane) (ω : Bivector) :
    inner ℝ (axisBivector P) ω = ω.1 P.lower P.upper := by
  rw [inner_eq_bivInner, bivInner,
    Finset.sum_eq_single (P.lower, P.upper)]
  · rw [axisBivector_apply P P.lower_lt_upper]
    simp
  · rintro ⟨a, b⟩ hab hne
    have hlt : a < b := by simpa [ascPairs] using hab
    have hnot : ¬(a = P.lower ∧ b = P.upper) := fun h => hne (Prod.ext h.1 h.2)
    simp only
    rw [axisBivector_apply P hlt, if_neg hnot, zero_mul]
  · intro h
    exact absurd (by simpa [ascPairs] using P.lower_lt_upper) h
theorem orthonormal_axisBivector : Orthonormal ℝ axisBivector := by
  classical
  rw [orthonormal_iff_ite]
  intro P Q
  rw [inner_axisBivector, axisBivector_apply Q P.lower_lt_upper]
  by_cases h : P = Q
  · simp [h]
  · have hnot : ¬(P.lower = Q.lower ∧ P.upper = Q.upper) :=
      fun e => h (AxisPlane.ext e.1 e.2)
    rw [if_neg hnot, if_neg h]
theorem top_le_span_axisBivector : ⊤ ≤ Submodule.span ℝ (Set.range axisBivector) := by
  have hbot : (Submodule.span ℝ (Set.range axisBivector))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro ω hω
    have h0 : ∀ P : AxisPlane, ω.1 P.lower P.upper = 0 := fun P => by
      rw [← inner_axisBivector P ω]
      exact (Submodule.mem_orthogonal _ _).1 hω _ (Submodule.subset_span ⟨P, rfl⟩)
    have hlt : ∀ a b : Fin 4, a < b → ω.1 a b = 0 := fun a b h => h0 ⟨a, b, h⟩
    apply Bivector.ext
    ext a b
    rcases lt_trichotomy a b with h | h | h
    · simpa using hlt a b h
    · subst h
      have := Bivector.apply_swap ω a a
      simp only [Bivector.zero_val, Matrix.zero_apply]
      linarith
    · have := Bivector.apply_swap ω b a
      simp only [Bivector.zero_val, Matrix.zero_apply]
      rw [this, hlt b a h, neg_zero]
  exact (Submodule.orthogonal_eq_bot_iff.1 hbot).ge
def axisBivectorBasis : OrthonormalBasis AxisPlane ℝ Bivector :=
  OrthonormalBasis.mk orthonormal_axisBivector top_le_span_axisBivector
@[simp] theorem axisBivectorBasis_apply (P : AxisPlane) : axisBivectorBasis P = axisBivector P := by
  simp [axisBivectorBasis]
def bivectorMatrixEntry (T : Bivector →ₗ[ℝ] Bivector) (P Q : AxisPlane) : ℝ :=
  inner ℝ (axisBivector P) (T (axisBivector Q))
open Classical in
theorem bivectorMatrixEntry_eq_toMatrix (T : Bivector →ₗ[ℝ] Bivector) (P Q : AxisPlane) :
    bivectorMatrixEntry T P Q =
      LinearMap.toMatrix axisBivectorBasis.toBasis axisBivectorBasis.toBasis T P Q := by
  rw [LinearMap.toMatrix_apply]
  simp [bivectorMatrixEntry, OrthonormalBasis.repr_apply_apply]
def bivectorTrace (T : Bivector →ₗ[ℝ] Bivector) : ℝ := ∑ P, bivectorMatrixEntry T P P
theorem bivectorTrace_eq_trace (T : Bivector →ₗ[ℝ] Bivector) :
    bivectorTrace T = LinearMap.trace ℝ Bivector T := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ axisBivectorBasis.toBasis T, Matrix.trace]
  exact Finset.sum_congr rfl fun P _ => bivectorMatrixEntry_eq_toMatrix T P P
def barycenterDist (p q : Plaquette L m j) : ℝ :=
  torusEuclidNorm (p.barycenter - q.barycenter)
def barycenterDisplacement (p q : Plaquette L m j) : Fin 4 → ℝ :=
  minimalLift (p.barycenter - q.barycenter)
end PeriodicLattice
end YangMills.Construction
end
