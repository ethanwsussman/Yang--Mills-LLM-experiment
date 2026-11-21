import YangMills.Construction.LinearAlgebra.BivectorsReflectionsAngles
import YangMills.Construction.LinearAlgebra.FreeCurvaturePropagatorIsSymmetricEvenAndContinuous
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import Mathlib
set_option autoImplicit false
open Matrix YangMills.Construction.TorusMetric YangMills.Construction.PeriodicLattice
noncomputable section
namespace YangMills.Construction.Exterior
namespace PropagatorSymmetry
theorem bivectorMatrixEntry_exteriorSq (hm : BivectorInnerMinorsReflectionDet)
    (A : Matrix (Fin 4) (Fin 4) ℝ) (P Q : AxisPlane) :
    bivectorMatrixEntry (exteriorSq A) P Q =
      A P.lower Q.lower * A P.upper Q.upper - A P.lower Q.upper * A P.upper Q.lower :=
  hm.2.2.1 A _ _ _ _ P.lower_lt_upper Q.lower_lt_upper
theorem isSelfAdjointMap_exteriorSq (hm : BivectorInnerMinorsReflectionDet)
    {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : Aᵀ = A) : IsSelfAdjointMap (exteriorSq A) := by
  have hA' : ∀ i j, A i j = A j i := fun i j => by
    conv_lhs => rw [← hA]
    rfl
  have hbasis : ∀ P Q : AxisPlane,
      inner ℝ (axisBivector P) (exteriorSq A (axisBivector Q)) =
        inner ℝ (exteriorSq A (axisBivector P)) (axisBivector Q) := by
    intro P Q
    rw [real_inner_comm (axisBivector Q)]
    have hPQ := bivectorMatrixEntry_exteriorSq hm A P Q
    have hQP := bivectorMatrixEntry_exteriorSq hm A Q P
    unfold bivectorMatrixEntry at hPQ hQP
    rw [hPQ, hQP, hA' Q.lower P.lower, hA' Q.upper P.upper, hA' Q.lower P.upper,
      hA' Q.upper P.lower]
    ring
  have hleft : ∀ (P : AxisPlane) (β : Bivector),
      inner ℝ (axisBivector P) (exteriorSq A β) =
        inner ℝ (exteriorSq A (axisBivector P)) β := by
    intro P β
    rw [← axisBivectorBasis.sum_repr β]
    simp only [map_sum, map_smul, inner_sum, inner_smul_right, axisBivectorBasis_apply, hbasis]
  intro α β
  rw [← axisBivectorBasis.sum_repr α]
  simp only [map_sum, map_smul, sum_inner, real_inner_smul_left, axisBivectorBasis_apply, hleft]
theorem householder_transpose (v : Fin 4 → ℝ) : (householder v)ᵀ = householder v := by
  ext i j
  simp only [householder, Matrix.transpose_apply, Matrix.sub_apply, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rfl
  · rw [if_neg hij, if_neg (Ne.symm hij), mul_comm (v j)]
theorem householder_neg (v : Fin 4 → ℝ) : householder (-v) = householder v := by
  ext i j
  simp [householder, vecMulVec_apply]
theorem euclidNormVec_neg (y : Fin 4 → ℝ) : euclidNormVec (-y) = euclidNormVec y := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem euclidNormVec_ne_zero {y : Fin 4 → ℝ} (hy : y ≠ 0) : euclidNormVec y ≠ 0 := by
  intro hzero
  apply hy
  have hsq : ∑ k, y k ^ 2 = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun k _ => sq_nonneg (y k))).1 hzero
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (y k)).1 hsq
  funext k
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (hall k (Finset.mem_univ k))
theorem continuousOn_householder_entry (i j : Fin 4) :
    ContinuousOn (fun y : Fin 4 → ℝ => householder ((euclidNormVec y)⁻¹ • y) i j) {y | y ≠ 0} := by
  have hrecip : ContinuousOn (fun y : Fin 4 → ℝ => (euclidNormVec y)⁻¹) {y | y ≠ 0} :=
    continuous_euclidNormVec.continuousOn.inv₀ fun y hy => euclidNormVec_ne_zero hy
  have hcomp : ∀ k : Fin 4, ContinuousOn (fun y : Fin 4 → ℝ => (euclidNormVec y)⁻¹ * y k)
      {y | y ≠ 0} := fun k => hrecip.mul (continuous_apply k).continuousOn
  simp only [householder, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply,
    smul_eq_mul]
  exact continuousOn_const.sub (continuousOn_const.mul ((hcomp i).mul (hcomp j)))
end PropagatorSymmetry
open PropagatorSymmetry in
theorem freeCurvaturePropagatorSymmEvenContinuous_holds
    (hm : BivectorInnerMinorsReflectionDet) :
    FreeCurvaturePropagatorSymmEvenContinuous := by
  refine ⟨fun y _ α β => ?_, fun y _ => ?_, fun P Q => ?_⟩
  · have hsa := isSelfAdjointMap_exteriorSq hm
      (householder_transpose ((euclidNormVec y)⁻¹ • y)) α β
    simp only [freeCurvaturePropagator, LinearMap.smul_apply, inner_smul_right,
      real_inner_smul_left, hsa]
  · simp only [freeCurvaturePropagator, euclidNormVec_neg, smul_neg, householder_neg]
  · have hentry : ∀ y : Fin 4 → ℝ, bivectorMatrixEntry (freeCurvaturePropagator y) P Q =
        1 / (Real.pi ^ 2 * euclidNormVec y ^ 4) *
          bivectorMatrixEntry (exteriorSq (householder ((euclidNormVec y)⁻¹ • y))) P Q := by
      intro y
      simp only [bivectorMatrixEntry, freeCurvaturePropagator, LinearMap.smul_apply,
        inner_smul_right]
    simp only [hentry, bivectorMatrixEntry_exteriorSq hm]
    have hscale : ContinuousOn (fun y : Fin 4 → ℝ => 1 / (Real.pi ^ 2 * euclidNormVec y ^ 4))
        {y | y ≠ 0} := by
      refine continuousOn_const.div
        (continuousOn_const.mul (continuous_euclidNormVec.continuousOn.pow 4)) fun y hy => ?_
      exact mul_ne_zero (pow_ne_zero 2 Real.pi_ne_zero) (pow_ne_zero 4 (euclidNormVec_ne_zero hy))
    exact hscale.mul
      (((continuousOn_householder_entry _ _).mul (continuousOn_householder_entry _ _)).sub
        ((continuousOn_householder_entry _ _).mul (continuousOn_householder_entry _ _)))
end YangMills.Construction.Exterior
end
