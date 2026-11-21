import YangMills.Construction.EuclideanFunctionals.TuplesIsometriesFreeSpaceAndMirrorOfFourSpace
import Mathlib
set_option autoImplicit false
open Matrix
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.EuclidMotion
def ofOrthogonalMatrix (Q : Matrix.orthogonalGroup (Fin 4) ℝ) : EuclidMotion where
  lin := Matrix.mulVecLin Q.1
  offset := 0
  lin_norm y := by
    have hQQ : Q.1ᵀ * Q.1 = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using
        (Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ).1 Q.2
    have hdot : (Q.1.mulVec y) ⬝ᵥ (Q.1.mulVec y) = y ⬝ᵥ y := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQQ,
        Matrix.one_mulVec]
    have hsum : ∑ μ, (Q.1.mulVec y) μ ^ 2 = ∑ μ, y μ ^ 2 := by
      simpa [dotProduct, sq] using hdot
    simp only [TorusMetric.euclidNormVec, Matrix.mulVecLin_apply, hsum]
theorem ofOrthogonalMatrix_apply (Q : Matrix.orthogonalGroup (Fin 4) ℝ) (y : R4) :
    ofOrthogonalMatrix Q y = Q.1.mulVec y := by
  simp [ofOrthogonalMatrix]
end YangMills.Construction.EuclideanFunctionals.EuclidMotion
end
