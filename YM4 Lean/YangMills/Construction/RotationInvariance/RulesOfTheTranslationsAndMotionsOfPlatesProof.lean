import YangMills.Construction.RotationInvariance.MotionsOfPlatesAndQuarterRotations
import YangMills.Construction.RotationInvariance.RulesOfTheTranslationsAndMotionsOfPlates
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TranslationRules
open RealPlane
theorem embedFour_smul_unitX (s : ℝ) :
    embedFour (s • unitX) = s • timeVec := by
  funext k
  fin_cases k <;>
    simp [embedFour, unitX, PeriodicLattice.coordVec]
theorem translationLaws_hold : TranslationLaws := by
  refine ⟨fun w f g F G => rfl, fun w c f F => ⟨rfl, rfl⟩, fun w w' f F => ?_, fun s => ?_⟩
  · funext y
    exact congrArg F (funext fun j => sub_sub _ _ _)
  · rw [planeShift, embedFour_smul_unitX]
    exact ⟨rfl, fun f F => rfl⟩
def timeFlipMatrix : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, 1, 1, -1]
theorem timeFlipMatrix_mem_orthogonalGroup : timeFlipMatrix ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff, timeFlipMatrix, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext k
  fin_cases k <;> simp
theorem liftFour_reflectFirst_eq_mulVec (y : R4) :
    liftFour reflectFirst y = timeFlipMatrix.mulVec y := by
  funext k
  fin_cases k <;>
    simp [liftFour, ofComponents, reflectFirst, planeComponent, orthogonalComponent, timeFlipMatrix,
      Matrix.mulVec_diagonal]
theorem planeMotionsAffineIsometric_holds
    (hRot : ProductMotions.RotationsSpecialOrthogonal) :
    PlaneMotionsAffineIsometric := by
  have hMat : ∀ s : ℝ, ∃ Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ,
      ∀ y, liftFour (rotate s) y = (Q : Matrix _ _ ℝ).mulVec y := fun s =>
    ⟨LinearMap.toMatrix' (rotateLin s),
      (Matrix.mem_specialOrthogonalGroup_iff.1 (hRot s).2.2.2.1).1, fun y => by
        rw [LinearMap.toMatrix'_mulVec]
        rfl⟩
  refine ⟨fun s => ?_, ⟨timeFlipMatrix, timeFlipMatrix_mem_orthogonalGroup, 0, fun y => ?_⟩,
    fun v => ⟨1, one_mem _, embedFour v, fun y => ?_⟩, hMat, liftFour_reflectFirst,
    fun v y => ?_⟩
  · obtain ⟨Q, hQ, hQy⟩ := hMat s
    exact ⟨Q, hQ, 0, fun y => by rw [hQy, add_zero]⟩
  · rw [liftFour_reflectFirst_eq_mulVec, add_zero]
  · rw [liftFour_add, Matrix.one_mulVec]
  · rw [liftFour_add]
    rfl
theorem translationAndMotionFacts_holds (hMot : ProductMotions.MotionFacts) :
    TranslationAndMotionFacts := by
  obtain ⟨hRot, -, hProd, hAct, hImg⟩ := hMot
  refine ⟨translationLaws_hold, fun β hβ ψ hψ v s => ?_, hProd,
    planeMotionsAffineIsometric_holds hRot⟩
  obtain ⟨a₁, a₂, a₃⟩ := hAct β hβ ψ hψ v s
  obtain ⟨b₁, b₂, b₃, -⟩ := hImg β hβ ψ hψ v s
  exact ⟨a₁, a₂, a₃, b₁, b₂, b₃⟩
end YangMills.Construction.EuclideanFunctionals.TranslationRules
end
