import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfAMovedExponential
import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace Interpolation
open BlockAverages ColdStepAtMirrorFrames
def logDerivAlongRightTranslationStatement : Prop :=
  ∀ (Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions)
    (U : Set (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)), IsOpen U →
    (∀ r, diagonalTriple r ∈ U) →
    ContDiffOn ℝ 3 Θ U → (∀ z ∈ U, expUnit (Θ z) = expUnit z.1 * expUnit z.2.1 * (expUnit z.2.2)⁻¹) →
    (∀ r, Θ (diagonalTriple r) = 0) → ∀ w X : imaginaryQuaternions,
      ((fderiv ℝ Θ (diagonalTriple w) (0, X, 0) : imaginaryQuaternions) : ℍ[ℝ]) =
        NormedSpace.exp (w : ℍ[ℝ]) * (X : ℍ[ℝ]) * (((expUnit w)⁻¹ : UnitQuaternion) : ℍ[ℝ]) ∧
      ∀ u : imaginaryQuaternions, IsRightTranslationDeriv w X u →
        ((fderiv ℝ Θ (diagonalTriple w) (u, 0, 0) : imaginaryQuaternions) : ℍ[ℝ]) =
          NormedSpace.exp (w : ℍ[ℝ]) * (X : ℍ[ℝ]) * (((expUnit w)⁻¹ : UnitQuaternion) : ℍ[ℝ])
end Interpolation
end YangMills.Construction
end
